import os
import base64
import tempfile
import re
import json
import time
import uuid
import secrets
import glob
import signal
import socket
import ipaddress
import threading
import subprocess
import urllib.request
import urllib.parse
import urllib.error
import requests
from playwright.sync_api import sync_playwright, TimeoutError as PlaywrightTimeoutError
from pathlib import Path
from urllib.parse import urlparse, unquote

from flask import Flask, request, jsonify, render_template, send_file, redirect, url_for, session, flash
from werkzeug.middleware.proxy_fix import ProxyFix

APP_DIR = Path(__file__).resolve().parent
DATA_DIR = Path(os.getenv("DATA_DIR", str(APP_DIR / "data"))).resolve()
DOWNLOAD_ROOT = Path(os.getenv("DOWNLOAD_DIR", str(APP_DIR / "downloads"))).resolve()
DATA_DIR.mkdir(parents=True, exist_ok=True)
DOWNLOAD_ROOT.mkdir(parents=True, exist_ok=True)

JOBS_FILE = DATA_DIR / "jobs.json"
SETTINGS_FILE = DATA_DIR / "settings.json"
APP_PASSWORD = os.getenv("APP_PASSWORD", "").strip()
SECRET_KEY = os.getenv("SECRET_KEY", "").strip() or uuid.uuid4().hex + uuid.uuid4().hex

app = Flask(__name__)
app.secret_key = SECRET_KEY
app.wsgi_app = ProxyFix(app.wsgi_app, x_for=1, x_proto=1, x_host=1)
app.config.update(
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE="Lax",
    SESSION_COOKIE_SECURE=os.getenv("COOKIE_SECURE", "0") == "1",
    MAX_CONTENT_LENGTH=32 * 1024,
)

LOCK = threading.RLock()
PROCESS_LOCK = threading.RLock()
PROCESSES = {}
RUNNING_IDS = set()
MAX_WORKERS = 8
MAX_JOBS = 100
ANILIST_CACHE_TTL = 300
ANILIST_STALE_TTL = 21600
ANILIST_CACHE = {}
ANILIST_CACHE_LOCK = threading.RLock()
DEFAULT_SETTINGS = {"max_concurrent": 3, "folder_name": "Videos", "videodownloader_token": ""}
jobs = {}
settings = dict(DEFAULT_SETTINGS)


def atomic_json_write(path, value):
    tmp = path.with_suffix(path.suffix + ".tmp")
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(value, f, ensure_ascii=False, indent=2)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)


def load_state():
    global jobs, settings
    if JOBS_FILE.exists():
        try:
            jobs = json.loads(JOBS_FILE.read_text(encoding="utf-8"))
        except Exception:
            jobs = {}
    if SETTINGS_FILE.exists():
        try:
            loaded = json.loads(SETTINGS_FILE.read_text(encoding="utf-8"))
            settings.update(loaded if isinstance(loaded, dict) else {})
        except Exception:
            pass
    # Recover active jobs after a worker restart. yt-dlp uses --continue for
    # partial downloads; FFmpeg safely starts the compression stage again.
    changed = False
    for job in jobs.values():
        if job.get("status") in ("starting", "downloading", "processing"):
            job["status"] = "queued"
            job["progress"] = 0
            job["stage_progress"] = 0
            job["speed"] = ""
            job["eta"] = ""
            job["error"] = "Recovered after a service restart; job queued to resume."
            job["updated"] = time.time()
            changed = True
    if changed:
        atomic_json_write(JOBS_FILE, jobs)
    settings["max_concurrent"] = max(1, min(4, int(settings.get("max_concurrent", 3))))
    settings["folder_name"] = clean_folder_name(settings.get("folder_name", "Videos"))
    save_settings()


def save_jobs_locked():
    atomic_json_write(JOBS_FILE, jobs)


def save_settings():
    with LOCK:
        atomic_json_write(SETTINGS_FILE, settings)


def clean_folder_name(value):
    value = str(value or "Videos").strip()
    value = re.sub(r"[^A-Za-z0-9 _-]", "", value)[:48].strip(" ._-")
    if not value or value in (".", ".."):
        return "Videos"
    return value


def output_dir_for(folder_name=None):
    name = clean_folder_name(folder_name or settings.get("folder_name", "Videos"))
    path = (DOWNLOAD_ROOT / name).resolve()
    if path.parent != DOWNLOAD_ROOT:
        raise ValueError("Invalid output directory")
    path.mkdir(parents=True, exist_ok=True)
    return path


def public_job(job):
    copy = dict(job)
    copy.pop("url", None)
    copy.pop("source_file", None)
    copy.pop("cancel_requested", None)
    copy.pop("paused_from", None)
    copy.pop("animepahe_meta", None)
    return copy


def valid_public_http_url(raw_url):
    try:
        parsed = urlparse(raw_url)
        if parsed.scheme not in ("http", "https") or not parsed.hostname:
            return False, "Use a full http:// or https:// video URL."
        if parsed.username or parsed.password:
            return False, "URLs containing embedded credentials are not accepted."
        host = parsed.hostname.rstrip(".").lower()
        if host in ("localhost", "localhost.localdomain"):
            return False, "Local and private network addresses are not allowed."
        try:
            ip = ipaddress.ip_address(host)
            if not ip.is_global:
                return False, "Private or local IP addresses are not allowed."
        except ValueError:
            try:
                addresses = socket.getaddrinfo(host, parsed.port or (443 if parsed.scheme == "https" else 80), type=socket.SOCK_STREAM)
            except socket.gaierror:
                return False, "The URL host could not be resolved."
            if not addresses:
                return False, "The URL host could not be resolved."
            for item in addresses:
                try:
                    if not ipaddress.ip_address(item[4][0].split("%")[0]).is_global:
                        return False, "The URL resolves to a private or local network address."
                except ValueError:
                    return False, "The URL host could not be validated."
        return True, ""
    except Exception:
        return False, "That URL is not valid."


def safe_label(raw_url):
    try:
        p = urlparse(raw_url)
        tail = unquote(p.path.rstrip("/").split("/")[-1])
        tail = re.sub(r"[_-]+", " ", tail)
        if tail and len(tail) > 2:
            return tail[:72]
        return p.hostname or "Video download"
    except Exception:
        return "Video download"


def update_job(job_id, **changes):
    with LOCK:
        if job_id not in jobs:
            return
        jobs[job_id].update(changes)
        jobs[job_id]["updated"] = time.time()
        save_jobs_locked()


def parse_size(text):
    if not text:
        return None
    text = text.strip().replace(",", "")
    match = re.match(r"^([\d.]+)\s*([KMGT]?i?B)$", text, re.I)
    if not match:
        return None
    value = float(match.group(1))
    unit = match.group(2).upper()
    factors = {
        "B": 1, "KB": 1000, "MB": 1000**2, "GB": 1000**3, "TB": 1000**4,
        "KIB": 1024, "MIB": 1024**2, "GIB": 1024**3, "TIB": 1024**4,
    }
    return int(value * factors.get(unit, 1))


def parse_ytdlp_line(job_id, line):
    # yt-dlp's newline progress format includes percent, total, speed and ETA.
    match = re.search(r"(\d+(?:\.\d+)?)%\s+of\s+~?\s*([\d.]+\s*[KMGT]?i?B|Unknown)", line, re.I)
    if not match:
        match = re.search(r"(\d+(?:\.\d+)?)%", line)
    if not match:
        return
    pct = max(0.0, min(100.0, float(match.group(1))))
    total = parse_size(match.group(2)) if match.lastindex and match.lastindex >= 2 else None
    speed_match = re.search(r"\bat\s+([\d.]+\s*[KMGT]?i?B/s)", line, re.I)
    eta_match = re.search(r"\bETA\s+([0-9:]+)", line, re.I)
    downloaded = None
    if total:
        downloaded = int(total * pct / 100)
    changes = {"status": "downloading", "stage_progress": round(pct, 1), "progress": round(pct * 0.85, 1)}
    if total:
        changes["source_size"] = total
    if downloaded is not None:
        changes["downloaded_bytes"] = downloaded
    if speed_match:
        changes["speed"] = speed_match.group(1).strip()
    if eta_match:
        changes["eta"] = eta_match.group(1)
    update_job(job_id, **changes)


def process_output(job_id, cmd, phase):
    proc = subprocess.Popen(
        cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        text=True, bufsize=1, universal_newlines=True, start_new_session=True
    )
    with PROCESS_LOCK:
        PROCESSES[job_id] = proc
    duration = None
    if phase == "processing":
        try:
            source = jobs.get(job_id, {}).get("source_file")
            probe = subprocess.run(
                ["ffprobe", "-v", "error", "-show_entries", "format=duration",
                 "-of", "default=noprint_wrappers=1:nokey=1", source],
                capture_output=True, text=True, timeout=20, check=False
            )
            if probe.returncode == 0:
                duration = float(probe.stdout.strip())
        except Exception:
            duration = None
    ff_progress = {}
    last_error = ""
    try:
        for raw in proc.stdout:
            line = raw.strip()
            if line and ("ERROR:" in line or "Error while" in line or "Conversion failed" in line):
                last_error = line[-700:]
                with LOCK:
                    job_url = str((jobs.get(job_id) or {}).get("url") or "")
                if job_url:
                    last_error = last_error.replace(job_url, "[video URL]")
            if phase == "downloading":
                parse_ytdlp_line(job_id, line)
            else:
                if "=" in line:
                    key, value = line.split("=", 1)
                    ff_progress[key] = value
                    if key in ("out_time_ms", "out_time_us") and duration and duration > 0:
                        try:
                            # FFmpeg's out_time_ms is historically microseconds despite its name.
                            pct = min(100.0, max(0.0, float(value) / (duration * 1_000_000) * 100))
                            update_job(job_id, status="processing", stage_progress=round(pct, 1),
                                       progress=round(85 + pct * 0.14, 1), stage="Compressing video")
                        except ValueError:
                            pass
                if line.startswith("progress=") and line.endswith("end"):
                    update_job(job_id, status="processing", stage_progress=100, progress=99)
        proc.wait()
        if proc.returncode != 0 and last_error:
            update_job(job_id, error=last_error[:500])
        return proc.returncode
    finally:
        with PROCESS_LOCK:
            if PROCESSES.get(job_id) is proc:
                PROCESSES.pop(job_id, None)
        try:
            if proc.stdout:
                proc.stdout.close()
        except Exception:
            pass


def cleanup_sources(job_id, folder):
    for path in glob.glob(str(folder / f"{job_id}_source.*")):
        try:
            if os.path.isfile(path):
                os.remove(path)
        except OSError:
            pass
    for path in glob.glob(str(folder / f"{job_id}_source*.part")):
        try:
            os.remove(path)
        except OSError:
            pass


def youtube_cookie_file():
    """Materialize the optional Render Base64 cookie secret privately."""
    encoded = os.getenv("YOUTUBE_COOKIES_BASE64", "").strip()
    if not encoded:
        return None
    try:
        raw = base64.b64decode(encoded, validate=True)
        if not raw.startswith(b"# Netscape HTTP Cookie File") and not raw.startswith(b"# HTTP Cookie File"):
            raise ValueError("not a Netscape cookies file")
        path = Path(tempfile.gettempdir()) / "my1080p-youtube-cookies.txt"
        path.write_bytes(raw)
        try:
            path.chmod(0o600)
        except OSError:
            pass
        return str(path)
    except Exception as exc:
        app.logger.warning("YOUTUBE_COOKIES_BASE64 could not be decoded as a Netscape cookie file: %s", type(exc).__name__)
        return None


def run_job(job_id):
    try:
        with LOCK:
            job = jobs.get(job_id)
            if not job:
                return
            if job.get("cancel_requested"):
                update_job(job_id, status="cancelled", error="Cancelled")
                return
            job_url = job["url"]
            folder_name = job.get("folder_name", "Videos")
        folder = output_dir_for(folder_name)
        final_path = folder / f"{job_id}.mp4"
        template = str(folder / f"{job_id}_source.%(ext)s")
        update_job(job_id, status="downloading", progress=0, stage_progress=0, speed="", eta="", error="")
        selected_format = str(job.get("format_id") or "").strip()
        # Frontend sends a resolution marker, not an arbitrary yt-dlp expression.
        height_match = re.fullmatch(r"height:(\d{2,4})", selected_format)
        if height_match:
            height = int(height_match.group(1))
            fmt = f"bestvideo[height={height}]+bestaudio/best[height={height}]/best[height<={height}]"
        else:
            fmt = "bestvideo*[height<=1080]+bestaudio/best[height<=1080]/best"
        cmd_dl = [
            "yt-dlp", "--newline", "--no-warnings", "--no-playlist",
            "--js-runtimes", "deno",
            "--continue", "--retries", "5", "--fragment-retries", "5",
            "--retry-sleep", "http:2", "--retry-sleep", "fragment:2",
            "--socket-timeout", "45", "--force-overwrites",
            "-f", fmt,
            "--merge-output-format", "mp4", "-o", template,
        ]
        cookies = youtube_cookie_file() if any(host in job_url.lower() for host in ("youtube.com", "youtu.be", "youtube-nocookie.com")) else None
        if cookies:
            cmd_dl.extend(["--cookies", cookies])
        # Aoneroom's signed media URLs may be hotlink-protected. Supply the
        # source site's referer and browser-like headers without touching the
        # signed URL itself. Normal user-submitted URLs keep the default flow.
        if str(job.get("source", "")).lower() in ("videodownloader.site", "h5-api.aoneroom.com"):
            cmd_dl.extend([
                "--referer", "https://videodownloader.site/",
                "--add-headers", "Origin:https://videodownloader.site",
                "--add-headers", "Accept: */*",
                "--add-headers", "Accept-Language:en-US,en;q=0.9",
                "--user-agent", SITE_HEADERS["User-Agent"],
            ])
        cmd_dl.append(job_url)
        anime_meta = job.get("animepahe_meta")
        if anime_meta:
            source_path = folder / f"{job_id}_source.mp4"
            try:
                sess = requests.Session()
                for cookie in anime_meta.get("cookies", []):
                    try:
                        sess.cookies.set(cookie.get("name"), cookie.get("value"), domain=cookie.get("domain"), path=cookie.get("path", "/"))
                    except Exception:
                        pass
                referer = anime_meta.get("referer", job_url)
                headers = {"User-Agent": SITE_HEADERS["User-Agent"], "Referer": referer,
                           "Origin": urllib.parse.urlsplit(referer).scheme + "://" + urllib.parse.urlsplit(referer).netloc,
                           "Accept": "*/*", "Accept-Language": "en-US,en;q=0.9"}
                with sess.post(anime_meta["post_url"], data={"_token": anime_meta["token"]}, headers=headers, stream=True, timeout=(30, 120), allow_redirects=True) as resp:
                    resp.raise_for_status()
                    ctype = (resp.headers.get("Content-Type") or "").lower()
                    if "text/html" in ctype or "application/json" in ctype:
                        raise RuntimeError("The provider returned a web page instead of a video file.")
                    total = int(resp.headers.get("Content-Length") or 0)
                    received = 0
                    with open(source_path, "wb") as out:
                        for chunk in resp.iter_content(chunk_size=1024 * 512):
                            if not chunk: continue
                            with LOCK:
                                cancelled_now = jobs.get(job_id, {}).get("cancel_requested", False)
                            if cancelled_now: break
                            out.write(chunk); received += len(chunk)
                            pct = min(84, int(received * 84 / total)) if total else 0
                            update_job(job_id, status="downloading", progress=pct, stage_progress=pct,
                                       downloaded_bytes=received, speed="", eta="", stage="Downloading AnimePahe episode")
                with LOCK:
                    cancelled = jobs.get(job_id, {}).get("cancel_requested", False)
                if cancelled:
                    source_path.unlink(missing_ok=True)
                    cleanup_sources(job_id, folder)
                    update_job(job_id, status="cancelled", error="Cancelled", speed="", eta="")
                    return
                if not source_path.exists() or source_path.stat().st_size < 1024:
                    raise RuntimeError("The provider returned an empty or invalid video response.")
                rc = 0
            except Exception as exc:
                source_path.unlink(missing_ok=True)
                update_job(job_id, status="failed", error=f"AnimePahe download failed: {type(exc).__name__}. The source may have expired; retry the job.", speed="", eta="")
                return
        else:
            rc = process_output(job_id, cmd_dl, "downloading")
        with LOCK:
            job = jobs.get(job_id, {})
            cancelled = job.get("cancel_requested", False)
        if cancelled:
            cleanup_sources(job_id, folder)
            update_job(job_id, status="cancelled", error="Cancelled", speed="", eta="")
            return
        candidates = []
        for path in glob.glob(str(folder / f"{job_id}_source.*")):
            if os.path.isfile(path) and not path.endswith((".part", ".ytdl", ".json")):
                candidates.append(path)
        if rc != 0 or not candidates:
            with LOCK:
                detail = str((jobs.get(job_id) or {}).get("error") or "")
            message = detail if detail else "Download failed. Check the URL and try again."
            update_job(job_id, status="failed", error=message[:500], speed="", eta="")
            return
        source_path = max(candidates, key=os.path.getsize)
        source_size = os.path.getsize(source_path)
        mode = str(job.get("download_mode", "compress")).lower()
        with LOCK:
            cancelled = jobs.get(job_id, {}).get("cancel_requested", False)
        if cancelled:
            cleanup_sources(job_id, folder)
            update_job(job_id, status="cancelled", error="Cancelled", speed="", eta="")
            return
        if mode == "original":
            # Keep the downloaded file exactly as received; don't run FFmpeg.
            source_ext = Path(source_path).suffix or ".bin"
            final_size = source_size
            saved = 0.0
            update_job(job_id, status="ready", progress=100, stage_progress=100, speed="", eta="",
                       file=f"{job_id}{source_ext}", file_path=str(source_path), final_size=final_size,
                       saved_percent=saved, stage="Original quality", error="")
            return

        candidate_path = folder / f"{job_id}_compressed.mp4"
        update_job(job_id, status="processing", source_file=str(source_path),
                   source_size=source_size, progress=85, stage_progress=0, speed="", eta="", stage="Compressing (fast preset)")
        cmd_ff = [
            "ffmpeg", "-hide_banner", "-loglevel", "error", "-y", "-i", str(source_path),
            "-map", "0:v:0?", "-map", "0:a:0?", "-c:v", "libx264", "-preset", "ultrafast",
            "-crf", "28",
            "-vf", "scale='min(1920,iw)':'min(1080,ih)':force_original_aspect_ratio=decrease:force_divisible_by=2",
            "-c:a", "aac", "-b:a", "128k", "-movflags", "+faststart",
            "-progress", "pipe:1", "-nostats", str(candidate_path)
        ]
        rc_ff = process_output(job_id, cmd_ff, "processing")
        with LOCK:
            cancelled = jobs.get(job_id, {}).get("cancel_requested", False)
        if cancelled:
            candidate_path.unlink(missing_ok=True)
            cleanup_sources(job_id, folder)
            update_job(job_id, status="cancelled", error="Cancelled", speed="", eta="")
            return
        if rc_ff != 0 or not candidate_path.exists() or candidate_path.stat().st_size == 0:
            candidate_path.unlink(missing_ok=True)
            with LOCK:
                detail = str((jobs.get(job_id) or {}).get("error") or "")
            message = detail if detail else "Compression failed. Check server logs and retry."
            update_job(job_id, status="failed", error=message[:500], speed="", eta="")
            return
        compressed_size = candidate_path.stat().st_size
        if compressed_size >= source_size:
            # Never deliver a larger file as the result of a compression job.
            candidate_path.unlink(missing_ok=True)
            final_path = Path(source_path)
            final_size = source_size
            saved = 0.0
            result_name = f"{job_id}{final_path.suffix or '.bin'}"
            result_stage = "Original kept (compression would be larger)"
        else:
            final_path = folder / f"{job_id}.mp4"
            os.replace(candidate_path, final_path)
            try:
                Path(source_path).unlink(missing_ok=True)
            except OSError:
                pass
            final_size = compressed_size
            saved = (source_size - final_size) / source_size * 100 if source_size else 0.0
            result_name = f"{job_id}.mp4"
            result_stage = "Compressed"
        # Remove only temporary fragments; never delete the chosen final file.
        for temp in glob.glob(str(folder / f"{job_id}_source*.part")) + glob.glob(str(folder / f"{job_id}_source*.ytdl")):
            try: os.remove(temp)
            except OSError: pass
        update_job(job_id, status="ready", progress=100, stage_progress=100, speed="", eta="",
                   file=result_name, file_path=str(final_path), final_size=final_size,
                   saved_percent=round(saved, 1), stage=result_stage, error="")
    except Exception as exc:
        update_job(job_id, status="failed", error=f"Job failed: {type(exc).__name__}. Please retry.", speed="", eta="")
    finally:
        with LOCK:
            RUNNING_IDS.discard(job_id)


def dispatcher():
    while True:
        try:
            to_start = []
            with LOCK:
                limit = max(1, min(4, int(settings.get("max_concurrent", 3))))
                available = limit - len(RUNNING_IDS)
                if available > 0:
                    for job_id, job in sorted(jobs.items(), key=lambda item: item[1].get("created", 0)):
                        if available <= 0:
                            break
                        if job.get("status") == "queued" and job_id not in RUNNING_IDS:
                            RUNNING_IDS.add(job_id)
                            job["status"] = "starting"
                            job["updated"] = time.time()
                            to_start.append(job_id)
                            available -= 1
                    if to_start:
                        save_jobs_locked()
            for job_id in to_start:
                threading.Thread(target=run_job, args=(job_id,), daemon=True).start()
        except Exception:
            pass
        time.sleep(0.5)


def require_login():
    return bool(APP_PASSWORD) and not session.get("authenticated")


@app.before_request
def protect_routes():
    if request.endpoint in ("login", "health", "static"):
        return None
    if require_login():
        if request.path.startswith("/api/"):
            return jsonify({"error": "Login required"}), 401
        return redirect(url_for("login"))
    return None


@app.route("/login", methods=["GET", "POST"])
def login():
    if not APP_PASSWORD:
        return redirect(url_for("index"))
    if request.method == "POST":
        if request.form.get("password", "") == APP_PASSWORD:
            session["authenticated"] = True
            return redirect(url_for("index"))
        flash("Incorrect password. Try again.", "error")
    return render_template("login.html")


@app.route("/logout", methods=["POST"])
def logout():
    session.clear()
    return redirect(url_for("login"))


@app.route("/")
def index():
    return render_template("index.html", auth_enabled=bool(APP_PASSWORD))


def anilist_graphql(query, variables=None):
    """Call AniList with short retries and a stale-cache fallback."""
    cache_key = json.dumps([query, variables or {}], sort_keys=True, ensure_ascii=False)
    now = time.time()
    with ANILIST_CACHE_LOCK:
        cached = ANILIST_CACHE.get(cache_key)
        if cached and now - cached[0] <= ANILIST_CACHE_TTL:
            return cached[1]

    body = json.dumps({"query": query, "variables": variables or {}}).encode("utf-8")
    last_error = None
    for attempt in range(3):
        req = urllib.request.Request(
            "https://graphql.anilist.co",
            data=body,
            headers={
                "Content-Type": "application/json",
                "Accept": "application/json",
                "User-Agent": "My1080pSaver/1.1 (My1080p Saver anime catalogue)",
            },
            method="POST",
        )
        try:
            with urllib.request.urlopen(req, timeout=10) as response:
                payload = json.loads(response.read(2_000_000).decode("utf-8"))
            if payload.get("errors"):
                raise ValueError("AniList returned an API error.")
            data = payload.get("data") or {}
            with ANILIST_CACHE_LOCK:
                ANILIST_CACHE[cache_key] = (time.time(), data)
            return data
        except urllib.error.HTTPError as exc:
            last_error = exc
            if exc.code not in (429, 500, 502, 503, 504) or attempt == 2:
                break
            retry_after = exc.headers.get("Retry-After", "") if exc.headers else ""
            try:
                delay = min(2.0, max(0.25, float(retry_after)))
            except (TypeError, ValueError):
                delay = 0.4 * (attempt + 1)
            time.sleep(delay)
        except (urllib.error.URLError, TimeoutError, OSError, ValueError, json.JSONDecodeError) as exc:
            last_error = exc
            if attempt == 2:
                break
            time.sleep(0.25 * (attempt + 1))
    # A previously successful result is better than failing during a temporary outage.
    with ANILIST_CACHE_LOCK:
        cached = ANILIST_CACHE.get(cache_key)
    if cached and time.time() - cached[0] <= ANILIST_STALE_TTL:
        return cached[1]
    raise RuntimeError("AniList is temporarily unavailable. Check the connection and try again.") from last_error


def archive_license_url(value):
    """Return a recognized open license URL; reject unknown or missing licenses."""
    value = str(value or "").strip()
    if not value:
        return ""
    match = re.fullmatch(
        r"https?://creativecommons\.org/(?:licenses/(?:by-nc-sa|by-nc|by-sa|by)/[0-9.]+|publicdomain/(?:zero|mark)/[0-9.]+)/?",
        value.rstrip("/"), re.I
    )
    return value if match else ""


def archive_json(url, timeout=8):
    req = urllib.request.Request(url, headers={"Accept": "application/json", "User-Agent": "My1080pSaver/1.1"})
    with urllib.request.urlopen(req, timeout=timeout) as response:
        return json.loads(response.read(3_000_000).decode("utf-8"))


def archive_video_file(identifier, files):
    allowed = {".mp4", ".m4v", ".webm", ".mov", ".mkv", ".avi", ".mpeg", ".mpg"}
    candidates = []
    for item in files if isinstance(files, list) else []:
        name = str(item.get("name") or "")
        if Path(name).suffix.lower() not in allowed:
            continue
        if item.get("private") in ("true", True, 1) or item.get("source") == "derivative" and item.get("format") == "Metadata":
            continue
        if not re.fullmatch(r"[A-Za-z0-9._ -]+", name) or name in (".", ".."):
            continue
        size = item.get("size")
        try:
            size = int(size) if size is not None else None
        except (TypeError, ValueError):
            size = None
        candidates.append((0 if Path(name).suffix.lower() == ".mp4" else 1, -(size or 0), name, size))
    if not candidates:
        return None
    _, _, name, size = sorted(candidates)[0]
    direct = "https://archive.org/download/{}/{}".format(
        urllib.parse.quote(identifier, safe=""), urllib.parse.quote(name, safe="")
    )
    return {"download_url": direct, "file_name": name, "size": size or None}


def normalize_anilist(item):
    """Map AniList's response to the fields already used by the page."""
    title = item.get("title") or {}
    cover = item.get("coverImage") or {}
    start_date = item.get("startDate") or {}
    studios = (item.get("studios") or {}).get("nodes") or []
    description = item.get("description") or "No synopsis is available."
    return {
        "id": item.get("id"),
        "title": title.get("english") or title.get("romaji") or title.get("native") or "Untitled",
        "english_title": title.get("english"),
        "japanese_title": title.get("native"),
        "image": cover.get("extraLarge") or cover.get("large") or "",
        "synopsis": description,
        "year": item.get("seasonYear") or start_date.get("year"),
        "episodes": item.get("episodes"),
        "status": (item.get("status") or "Unknown").replace("_", " ").title(),
        "score": (item.get("averageScore") / 10) if isinstance(item.get("averageScore"), (int, float)) else None,
        "type": item.get("format") or "Anime",
        "rating": None,
        "season": (item.get("season") or "").title(),
        "studios": [studio.get("name") for studio in studios if studio.get("name")],
        "genres": item.get("genres") or [],
        "url": item.get("siteUrl") or "",
        "streaming_episodes": [
            {"title": ep.get("title") or "Episode", "thumbnail": ep.get("thumbnail") or "", "url": ep.get("url") or ""}
            for ep in (item.get("streamingEpisodes") or [])
            if isinstance(ep, dict) and ep.get("url", "").startswith(("https://", "http://"))
        ][:40],
    }


ANIME_FIELDS = """
    id
    title { romaji english native }
    coverImage { extraLarge large }
    description(asHtml: false)
    season
    seasonYear
    episodes
    status
    averageScore
    genres
    siteUrl
    streamingEpisodes { title thumbnail url }
    format
    countryOfOrigin
    startDate { year }
    studios(isMain: true) { nodes { name } }
"""


SITE_API = "https://h5-api.aoneroom.com/wefeed-h5api-bff"
# Match the browser request headers observed in the user's HAR. The catalogue
# API itself is h5-api.aoneroom.com; videodownloader.site is only the web client
# whose request flow was captured.
SITE_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Android 14; Mobile; rv:155.0) Gecko/155.0 Firefox/155.0",
    "Accept": "application/json",
    "Accept-Language": "en-US",
    "X-Source": "downloader",
    "x-request-lang": "en",
    "X-Client-Info": json.dumps({"timezone": os.getenv("TZ", "Africa/Lagos")}),
    "Origin": "https://videodownloader.site",
    "Referer": "https://videodownloader.site/",
    "Sec-Fetch-Dest": "empty",
    "Sec-Fetch-Mode": "cors",
    "Sec-Fetch-Site": "cross-site",
}

_SITE_TOKEN_CACHE = ""
_SITE_TOKEN_CACHE_AT = 0.0
_SITE_TOKEN_LOCK = threading.Lock()
_SITE_TOKEN_TTL = 180  # site-issued tokens have a short ext window in the captured HAR


def _manual_site_token():
    with LOCK:
        return str(settings.get("videodownloader_token") or os.getenv("VIDEODOWNLOADER_TOKEN", "")).strip()


def acquire_site_token(force=False, keyword="anime"):
    """Obtain the short-lived bearer token through the API flow observed in the HAR.

    The site's successful /subject/search-suggest response sets a `token` cookie.
    The browser then sends that JWT as a Bearer token to protected catalogue routes.
    This reproduces that API exchange directly; it does not load the website in a browser.
    """
    global _SITE_TOKEN_CACHE, _SITE_TOKEN_CACHE_AT
    manual = _manual_site_token()
    if manual:
        return manual if manual.lower().startswith("bearer ") else "Bearer " + manual

    with _SITE_TOKEN_LOCK:
        now = time.time()
        if not force and _SITE_TOKEN_CACHE and (now - _SITE_TOKEN_CACHE_AT) < _SITE_TOKEN_TTL:
            return "Bearer " + _SITE_TOKEN_CACHE

        # HAR format: X-Client-Token: unix_timestamp,32_hex_chars.
        client_token = f"{int(now)},{secrets.token_hex(16)}"
        headers = dict(SITE_HEADERS)
        headers["Content-Type"] = "application/json"
        headers["X-Client-Token"] = client_token
        body = json.dumps({"keyword": (str(keyword or "anime").strip()[:100] or "anime"), "perPage": 30}).encode("utf-8")
        req = urllib.request.Request(SITE_API + "/subject/search-suggest", data=body, headers=headers, method="POST")
        try:
            with urllib.request.urlopen(req, timeout=20) as response:
                response.read(1024 * 1024)
                cookie_headers = response.headers.get_all("Set-Cookie") or []
                # Some gateways normalize the header casing; search case-insensitively too.
                if not cookie_headers:
                    cookie_headers = [v for k, v in response.headers.items() if k.lower() == "set-cookie"]
            token = ""
            for cookie in cookie_headers:
                match = re.search(r"(?:^|[,;]\s*)token=([^;]+)", cookie)
                if match:
                    token = match.group(1).strip()
                    break
            if not token:
                raise RuntimeError("The catalogue token bootstrap did not return a token cookie. The site's API flow may have changed.")
            _SITE_TOKEN_CACHE = token
            _SITE_TOKEN_CACHE_AT = time.time()
            return "Bearer " + token
        except urllib.error.HTTPError as exc:
            # Never echo response headers or tokens into the UI/logs.
            raise RuntimeError(f"Catalogue authorization bootstrap returned HTTP {exc.code}.") from exc
        except urllib.error.URLError as exc:
            raise RuntimeError("Could not reach the catalogue authorization endpoint. Check the server's internet connection.") from exc


def site_api_request(path, method="GET", payload=None, query=None):
    """Call the underlying Aoneroom catalogue API using the HAR-observed flow."""
    global _SITE_TOKEN_CACHE, _SITE_TOKEN_CACHE_AT
    url = SITE_API + path
    if query:
        url += "?" + urllib.parse.urlencode(query)
    data = None
    headers = dict(SITE_HEADERS)
    if payload is not None:
        headers["Content-Type"] = "application/json"
        data = json.dumps(payload).encode("utf-8")

    last_auth_error = None
    for attempt in range(2):
        token = acquire_site_token(force=(attempt == 1), keyword=(payload or {}).get("keyword", "anime"))
        request_headers = dict(headers)
        request_headers["Authorization"] = token if token.lower().startswith("bearer ") else "Bearer " + token
        req = urllib.request.Request(url, data=data, headers=request_headers, method=method)
        try:
            with urllib.request.urlopen(req, timeout=25) as response:
                raw = response.read(4 * 1024 * 1024)
            obj = json.loads(raw.decode("utf-8"))
            code = obj.get("code") if isinstance(obj, dict) else None
            if str(code) in ("401", "403", "406", "1001", "1002"):
                last_auth_error = RuntimeError("The catalogue rejected the request or its authorization token.")
                _SITE_TOKEN_CACHE = ""
                _SITE_TOKEN_CACHE_AT = 0.0
                if attempt == 0:
                    continue
                raise RuntimeError("The catalogue rejected the request after a fresh token was obtained. Its request requirements may have changed.")
            if code not in (None, 0, 200, "0", "200", "success"):
                msg = str(obj.get("message") or obj.get("msg") or "API request failed")[:180]
                raise RuntimeError("Aoneroom catalogue API: " + msg)
            return obj
        except urllib.error.HTTPError as exc:
            if exc.code in (401, 403, 406):
                last_auth_error = exc
                _SITE_TOKEN_CACHE = ""
                _SITE_TOKEN_CACHE_AT = 0.0
                if attempt == 0:
                    continue
                if exc.code == 406:
                    raise RuntimeError("The Aoneroom catalogue API returned HTTP 406 even after refreshing its token. The upstream API is rejecting this request; its requirements may have changed.") from exc
                raise RuntimeError("The catalogue rejected the request after a fresh token was obtained.") from exc
            raise RuntimeError(f"Aoneroom catalogue API returned HTTP {exc.code} for {path}.") from exc
        except (urllib.error.URLError, TimeoutError, json.JSONDecodeError) as exc:
            raise RuntimeError("Could not reach the video catalogue. Check the server's internet connection and try again.") from exc
    raise RuntimeError("Could not authorize with videodownloader.site.") from last_auth_error

def _site_walk(value):
    if isinstance(value, dict):
        yield value
        for v in value.values():
            yield from _site_walk(v)
    elif isinstance(value, list):
        for v in value:
            yield from _site_walk(v)

def _site_first(item, *keys):
    for key in keys:
        value = item.get(key)
        if value not in (None, "", [], {}):
            return value
    return None

def _site_subjects(payload):
    """Normalize the catalogue's varying response envelopes without inventing titles."""
    found, seen = [], set()
    for obj in _site_walk(payload):
        detail = _site_first(obj, "detailPath", "detail_path", "detailpath")
        sid = _site_first(obj, "subjectId", "subject_id", "subjectID")
        title = _site_first(obj, "subjectName", "subject_name", "title", "name", "nameEn", "nameCn", "name_en", "name_cn")
        # Avoid mistaking metadata or response envelope objects for a result.
        if detail and sid and title and isinstance(title, str) and len(title) < 300:
            key = (str(sid), str(detail))
            if key in seen: continue
            seen.add(key)
            found.append({"subject_id": str(sid), "detail_path": str(detail), "title": title,
                          "image": _site_first(obj, "cover", "coverUrl", "cover_url", "image", "poster", "coverImage", "cover_image") or "",
                          "description": str(_site_first(obj, "description", "intro", "synopsis", "overview") or "")[:500],
                          "raw_type": str(_site_first(obj, "subjectType", "type") or "")})
    return found[:30]

def _site_episodes(payload):
    out, seen = [], set()
    for obj in _site_walk(payload):
        ep = _site_first(obj, "ep", "episode", "episodeNo", "episodeNumber", "episode_no", "episode_number", "episodeIndex", "episode_index")
        se = _site_first(obj, "se", "season", "seasonNo", "seasonNumber", "season_no", "season_number")
        # Episode objects are only accepted when they include a plausible episode number.
        try: ep_num = int(ep)
        except (TypeError, ValueError): continue
        if not 1 <= ep_num <= 999: continue
        try: se_num = int(se or 1)
        except (TypeError, ValueError): se_num = 1
        key = (se_num, ep_num)
        if key in seen: continue
        seen.add(key)
        out.append({"season": se_num, "episode": ep_num,
                    "title": str(_site_first(obj, "name", "title", "episodeName", "episode_name") or f"Episode {ep_num}")[:180],
                    "subject_id": str(_site_first(obj, "subjectId", "subject_id", "subjectID") or "")})
    return sorted(out, key=lambda x: (x["season"], x["episode"]))[:500]

def _site_media_url(payload):
    """Extract a direct/signed video URL from the catalogue response.

    Keep candidate URL strings byte-for-byte as returned: signatures and their
    query-parameter order must not be decoded, sorted, or rebuilt. Prefer fields
    explicitly named for media, then signed CDN links. Never prefer poster/image
    URLs merely because they happen to live on a CDN.
    """
    media_keys = {
        "url", "downloadurl", "download_url", "downloadlink", "download_link",
        "resourceurl", "resource_url", "videourl", "video_url", "playurl",
        "play_url", "streamurl", "stream_url", "src", "fileurl", "file_url",
        "m3u8", "mp4", "hlsurl", "hls_url", "masterurl", "master_url",
        "mediaurl", "media_url", "signedurl", "signed_url", "signeddownloadurl",
        "signed_download_url", "originurl", "origin_url", "backupurl", "backup_url",
        "download", "stream", "playbackurl", "playback_url", "video",
    }
    image_keys = {"cover", "coverurl", "cover_url", "poster", "image", "imageurl",
                  "image_url", "thumbnail", "thumbnailurl", "thumbnail_url", "avatar"}
    image_exts = (".jpg", ".jpeg", ".png", ".gif", ".webp", ".avif", ".bmp", ".svg")
    video_exts = (".mp4", ".m3u8", ".mkv", ".mpd", ".m4v", ".webm", ".mov", ".ts")
    candidates = {}

    def walk(value, key_hint="", parent_is_image=False):
        if isinstance(value, dict):
            for key, child in value.items():
                normalized = re.sub(r"[^a-z0-9_]", "", str(key).lower())
                walk(child, normalized, parent_is_image or normalized in image_keys)
            return
        if isinstance(value, list):
            for child in value:
                walk(child, key_hint, parent_is_image)
            return
        if not isinstance(value, str):
            return
        candidate = value.strip()
        if not candidate.startswith(("https://", "http://")) or parent_is_image or key_hint in image_keys:
            return
        try:
            parsed = urllib.parse.urlsplit(candidate)
        except ValueError:
            return
        if not parsed.hostname:
            return
        host, path, query = parsed.hostname.lower(), parsed.path.lower(), parsed.query.lower()
        if path.endswith(image_exts):
            return
        # Ignore obvious API/catalogue pages unless the API explicitly labels
        # the field as a media URL.
        explicit_media_key = key_hint in media_keys
        is_video_path = any(path.endswith(ext) for ext in video_exts)
        has_signature = any(mark in query for mark in (
            "sign=", "signature=", "token=", "expires=", "expire=", "auth_key=",
            "policy=", "x-amz-", "x-oss-", "hdnts=", "key-pair-id="
        ))
        media_host = any(word in host for word in ("cdn", "video", "media", "stream", "download", "storage", "oss"))
        media_path = any(word in path for word in ("video", "media", "stream", "download", "play", "hls"))
        if not (explicit_media_key or is_video_path or has_signature or media_host or media_path):
            return
        # Lower score wins. Explicit media fields and recognizable video files
        # outrank generic signed URLs; image URLs have already been discarded.
        score = (0 if explicit_media_key else 3)
        score += (0 if is_video_path else 2)
        score += (0 if has_signature else 1)
        score += (0 if media_host or media_path else 1)
        candidates[candidate] = min(score, candidates.get(candidate, score))

    walk(payload)
    for candidate, _score in sorted(candidates.items(), key=lambda item: item[1]):
        ok, _reason = valid_public_http_url(candidate)
        if ok:
            return candidate
    return None

@app.route("/api/site/search", methods=["GET"])
def site_search():
    query = str(request.args.get("q", "")).strip()[:100]
    if len(query) < 2:
        return jsonify({"error": "Enter at least two characters."}), 400
    try:
        payload = site_api_request("/subject/search", "POST", {"keyword": query, "page": 1, "perPage": 15, "subjectType": 0})
        results = _site_subjects(payload)
        return jsonify({"results": results, "source": "h5-api.aoneroom.com"})
    except RuntimeError as exc:
        return jsonify({"error": str(exc)}), 502

@app.route("/api/site/episodes", methods=["GET"])
def site_episodes():
    detail_path = str(request.args.get("detailPath", "")).strip()[:240]
    if not detail_path or not re.fullmatch(r"[A-Za-z0-9._/-]+", detail_path):
        return jsonify({"error": "Invalid catalogue result."}), 400
    try:
        payload = site_api_request("/detail", query={"detailPath": detail_path})
        return jsonify({"detail": payload, "episodes": _site_episodes(payload), "detail_path": detail_path})
    except RuntimeError as exc:
        return jsonify({"error": str(exc)}), 502

@app.route("/api/site/resolve", methods=["POST"])
def site_resolve():
    data = request.get_json(silent=True) or {}
    detail_path = str(data.get("detailPath", "")).strip()[:240]
    subject_id = str(data.get("subjectId", "")).strip()[:80]
    try:
        season, episode = int(data.get("season", 1)), int(data.get("episode", 1))
    except (TypeError, ValueError):
        return jsonify({"error": "Choose a valid season and episode."}), 400
    if not detail_path or not subject_id or not re.fullmatch(r"[A-Za-z0-9._/-]+", detail_path) or not (1 <= season <= 99 and 1 <= episode <= 999):
        return jsonify({"error": "Invalid catalogue selection."}), 400
    try:
        payload = site_api_request("/subject/download", query={"subjectId": subject_id, "se": season, "ep": episode, "detailPath": detail_path, "supportCodecs[h264]": 1, "supportCodecs[hevc]": 1})
        media_url = _site_media_url(payload)
        if not media_url:
            return jsonify({"error": "The site did not return a direct media URL. This can happen when the response is not available to this account or region."}), 502
        ok, reason = valid_public_http_url(media_url)
        if not ok:
            return jsonify({"error": "The site returned an unsafe or invalid media URL."}), 502
        return jsonify({"url": media_url, "title": f"{detail_path} S{season:02d}E{episode:02d}", "source": "h5-api.aoneroom.com"})
    except RuntimeError as exc:
        return jsonify({"error": str(exc)}), 502

ANIMEPAHE_HOSTS = {"animepahe.si", "animepahe.ru", "animepahe.com"}

def animepahe_url_ok(raw):
    try:
        parsed = urlparse(str(raw or "").strip())
        return parsed.scheme == "https" and (parsed.hostname or "").lower() in ANIMEPAHE_HOSTS and parsed.path.startswith(("/play/", "/a/", "/anime/", "/"))
    except Exception:
        return False

def animepahe_browser_flow(target_url, want_episodes=False):
    if not animepahe_url_ok(target_url):
        raise ValueError("Paste a valid HTTPS AnimePahe page URL.")
    with sync_playwright() as p:
        browser = p.chromium.launch(headless=True, args=["--no-sandbox", "--disable-dev-shm-usage"])
        context = browser.new_context(user_agent=SITE_HEADERS["User-Agent"])
        page = context.new_page()
        try:
            page.goto(target_url, wait_until="domcontentloaded", timeout=60000)
            if want_episodes:
                page.wait_for_selector("a.play", timeout=25000)
                items = page.eval_on_selector_all("a.play", "els => els.map((e,i) => ({title:(e.innerText||e.getAttribute('title')||('Episode '+(i+1))).trim(), url:e.href})).filter(x=>x.url)")
                return items[:500]
            page.wait_for_selector("#downloadMenu, #pickDownload", timeout=30000)
            items = page.eval_on_selector_all("#pickDownload a.dropdown-item", "els => els.map(e => ({label:(e.innerText||'').trim(), url:e.href})).filter(x=>x.url)")
            return items[:100]
        finally:
            browser.close()

def animepahe_resolve(episode_url, quality_url):
    # AnimePahe's quality links may legitimately point to its Kwik download host.
    try:
        qparsed = urlparse(quality_url)
        qhost = (qparsed.hostname or "").lower()
        quality_host_ok = qparsed.scheme == "https" and (
            qhost in ANIMEPAHE_HOSTS or qhost == "kwik.cx" or qhost.endswith(".kwik.cx")
            or qhost == "kwik.si" or qhost.endswith(".kwik.si")
            or qhost == "kwik.to" or qhost.endswith(".kwik.to")
        )
    except Exception:
        quality_host_ok = False
    if not animepahe_url_ok(episode_url) or not quality_host_ok:
        raise ValueError("The selected episode or quality link is not a supported AnimePahe/Kwik URL.")
    with sync_playwright() as p:
        browser = p.chromium.launch(headless=True, args=["--no-sandbox", "--disable-dev-shm-usage"])
        context = browser.new_context(user_agent=SITE_HEADERS["User-Agent"])
        page = context.new_page()
        try:
            page.goto(episode_url, wait_until="domcontentloaded", timeout=60000)
            page.goto(quality_url, wait_until="domcontentloaded", timeout=60000)
            page.wait_for_selector("a.redirect", timeout=30000)
            cont = page.locator("a.redirect", has_text="Continue").first.get_attribute("href")
            if not cont:
                raise RuntimeError("The source did not provide a Continue link.")
            page.goto(urllib.parse.urljoin(page.url, cont), wait_until="domcontentloaded", timeout=60000)
            page.wait_for_selector("form:has(button)", timeout=30000)
            form = page.locator("form", has=page.locator("button", has_text="Download")).first
            if form.count() == 0:
                raise RuntimeError("The source download form was not found.")
            action = form.get_attribute("action")
            token = form.locator("input[name='_token']").get_attribute("value")
            title = page.locator("h1.title").inner_text().strip() if page.locator("h1.title").count() else "AnimePahe episode"
            if not action or not token:
                raise RuntimeError("The source download form is missing its required fields.")
            return {"post_url": urllib.parse.urljoin(page.url, action), "token": token, "title": title[:160], "cookies": context.cookies(), "referer": page.url}
        finally:
            browser.close()

@app.route("/api/animepahe/episodes", methods=["GET"])
def animepahe_episodes():
    url = str(request.args.get("url", "")).strip()[:1000]
    try:
        items = animepahe_browser_flow(url, want_episodes=True)
        return jsonify({"episodes": items, "count": len(items)})
    except ValueError as exc:
        return jsonify({"error": str(exc)}), 400
    except PlaywrightTimeoutError:
        return jsonify({"error": "AnimePahe did not show episode links in time. Check the page URL or try again later."}), 502
    except Exception as exc:
        app.logger.warning("AnimePahe episode scrape failed: %s", type(exc).__name__)
        return jsonify({"error": "Could not scrape episodes from that page. The source layout may have changed or the host may be unavailable."}), 502

@app.route("/api/animepahe/qualities", methods=["POST"])
def animepahe_qualities():
    data = request.get_json(silent=True) or {}
    url = str(data.get("url", "")).strip()[:1000]
    try:
        items = animepahe_browser_flow(url, want_episodes=False)
        return jsonify({"qualities": items})
    except ValueError as exc:
        return jsonify({"error": str(exc)}), 400
    except PlaywrightTimeoutError:
        return jsonify({"error": "The episode page did not expose download quality options in time."}), 502
    except Exception as exc:
        app.logger.warning("AnimePahe quality scrape failed: %s", type(exc).__name__)
        return jsonify({"error": "Could not read download options for this episode."}), 502

@app.route("/api/animepahe/queue", methods=["POST"])
def animepahe_queue():
    data = request.get_json(silent=True) or {}
    episode_url = str(data.get("episode_url", "")).strip()[:1000]
    quality_url = str(data.get("quality_url", "")).strip()[:1000]
    mode = "original" if str(data.get("mode", "compress")).lower() == "original" else "compress"
    try:
        meta = animepahe_resolve(episode_url, quality_url)
    except ValueError as exc:
        return jsonify({"error": str(exc)}), 400
    except PlaywrightTimeoutError:
        return jsonify({"error": "The selected quality could not be resolved in time. Try another quality."}), 502
    except Exception as exc:
        app.logger.warning("AnimePahe source resolve failed: %s", type(exc).__name__)
        return jsonify({"error": "Could not resolve this download option. The provider may have changed its page flow."}), 502
    with LOCK:
        if len(jobs) >= MAX_JOBS:
            return jsonify({"error": "Queue is full. Delete old jobs before adding more."}), 429
        job_id = uuid.uuid4().hex[:12]
        folder_name = settings.get("folder_name", "Videos")
        jobs[job_id] = {"id": job_id, "url": episode_url, "source": "AnimePahe", "title": meta["title"],
            "status": "queued", "progress": 0, "stage_progress": 0, "speed": "", "eta": "",
            "created": time.time(), "updated": time.time(), "folder_name": folder_name, "file_path": "", "error": "",
            "download_mode": mode, "animepahe_meta": meta, "cancel_requested": False}
        save_jobs_locked()
        result = public_job(jobs[job_id])
    return jsonify({"job": result}), 201

@app.route("/api/anime/search", methods=["GET"])
def anime_search():
    """Search AniList for anime metadata; does not fetch video files."""
    query = str(request.args.get("q", "")).strip()[:120]
    if len(query) < 2:
        return jsonify({"results": [], "error": "Enter at least two characters."}), 400
    # Common shorthand is not always indexed as an anime title; expand it before querying AniList.
    search_query = {"jjk": "Jujutsu Kaisen", "jujutsu kaisen": "Jujutsu Kaisen"}.get(query.casefold(), query)
    graphql = "query ($search: String) { Page(page: 1, perPage: 12) { media(search: $search, type: ANIME, sort: SEARCH_MATCH, isAdult: false) { " + ANIME_FIELDS + " } } }"
    try:
        data = anilist_graphql(graphql, {"search": search_query})
        items = ((data.get("Page") or {}).get("media") or [])
        return jsonify({"results": [normalize_anilist(item) for item in items]})
    except Exception as exc:
        app.logger.warning("AniList anime search failed: %s", exc)
        return jsonify({"error": "AniList search is temporarily unavailable. Please try again shortly."}), 502


@app.route("/api/free-videos/search", methods=["GET"])
def free_video_search():
    """Find likely exact-title, exact-episode openly licensed videos; never bypass restrictions."""
    raw_query = str(request.args.get("q", "")).strip()[:90]
    query = re.sub(r"[^A-Za-z0-9 ]", " ", raw_query)
    query = re.sub(r"\s+", " ", query).strip()
    episode_raw = str(request.args.get("episode", "")).strip()
    if len(query) < 2:
        return jsonify({"results": [], "error": "Enter at least two characters."}), 400
    if not episode_raw.isdigit() or not 1 <= int(episode_raw) <= 999:
        return jsonify({"results": [], "error": "Choose a valid episode number first."}), 400
    episode = int(episode_raw)
    # AniList often indexes Jujutsu Kaisen by its full title, not the fan acronym JJK.
    aliases = {"jjk": "Jujutsu Kaisen", "jujutsu kaisen": "Jujutsu Kaisen"}
    search_title = aliases.get(query.lower(), query)
    words = [w.lower() for w in re.findall(r"[a-z0-9]+", search_title) if len(w) > 1]
    if len(words) < 2:
        return jsonify({"results": [], "notice": "Use the full anime title to reduce unrelated matches."})
    encoded_query = urllib.parse.quote(f'mediatype:movies AND title:("{search_title}")', safe="():")
    url = ("https://archive.org/advancedsearch.php?q=" + encoded_query +
           "&fl[]=identifier&fl[]=title&fl[]=description&fl[]=licenseurl&fl[]=mediatype&rows=40&page=1&output=json")
    # Accept explicit episode markers only. A random file containing the title keyword is not enough.
    ep_patterns = [
        re.compile(rf"\bepisode\s*0*{episode}\b", re.I),
        re.compile(rf"\bep\.?\s*0*{episode}\b", re.I),
        re.compile(rf"\bs\d{{1,2}}\s*e\s*0*{episode}\b", re.I),
        re.compile(rf"\bseason\s*\d+\s*(?:episode|ep\.?)\s*0*{episode}\b", re.I),
    ]
    try:
        payload = archive_json(url)
        docs = ((payload.get("response") or {}).get("docs") or [])
        results = []
        for doc in docs:
            identifier = str(doc.get("identifier") or "").strip()
            if not re.fullmatch(r"[A-Za-z0-9._-]{1,120}", identifier):
                continue
            title = str(doc.get("title") or identifier)[:180]
            title_norm = re.sub(r"[^a-z0-9]+", " ", title.lower()).strip()
            # Require all important title words in the item title; description-only keyword hits are rejected.
            if not all(word in title_norm.split() for word in words):
                continue
            description_value = doc.get("description") or ""
            description = " ".join(map(str, description_value)) if isinstance(description_value, list) else str(description_value)
            searchable = " ".join((title, description, identifier))
            if not any(pattern.search(searchable) for pattern in ep_patterns):
                continue
            try:
                metadata_payload = archive_json("https://archive.org/metadata/" + urllib.parse.quote(identifier, safe=""))
            except Exception:
                continue
            metadata = metadata_payload.get("metadata") or {}
            license_url = archive_license_url(metadata.get("licenseurl") or doc.get("licenseurl"))
            if not license_url:
                continue
            media = archive_video_file(identifier, metadata_payload.get("files"))
            if not media:
                continue
            results.append({
                "identifier": identifier, "title": title,
                "description": re.sub(r"<[^>]+>", " ", description)[:500],
                "episode": episode, "license_url": license_url,
                "download_url": media["download_url"], "file_name": media["file_name"],
                "size": media["size"], "page_url": "https://archive.org/details/" + identifier,
                "source": "Internet Archive"
            })
            if len(results) >= 4:
                break
        return jsonify({
            "results": results, "source": "Internet Archive",
            "notice": (f"Found {len(results)} title-and-episode matches. Open each item page and verify the rights and episode before downloading."
                       if results else "No exact title + episode match with a recognized open license was found. No unrelated keyword-only results are shown.")
        })
    except Exception as exc:
        app.logger.warning("Internet Archive episode search failed: %s", exc)
        return jsonify({"error": "The licensed-video catalogue is temporarily unavailable. Try again shortly."}), 502


@app.route("/api/anime/<int:anime_id>", methods=["GET"])
def anime_details(anime_id):
    """Fetch detailed public metadata for one AniList anime entry."""
    graphql = "query ($id: Int) { Media(id: $id, type: ANIME) { " + ANIME_FIELDS + " } }"
    try:
        data = anilist_graphql(graphql, {"id": anime_id})
        item = data.get("Media")
        if not item:
            return jsonify({"error": "Anime details were not found."}), 404
        return jsonify({"anime": normalize_anilist(item)})
    except Exception as exc:
        app.logger.warning("AniList anime details failed: %s", exc)
        return jsonify({"error": "AniList details are temporarily unavailable."}), 502


@app.route("/api/formats", methods=["POST"])
def list_video_formats():
    data = request.get_json(silent=True) or {}
    url = str(data.get("url", "")).strip()
    ok, reason = valid_public_http_url(url)
    if not ok:
        return jsonify({"error": reason}), 400
    if not any(host in (urlparse(url).hostname or "").lower() for host in ("youtube.com", "youtu.be", "youtube-nocookie.com")):
        return jsonify({"formats": [], "message": "Quality picker is available for YouTube links."})
    cmd = ["yt-dlp", "--no-warnings", "--no-playlist", "--js-runtimes", "deno", "-J", "--socket-timeout", "30"]
    cookies = youtube_cookie_file()
    if cookies:
        cmd.extend(["--cookies", cookies])
    cmd.append(url)
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=75, check=False)
        if result.returncode != 0:
            detail = (result.stderr or result.stdout or "Could not read available YouTube formats.")[-700:]
            return jsonify({"error": detail}), 502
        info = json.loads(result.stdout)
        by_height = {}
        for f in info.get("formats", []):
            height = f.get("height")
            if not height or height > 4320 or not f.get("format_id"):
                continue
            # Prefer combined audio/video formats when available; otherwise yt-dlp merges video+audio.
            has_audio = f.get("acodec") not in (None, "none")
            has_video = f.get("vcodec") not in (None, "none")
            if not has_video:
                continue
            key = int(height)
            score = (1 if has_audio else 0, int(f.get("tbr") or 0))
            if key not in by_height or score > by_height[key][0]:
                by_height[key] = (score, {"format_id": f"height:{key}", "height": key,
                    "label": f"{key}p" + (" · audio included" if has_audio else " · best audio merged"),
                    "filesize": f.get("filesize") or f.get("filesize_approx"), "has_audio": has_audio})
        formats = [v[1] for _, v in sorted(by_height.items(), reverse=True)]
        formats.insert(0, {"format_id": "bestvideo*[height<=1080]+bestaudio/best[height<=1080]/best", "height": 0, "label": "Auto · best up to 1080p", "filesize": None})
        return jsonify({"title": info.get("title", "YouTube video"), "formats": formats})
    except subprocess.TimeoutExpired:
        return jsonify({"error": "Checking YouTube formats timed out. Try again or choose Auto."}), 504
    except Exception as exc:
        app.logger.warning("Format lookup failed: %s", type(exc).__name__)
        return jsonify({"error": "Could not list formats for this video."}), 502


@app.route("/api/jobs", methods=["GET"])
def list_jobs():
    with LOCK:
        items = [public_job(j) for j in jobs.values()]
    items.sort(key=lambda j: j.get("created", 0), reverse=True)
    return jsonify({"jobs": items})


@app.route("/api/add", methods=["POST"])
def add_job():
    data = request.get_json(silent=True) or {}
    url = str(data.get("url", "")).strip()
    if not url:
        return jsonify({"error": "Paste a video URL first."}), 400
    ok, reason = valid_public_http_url(url)
    if not ok:
        return jsonify({"error": reason}), 400
    with LOCK:
        active_count = len(jobs)
        if active_count >= MAX_JOBS:
            return jsonify({"error": "Queue is full. Delete old jobs before adding more."}), 429
        job_id = uuid.uuid4().hex[:12]
        folder_name = settings.get("folder_name", "Videos")
        jobs[job_id] = {
            "id": job_id, "url": url, "title": re.sub(r"[\r\n\t]+", " ", str(data.get("title") or safe_label(url)))[:160],
            "source": re.sub(r"[\r\n\t]+", " ", str(data.get("source") or urlparse(url).hostname or "Video source"))[:100],
            "status": "queued", "progress": 0, "stage_progress": 0,
            "speed": "", "eta": "", "created": time.time(), "updated": time.time(),
            "folder_name": folder_name, "file_path": "", "error": "",
            "format_id": str(data.get("format_id") or "")[:100],
            "download_mode": "original" if str(data.get("mode", "compress")).lower() == "original" else "compress",
            "cancel_requested": False
        }
        save_jobs_locked()
    return jsonify({"job": public_job(jobs[job_id])}), 201


@app.route("/api/jobs/<job_id>/pause", methods=["POST"])
def pause_job(job_id):
    with LOCK:
        job = jobs.get(job_id)
        if not job:
            return jsonify({"error": "Job not found."}), 404
        status = job.get("status")
        if status == "queued":
            job["status"] = "paused"
            job["paused_from"] = "queued"
            job["updated"] = time.time()
            save_jobs_locked()
            return jsonify({"ok": True, "job": public_job(job)})
        if status not in ("downloading", "processing", "starting"):
            return jsonify({"error": "This job cannot be paused in its current state."}), 409
    with PROCESS_LOCK:
        proc = PROCESSES.get(job_id)
    if not proc:
        return jsonify({"error": "The process is starting. Wait a moment and try again."}), 409
    try:
        os.killpg(proc.pid, signal.SIGSTOP)
        with LOCK:
            job = jobs[job_id]
            job["paused_from"] = job.get("status", "downloading")
            job["status"] = "paused"
            job["updated"] = time.time()
            save_jobs_locked()
        return jsonify({"ok": True})
    except Exception:
        return jsonify({"error": "Pause is not available for this process right now."}), 409


@app.route("/api/jobs/<job_id>/resume", methods=["POST"])
def resume_job(job_id):
    with LOCK:
        job = jobs.get(job_id)
        if not job:
            return jsonify({"error": "Job not found."}), 404
        if job.get("status") != "paused":
            return jsonify({"error": "This job is not paused."}), 409
        paused_from = job.get("paused_from", "queued")
    if paused_from == "queued":
        update_job(job_id, status="queued", error="")
        return jsonify({"ok": True})
    with PROCESS_LOCK:
        proc = PROCESSES.get(job_id)
    if not proc:
        update_job(job_id, status="queued", progress=0, stage_progress=0, speed="", eta="", error="Resuming after a service restart.")
        return jsonify({"ok": True, "requeued": True})
    try:
        os.killpg(proc.pid, signal.SIGCONT)
        update_job(job_id, status=paused_from, error="")
        return jsonify({"ok": True})
    except Exception:
        return jsonify({"error": "Could not resume this process. Retry the job."}), 409


@app.route("/api/jobs/<job_id>/cancel", methods=["POST"])
def cancel_job(job_id):
    with LOCK:
        job = jobs.get(job_id)
        if not job:
            return jsonify({"error": "Job not found."}), 404
        job["cancel_requested"] = True
        status = job.get("status")
        if status in ("queued", "paused") and job_id not in RUNNING_IDS:
            job["status"] = "cancelled"
            job["error"] = "Cancelled"
            job["updated"] = time.time()
            save_jobs_locked()
            return jsonify({"ok": True})
    with PROCESS_LOCK:
        proc = PROCESSES.get(job_id)
    if proc:
        try:
            os.killpg(proc.pid, signal.SIGCONT)
        except Exception:
            pass
        try:
            os.killpg(proc.pid, signal.SIGTERM)
        except Exception:
            pass
    return jsonify({"ok": True})


@app.route("/api/jobs/<job_id>/retry", methods=["POST"])
def retry_job(job_id):
    with LOCK:
        job = jobs.get(job_id)
        if not job:
            return jsonify({"error": "Job not found."}), 404
        if job.get("status") not in ("failed", "cancelled"):
            return jsonify({"error": "Only failed or cancelled jobs can be retried."}), 409
        job["status"] = "queued"
        job["progress"] = 0
        job["stage_progress"] = 0
        job["speed"] = ""
        job["eta"] = ""
        job["error"] = ""
        job["cancel_requested"] = False
        job["source_size"] = None
        job["downloaded_bytes"] = None
        job["final_size"] = None
        job["saved_percent"] = None
        job["file"] = ""
        job["file_path"] = ""
        job["updated"] = time.time()
        save_jobs_locked()
        result = public_job(job)
    return jsonify({"ok": True, "job": result})


@app.route("/api/jobs/<job_id>", methods=["DELETE"])
def delete_job(job_id):
    with LOCK:
        job = jobs.get(job_id)
        if not job:
            return jsonify({"error": "Job not found."}), 404
        if job.get("status") in ("queued", "starting", "downloading", "processing", "paused"):
            return jsonify({"error": "Cancel active jobs before deleting them."}), 409
        file_path = job.get("file_path")
        del jobs[job_id]
        save_jobs_locked()
    if file_path:
        try:
            Path(file_path).unlink(missing_ok=True)
        except Exception:
            pass
    return jsonify({"ok": True})


@app.route("/download/<job_id>")
def download_job(job_id):
    with LOCK:
        job = jobs.get(job_id)
        if not job or job.get("status") != "ready":
            return "File not ready yet, or it has already been sent.", 404
        file_path = Path(job.get("file_path", ""))
        folder_name = clean_folder_name(job.get("folder_name", "Videos"))
    expected_parent = DOWNLOAD_ROOT.joinpath(folder_name).resolve()
    if not file_path.is_file() or file_path.parent.resolve() != expected_parent:
        return "File not found. The server may have restarted or storage may have changed.", 404

    response = send_file(file_path, as_attachment=True, download_name=f"My1080pSaver-{job_id}{file_path.suffix or '.mp4'}")

    # Remove the compressed output once the server finishes the response stream.
    # The server still needs temporary disk space while processing and transferring it.
    def cleanup_after_transfer():
        try:
            if file_path.parent.resolve() == expected_parent:
                file_path.unlink(missing_ok=True)
        except OSError:
            pass
        with LOCK:
            current = jobs.get(job_id)
            if current and current.get("status") == "ready" and current.get("file_path") == str(file_path):
                current["status"] = "downloaded"
                current["file_path"] = ""
                current["file"] = ""
                current["updated"] = time.time()
                save_jobs_locked()

    response.call_on_close(cleanup_after_transfer)
    return response


@app.route("/api/settings", methods=["GET", "POST"])
def api_settings():
    if request.method == "GET":
        with LOCK:
            data = dict(settings)
        data["download_path"] = str(output_dir_for(data["folder_name"]))
        data["auth_enabled"] = bool(APP_PASSWORD)
        data["site_token_configured"] = bool(data.get("videodownloader_token") or os.getenv("VIDEODOWNLOADER_TOKEN", ""))
        data.pop("videodownloader_token", None)
        return jsonify(data)
    data = request.get_json(silent=True) or {}
    with LOCK:
        if "max_concurrent" in data:
            try:
                settings["max_concurrent"] = max(1, min(4, int(data["max_concurrent"])))
            except (TypeError, ValueError):
                return jsonify({"error": "Concurrency must be between 1 and 4."}), 400
        if "folder_name" in data:
            settings["folder_name"] = clean_folder_name(data["folder_name"])
        if "videodownloader_token" in data:
            token = str(data.get("videodownloader_token") or "").strip()[:5000]
            if token:
                settings["videodownloader_token"] = token
            elif data.get("clear_videodownloader_token") is True:
                settings["videodownloader_token"] = ""
        atomic_json_write(SETTINGS_FILE, settings)
        result = dict(settings)
    result["download_path"] = str(output_dir_for(result["folder_name"]))
    result["auth_enabled"] = bool(APP_PASSWORD)
    result["site_token_configured"] = bool(result.get("videodownloader_token") or os.getenv("VIDEODOWNLOADER_TOKEN", ""))
    result.pop("videodownloader_token", None)
    return jsonify(result)


@app.route("/health")
def health():
    return "ok"


load_state()
threading.Thread(target=dispatcher, daemon=True, name="job-dispatcher").start()

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8000))
    app.run(host="0.0.0.0", port=port, threaded=True)

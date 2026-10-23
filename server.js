'use strict';

const http = require('node:http');
const fs = require('node:fs');
const fsp = require('node:fs/promises');
const path = require('node:path');
const os = require('node:os');
const crypto = require('node:crypto');
const dns = require('node:dns/promises');
const net = require('node:net');
const { spawn, execFile } = require('node:child_process');
const { promisify } = require('node:util');
const { pipeline } = require('node:stream/promises');
const { chromium } = require('playwright');
const execFileAsync = promisify(execFile);

const ROOT = __dirname;
const DATA_DIR = path.resolve(process.env.DATA_DIR || path.join(ROOT, 'data'));
const DOWNLOAD_ROOT = path.resolve(process.env.DOWNLOAD_DIR || path.join(ROOT, 'downloads'));
const JOBS_FILE = path.join(DATA_DIR, 'jobs.json');
const SETTINGS_FILE = path.join(DATA_DIR, 'settings.json');
const APP_PASSWORD = (process.env.APP_PASSWORD || '').trim();
const SECRET_KEY = process.env.SECRET_KEY || crypto.randomBytes(32).toString('hex');
const PORT = Number(process.env.PORT || 8000);
const ANIMEPAHE_BASE = (process.env.ANIMEPAHE_BASE_URL || 'https://animepahe.ch').replace(/\/$/, '');
const UA = 'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36';
const MAX_JOBS = 100;
const ACTIVE = new Set(['starting', 'downloading', 'processing']);
const jobs = new Map();
const processes = new Map();
let settings = { max_concurrent: 3, folder_name: 'Videos', videodownloader_token: '' };
let dispatcherRunning = false;
let shuttingDown = false;

fs.mkdirSync(DATA_DIR, { recursive: true });
fs.mkdirSync(DOWNLOAD_ROOT, { recursive: true });

function now() { return Date.now() / 1000; }
function cleanFolderName(value) {
  const s = String(value || 'Videos').replace(/[^A-Za-z0-9 _-]/g, '').slice(0, 48).trim().replace(/^[ ._-]+|[ ._-]+$/g, '');
  return s && s !== '.' && s !== '..' ? s : 'Videos';
}
function outputDir(folderName) {
  const dir = path.resolve(DOWNLOAD_ROOT, cleanFolderName(folderName || settings.folder_name));
  if (path.dirname(dir) !== DOWNLOAD_ROOT) throw new Error('Invalid output directory');
  fs.mkdirSync(dir, { recursive: true });
  return dir;
}
function atomicWrite(file, value) {
  const tmp = `${file}.tmp`;
  fs.writeFileSync(tmp, JSON.stringify(value, null, 2));
  const fd = fs.openSync(tmp, 'r'); fs.fsyncSync(fd); fs.closeSync(fd);
  fs.renameSync(tmp, file);
}
function saveJobs() { atomicWrite(JOBS_FILE, Object.fromEntries(jobs)); }
function saveSettings() { atomicWrite(SETTINGS_FILE, settings); }
function publicJob(job) {
  const out = { ...job };
  for (const k of ['url', 'source_file', 'cancel_requested', 'paused_from', 'anime_meta', 'quality_url', 'episode_url', 'download_url', 'download_headers']) delete out[k];
  return out;
}
function updateJob(id, changes) {
  const j = jobs.get(id); if (!j) return;
  Object.assign(j, changes, { updated: now() });
  saveJobs();
}
function safeLabel(raw) {
  try { const u = new URL(raw); const tail = decodeURIComponent(u.pathname.split('/').filter(Boolean).pop() || '').replace(/[_-]+/g, ' '); return (tail.length > 2 ? tail : u.hostname).slice(0, 100); }
  catch { return 'Video download'; }
}
function parseSize(s) {
  const m = String(s || '').trim().match(/^([\d.]+)\s*([KMGT]?i?B)$/i); if (!m) return null;
  const unit = m[2].toUpperCase(); const factor = { B: 1, KB: 1e3, MB: 1e6, GB: 1e9, TB: 1e12, KIB: 1024, MIB: 1024**2, GIB: 1024**3, TIB: 1024**4 }[unit] || 1;
  return Math.round(Number(m[1]) * factor);
}
function fmtDuration(sec) {
  if (!Number.isFinite(sec) || sec < 0) return '';
  sec = Math.ceil(sec); const h = Math.floor(sec / 3600), m = Math.floor((sec % 3600) / 60), s = sec % 60;
  return h ? `${h}:${String(m).padStart(2,'0')}:${String(s).padStart(2,'0')}` : `${m}:${String(s).padStart(2,'0')}`;
}
function hmac(value) { return crypto.createHmac('sha256', SECRET_KEY).update(value).digest('hex'); }
function makeSession() { const v = `${Date.now()}.${crypto.randomBytes(18).toString('hex')}`; return `${v}.${hmac(v)}`; }
function validSession(req) {
  const cookie = (req.headers.cookie || '').split(';').map(s => s.trim()).find(s => s.startsWith('m1080_session='));
  if (!cookie) return false;
  const token = decodeURIComponent(cookie.slice('m1080_session='.length)); const parts = token.split('.');
  if (parts.length !== 3) return false; const v = `${parts[0]}.${parts[1]}`;
  const expected = hmac(v); if (parts[2].length !== expected.length) return false; return crypto.timingSafeEqual(Buffer.from(parts[2]), Buffer.from(expected)) && Date.now() - Number(parts[0]) < 7 * 86400000;
}
function sendJson(res, status, value) { const body = JSON.stringify(value); res.writeHead(status, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store' }); res.end(body); }
function sendText(res, status, value, type = 'text/plain; charset=utf-8') { res.writeHead(status, { 'Content-Type': type, 'Cache-Control': 'no-store' }); res.end(value); }
async function readBody(req, limit = 1024 * 1024) {
  const chunks = []; let size = 0;
  for await (const c of req) { size += c.length; if (size > limit) throw new Error('Request body too large.'); chunks.push(c); }
  const raw = Buffer.concat(chunks).toString('utf8');
  if ((req.headers['content-type'] || '').includes('application/x-www-form-urlencoded')) return Object.fromEntries(new URLSearchParams(raw));
  if (!raw) return {};
  try { return JSON.parse(raw); } catch { throw new Error('Invalid JSON request.'); }
}
function sendError(res, status, error) { sendJson(res, status, { error: String(error || 'Request failed').slice(0, 500) }); }

async function validatePublicUrl(raw) {
  let u; try { u = new URL(String(raw || '').trim()); } catch { return 'Enter a valid full URL.'; }
  if (!['http:', 'https:'].includes(u.protocol) || !u.hostname) return 'Use a full http:// or https:// URL.';
  if (u.username || u.password) return 'URLs containing embedded credentials are not accepted.';
  const host = u.hostname.toLowerCase().replace(/\.$/, '');
  if (host === 'localhost' || host.endsWith('.localhost') || host.endsWith('.local')) return 'Local and private network addresses are not allowed.';
  if (net.isIP(host)) {
    if (isPrivateIp(host)) return 'Private or local IP addresses are not allowed.';
  } else {
    try { const addresses = await dns.lookup(host, { all: true, verbatim: true }); if (!addresses.length || addresses.some(a => isPrivateIp(a.address))) return 'The URL resolves to a private or local network address.'; }
    catch { return 'The URL host could not be resolved.'; }
  }
  return '';
}
function isPrivateIp(ip) {
  if (ip.includes(':')) return ip === '::1' || ip.startsWith('fc') || ip.startsWith('fd') || ip.startsWith('fe80:') || ip === '::';
  const a = ip.split('.').map(Number); return a[0] === 10 || a[0] === 127 || (a[0] === 169 && a[1] === 254) || (a[0] === 172 && a[1] >= 16 && a[1] <= 31) || (a[0] === 192 && a[1] === 168) || a[0] === 0 || a[0] >= 224;
}

async function runCapture(cmd, args, opts = {}) {
  const { stdout = '', stderr = '' } = await execFileAsync(cmd, args, { maxBuffer: 24 * 1024 * 1024, timeout: opts.timeout || 90000, windowsHide: true });
  return { stdout, stderr };
}
function spawnProcess(id, cmd, args, onLine, opts = {}) {
  return new Promise((resolve, reject) => {
    const child = spawn(cmd, args, { cwd: opts.cwd || ROOT, detached: process.platform !== 'win32', stdio: ['ignore', 'pipe', 'pipe'], windowsHide: true });
    processes.set(id, child);
    let buffer = '', errBuffer = '', lastError = '';
    const consume = (chunk, isErr) => {
      const s = chunk.toString('utf8');
      if (isErr) errBuffer += s; else buffer += s;
      const source = isErr ? errBuffer : buffer;
      const lines = source.split(/\r?\n/);
      if (isErr) errBuffer = lines.pop() || ''; else buffer = lines.pop() || '';
      for (const line of lines) { if (line) { if (/ERROR:|Conversion failed|Error while/i.test(line)) lastError = line.slice(-700); try { onLine(line); } catch {} } }
    };
    child.stdout.on('data', c => consume(c, false)); child.stderr.on('data', c => consume(c, true));
    child.on('error', e => { processes.delete(id); reject(e); });
    child.on('close', (code, signal) => {
      processes.delete(id);
      if (buffer.trim()) { try { onLine(buffer.trim()); } catch {} }
      if (errBuffer.trim()) { try { onLine(errBuffer.trim()); } catch {} }
      resolve({ code: code ?? 1, signal, error: lastError });
    });
  });
}
function isCancelled(id) { return !!jobs.get(id)?.cancel_requested; }
function sourceFiles(folder, id) {
  return fs.readdirSync(folder).filter(n => n.startsWith(`${id}_source.`) && !/\.(part|ytdl|json)$/i.test(n)).map(n => path.join(folder, n)).filter(p => { try { return fs.statSync(p).isFile() && fs.statSync(p).size > 0; } catch { return false; } });
}
async function downloadYtDlp(id, job, folder) {
  const template = path.join(folder, `${id}_source.%(ext)s`);
  const selected = String(job.format_id || '').trim();
  let fmt = 'bestvideo*[height<=1080]+bestaudio/best[height<=1080]/best';
  const hm = selected.match(/^height:(\d{2,4})$/); if (hm) { const h = Number(hm[1]); fmt = `bestvideo[height=${h}]+bestaudio/best[height=${h}]/best[height<=${h}]/best`; }
  else if (selected && /^[\w.,+\-/]+$/.test(selected)) fmt = selected;
  const args = ['--newline','--no-warnings','--no-playlist','--js-runtimes','node','--continue','--retries','5','--fragment-retries','5','--retry-sleep','http:2','--retry-sleep','fragment:2','--socket-timeout','45','--progress-template','download:__DL__%(progress._percent_str)s|%(progress._downloaded_bytes_str)s|%(progress._total_bytes_str)s|%(progress._speed_str)s|%(progress._eta_str)s','-f',fmt,'--merge-output-format','mkv','-o',template,job.url];
  updateJob(id, { status: 'downloading', stage: 'Downloading', progress: 0, stage_progress: 0, speed: '', eta: '', error: '' });
  const started = now();
  const result = await spawnProcess(id, 'yt-dlp', args, line => {
    if (line.startsWith('__DL__')) {
      const parts = line.slice(6).split('|'); const pct = Number(String(parts[0] || '').replace('%','').trim());
      const downloaded = parseSize(parts[1]); const total = parseSize(parts[2]); const speed = String(parts[3] || '').trim(); const eta = String(parts[4] || '').trim();
      const changes = { status: 'downloading', stage: 'Downloading', updated: now() };
      if (Number.isFinite(pct)) { changes.stage_progress = Math.max(0, Math.min(100, pct)); changes.progress = Math.round(Math.max(0, Math.min(100, pct)) * 0.82); }
      if (downloaded !== null) changes.downloaded_bytes = downloaded; if (total !== null) changes.source_size = total;
      if (speed && speed !== 'NA') changes.speed = speed; if (eta && eta !== 'NA') changes.eta = eta;
      updateJob(id, changes);
    } else if (/ERROR:|Unable to|403 Forbidden|404 Not Found/i.test(line)) updateJob(id, { error: line.slice(-450) });
  });
  if (isCancelled(id)) return { cancelled: true };
  if (result.code !== 0) throw new Error((jobs.get(id)?.error || result.error || 'Download failed. The source may be unavailable or unsupported.').slice(0, 500));
  const files = sourceFiles(folder, id).sort((a,b) => fs.statSync(b).size - fs.statSync(a).size);
  if (!files.length) throw new Error('Downloader finished without producing a valid media file.');
  return { sourcePath: files[0], elapsed: now() - started };
}
async function probeMedia(file) {
  try {
    const { stdout } = await runCapture('ffprobe', ['-v','error','-show_entries','format=duration:stream=codec_type,bit_rate','-of','json',file], { timeout: 20000 });
    const data = JSON.parse(stdout || '{}');
    const duration = Number(data.format && data.format.duration);
    const audioStreams = (data.streams || []).filter(s => s.codec_type === 'audio');
    const knownAudioBitrate = audioStreams.reduce((sum, s) => sum + (Number(s.bit_rate) > 0 ? Number(s.bit_rate) : 0), 0);
    // If a container doesn't report audio bitrates, reserve a conservative 192 kb/s per audio track.
    const audioBitrate = knownAudioBitrate || audioStreams.length * 192000;
    return { duration: Number.isFinite(duration) && duration > 0 ? duration : null, audioBitrate, audioTracks: audioStreams.length };
  } catch { return { duration: null, audioBitrate: 0, audioTracks: 0 }; }
}
async function compressFile(id, sourcePath, folder) {
  const sourceSize = fs.statSync(sourcePath).size;
  const candidate = path.join(folder, `${id}_compressed.mkv`);
  const passlog = path.join(folder, `${id}_ffmpeg_pass`);
  const media = await probeMedia(sourcePath);
  const duration = media.duration;
  if (!duration) throw new Error('Cannot calculate the 55% compression target because FFprobe could not read the video duration. The original download is preserved.');

  // 55% size reduction means targeting an output around 45% of the source size.
  // Keep the source dimensions and copy the original audio/subtitle tracks.
  const targetTotalBitrate = (sourceSize * 8 * 0.45 / duration) * 0.985;
  const targetVideoBitrate = Math.floor((targetTotalBitrate - media.audioBitrate) / 1000);
  if (targetVideoBitrate < 100) {
    throw new Error('A 55% size reduction is not realistic for this file while copying its audio tracks at their original bitrate. The original download is preserved.');
  }
  updateJob(id, { status: 'processing', stage: 'Compressing video (55% size-reduction target)', progress: 82, stage_progress: 0, source_file: sourcePath, source_size: sourceSize, compression_started: now(), compression_duration: duration, target_saved_percent: 55, target_size: Math.round(sourceSize * 0.45), target_video_bitrate_kbps: targetVideoBitrate, speed: '', eta: 'Calculating…', error: '' });

  let lastCurrent = 0;
  const handleProgress = (line, pass) => {
    if (!line.includes('=')) return;
    const [key, ...rest] = line.split('='); const value = rest.join('=').trim();
    if (key === 'speed' && value && value !== 'N/A') updateJob(id, { speed: value });
    if ((key === 'out_time_ms' || key === 'out_time_us') && duration) {
      const current = Math.max(0, Number(value) / 1000000); lastCurrent = current;
      const pct = Math.max(0, Math.min(100, current / duration * 100));
      const speedText = String(jobs.get(id)?.speed || '').match(/([\d.]+)x/); const speed = speedText ? Number(speedText[1]) : 0;
      const passPct = pass === 1 ? pct * 0.5 : 50 + pct * 0.5;
      // ETA includes the uncompleted portion of this pass and, during pass one, the expected second pass.
      const remainingVideoSeconds = pass === 1 ? (duration - current) + duration : duration - current;
      const eta = speed > 0 ? fmtDuration(remainingVideoSeconds / speed) : '';
      updateJob(id, { status: 'processing', stage: `Compressing video — pass ${pass}/2`, stage_progress: Math.round(passPct * 10) / 10, progress: Math.round(82 + passPct * 0.18), eta: eta || 'Calculating…', compression_elapsed: Math.round(now() - Number(jobs.get(id)?.compression_started || now())) });
    }
  };
  const common = ['-hide_banner','-loglevel','error','-y','-i',sourcePath,'-map','0:v:0','-c:v','libx265','-preset','medium','-b:v',`${targetVideoBitrate}k`,'-x265-params','log-level=error','-passlogfile',passlog];
  // First pass measures how to allocate bits; second pass targets about 45% of original total size.
  const pass1Args = [...common,'-pass','1','-an','-sn','-dn','-f','null','-progress','pipe:1','-nostats','-'];
  const pass1 = await spawnProcess(id, 'ffmpeg', pass1Args, line => handleProgress(line, 1));
  if (isCancelled(id)) { try { fs.unlinkSync(candidate); } catch {} return { cancelled: true }; }
  if (pass1.code !== 0) { cleanupPassLogs(passlog); throw new Error((pass1.error || 'FFmpeg first compression pass failed.').slice(0, 500)); }

  const pass2Args = [...common,'-pass','2','-map','0:a?','-map','0:s?','-map_metadata','0','-map_chapters','0','-c:a','copy','-c:s','copy','-max_muxing_queue_size','2048','-progress','pipe:1','-nostats',candidate];
  const pass2 = await spawnProcess(id, 'ffmpeg', pass2Args, line => handleProgress(line, 2));
  cleanupPassLogs(passlog);
  if (isCancelled(id)) { try { fs.unlinkSync(candidate); } catch {} return { cancelled: true }; }
  if (pass2.code !== 0 || !fs.existsSync(candidate) || fs.statSync(candidate).size === 0) { try { fs.unlinkSync(candidate); } catch {} throw new Error((pass2.error || 'FFmpeg could not finish the 55% compression target. The original download is preserved.').slice(0, 500)); }

  const compressedSize = fs.statSync(candidate).size;
  const savedPercent = (sourceSize - compressedSize) / sourceSize * 100;
  if (compressedSize >= sourceSize) {
    try { fs.unlinkSync(candidate); } catch {}
    return { finalPath: sourcePath, finalSize: sourceSize, sourceSize, savedPercent: 0, stage: 'Original kept — compression was not smaller', note: 'The 55% target could not be reached without making the file larger; original retained.' };
  }
  try { if (sourcePath !== candidate) fs.unlinkSync(sourcePath); } catch {}
  const note = savedPercent >= 52 && savedPercent <= 58
    ? `Target achieved: ${savedPercent.toFixed(1)}% smaller than the original.`
    : `Target was 55%; actual reduction was ${savedPercent.toFixed(1)}% because audio/subtitle tracks and encoding constraints affect the final size.`;
  return { finalPath: candidate, finalSize: compressedSize, sourceSize, savedPercent, stage: 'Compressed', note };
}
function cleanupPassLogs(prefix) {
  for (const suffix of ['', '.log', '.log.mbtree', '-0.log', '-0.log.mbtree']) {
    try { fs.unlinkSync(prefix + suffix); } catch {}
  }
}

function animeHostAllowed(host) {
  host = String(host || '').toLowerCase();
  return host === 'animepahe.ch' || host.endsWith('.animepahe.ch') || ['animepahe.com','animepahe.si','animepahe.ru','animepahe.pw','animepahe.org'].includes(host);
}
function validAnimeUrl(raw) {
  try { const u = new URL(raw); return u.protocol === 'https:' && (animeHostAllowed(u.hostname) || /^kwik\.(cx|si|to|la|li|pe)$/.test(u.hostname.toLowerCase()) || /^([a-z0-9-]+\.)?kwik\.(cx|si|to|la|li|pe)$/.test(u.hostname.toLowerCase())); } catch { return false; }
}
async function animeRequest(url, referer = `${ANIMEPAHE_BASE}/`) {
  const response = await fetch(url, { headers: { 'User-Agent': UA, 'Referer': referer, 'Accept': 'application/json, text/html;q=0.9, */*;q=0.8' }, signal: AbortSignal.timeout(25000), redirect: 'follow' });
  if (!response.ok) throw new Error(`Anime source returned HTTP ${response.status}.`);
  return response;
}
async function animeJson(url, referer) {
  let directError = null;
  try {
    const response = await animeRequest(url, referer); const text = await response.text();
    try { return JSON.parse(text); } catch { directError = new Error('The API response was not JSON.'); }
  } catch (e) { directError = e; }
  // Retry the same first-party API call in an ordinary browser context so normal site cookies/redirects can be used.
  // This does not disable challenges or bypass access controls.
  try {
    const target = new URL(url); const base = new URL(ANIMEPAHE_BASE);
    if (target.origin !== base.origin) throw directError || new Error('Cross-origin API fallback is not allowed.');
    const browser = await chromium.launch({ headless: true, args: ['--no-sandbox','--disable-dev-shm-usage'] });
    try {
      const page = await browser.newPage({ userAgent: UA });
      await page.goto(referer || `${ANIMEPAHE_BASE}/`, { waitUntil: 'domcontentloaded', timeout: 45000 });
      const effectiveOrigin = new URL(page.url()).origin;
      const effectiveHost = new URL(effectiveOrigin).hostname;
      const requestUrl = animeHostAllowed(effectiveHost) ? new URL(target.pathname + target.search, effectiveOrigin).href : url;
      const result = await page.evaluate(async (targetUrl) => {
        const r = await fetch(targetUrl, { credentials: 'include', headers: { Accept: 'application/json, text/plain, */*' } });
        return { status: r.status, text: await r.text() };
      }, requestUrl);
      if (result.status < 200 || result.status >= 300) throw new Error(`Anime source returned HTTP ${result.status}.`);
      try { return JSON.parse(result.text); } catch { throw new Error('The anime source did not return JSON. Its API may have changed.'); }
    } finally { await browser.close(); }
  } catch (fallbackError) {
    throw new Error((fallbackError && fallbackError.message) || (directError && directError.message) || 'The anime source could not be reached.');
  }
}
async function animePageInfo(session) {
  const browser = await chromium.launch({ headless: true, args: ['--no-sandbox','--disable-dev-shm-usage'] });
  try {
    const page = await browser.newPage({ userAgent: UA });
    await page.goto(`${ANIMEPAHE_BASE}/anime/${encodeURIComponent(session)}`, { waitUntil: 'domcontentloaded', timeout: 45000 });
    await page.waitForTimeout(700);
    return await page.evaluate(() => {
      const txt = s => document.querySelector(s)?.content || document.querySelector(s)?.textContent?.trim() || '';
      const title = document.querySelector('h1')?.textContent?.trim() || txt('meta[property="og:title"]');
      const synopsis = document.querySelector('.anime-summary, .summary, .anime-desc, .description, [itemprop="description"]')?.textContent?.trim() || txt('meta[property="og:description"]') || txt('meta[name="description"]');
      const poster = txt('meta[property="og:image"]') || document.querySelector('.anime-poster img, .poster img')?.src || '';
      const genres = Array.from(document.querySelectorAll('.anime-genre a, .genre a, a[href*="/genre/"]')).map(x=>x.textContent.trim()).filter(Boolean).slice(0,20);
      const text = document.body?.innerText || '';
      const year = (text.match(/(?:Year|Aired|Release)\s*:?\s*(20\d{2}|19\d{2})/i)||[])[1] || '';
      const type = (text.match(/\b(TV|Movie|OVA|ONA|Special)\b/)||[])[1] || '';
      const status = (text.match(/Status\s*:?\s*(Currently Airing|Finished Airing|Not yet aired)/i)||[])[1] || '';
      return { title, synopsis, poster, genres, year, type, status };
    });
  } finally { await browser.close(); }
}
async function animeSearch(q) {
  const url = `${ANIMEPAHE_BASE}/api?m=search&q=${encodeURIComponent(q)}`;
  const data = await animeJson(url);
  const items = Array.isArray(data.data) ? data.data : Array.isArray(data.results) ? data.results : [];
  return items.slice(0, 40).map(a => ({
    title: String(a.title || a.name || 'Untitled anime'), image: a.poster || a.image || '',
    subject_id: String(a.id ?? a.anime_id ?? ''), detail_path: String(a.session || a.slug || ''),
    description: a.synopsis || a.description || [a.type, a.year].filter(Boolean).join(' · '),
    year: a.year || '', type: a.type || '', session: String(a.session || ''), url: a.session ? `${ANIMEPAHE_BASE}/anime/${a.session}` : ''
  }));
}
async function animeEpisodes(session, numericId) {
  let id = String(numericId || '').trim();
  if (!/^\d+$/.test(id)) {
    const browser = await chromium.launch({ headless: true, args: ['--no-sandbox','--disable-dev-shm-usage'] });
    try { const page = await browser.newPage({ userAgent: UA }); await page.goto(`${ANIMEPAHE_BASE}/anime/${encodeURIComponent(session)}`, { waitUntil: 'domcontentloaded', timeout: 45000 });
      id = await page.evaluate(() => { const m = document.querySelector('meta[property="og:url"]')?.content || location.href; const parts = new URL(m).pathname.split('/').filter(Boolean); return parts.at(-1)?.match(/^\d+$/) ? parts.at(-1) : (document.querySelector('[data-id]')?.getAttribute('data-id') || ''); });
    } finally { await browser.close(); }
  }
  if (!/^\d+$/.test(id)) throw new Error('Could not identify this anime release ID from the source.');
  const all = []; let lastPage = 1;
  for (let page = 1; page <= Math.min(100, Math.max(1, lastPage)); page++) {
    const url = `${ANIMEPAHE_BASE}/api?m=release&id=${encodeURIComponent(id)}&sort=episode_asc&page=${page}`;
    const data = await animeJson(url, `${ANIMEPAHE_BASE}/anime/${session}`);
    const rows = Array.isArray(data.data) ? data.data : [];
    all.push(...rows); lastPage = Number(data.last_page || 1);
    if (page >= lastPage || rows.length === 0) break;
  }
  return all.map((ep, i) => ({ episode: Number(ep.episode || ep.number || i+1), season: 1, title: ep.title || `Episode ${ep.episode || i+1}`, session: String(ep.session || ''), snapshot: ep.snapshot || '', anime_id: String(ep.anime_id || id), url: `${ANIMEPAHE_BASE}/play/${session}/${ep.session}` })).filter(e => e.session).sort((a,b)=>a.episode-b.episode);
}
async function animeQualities(episodeUrl) {
  if (!validAnimeUrl(episodeUrl)) throw new Error('Unsupported anime episode URL.');
  const browser = await chromium.launch({ headless: true, args: ['--no-sandbox','--disable-dev-shm-usage'] });
  try {
    const page = await browser.newPage({ userAgent: UA });
    await page.goto(episodeUrl, { waitUntil: 'domcontentloaded', timeout: 60000 });
    await page.waitForSelector('#pickDownload a.dropdown-item, #downloadMenu a, a[data-src]', { timeout: 25000 }).catch(()=>{});
    const list = await page.evaluate(() => {
      const anchors = Array.from(document.querySelectorAll('#pickDownload a.dropdown-item, #downloadMenu a, a[data-src]'));
      return anchors.map(a => ({ label: (a.innerText || a.textContent || a.getAttribute('title') || '').trim(), url: a.getAttribute('data-src') || a.href || '', audio: a.getAttribute('data-audio') || '', resolution: a.getAttribute('data-resolution') || '' })).filter(x => x.url && /^https?:/i.test(x.url));
    });
    const unique = new Map();
    for (const q of list) { if (!validAnimeUrl(q.url)) continue; const label = q.label || `${q.resolution || 'Available'} ${q.audio}`.trim(); const key = `${label}|${q.url}`; if (!unique.has(key)) unique.set(key, { label, url: q.url, audio: q.audio, resolution: q.resolution }); }
    const qualities = [...unique.values()];
    if (!qualities.length) throw new Error('No download resolutions were exposed for this episode. The source may be unavailable or its page layout may have changed.');
    return qualities;
  } finally { await browser.close(); }
}
async function resolveAnimeDownload(episodeUrl, qualityUrl) {
  if (!validAnimeUrl(episodeUrl) || !validAnimeUrl(qualityUrl)) throw new Error('The selected episode or resolution URL is not supported.');
  const browser = await chromium.launch({ headless: true, args: ['--no-sandbox','--disable-dev-shm-usage'] });
  try {
    const context = await browser.newContext({ userAgent: UA }); const page = await context.newPage();
    await page.goto(episodeUrl, { waitUntil: 'domcontentloaded', timeout: 60000 });
    await page.goto(qualityUrl, { waitUntil: 'domcontentloaded', timeout: 60000 });
    const redirectLink = await page.locator('a.redirect').filter({ hasText: /continue/i }).first().getAttribute('href').catch(()=>null);
    if (redirectLink) await page.goto(new URL(redirectLink, page.url()).href, { waitUntil: 'domcontentloaded', timeout: 60000 });
    await page.waitForSelector('form:has(button), form:has(input[name="_token"])', { timeout: 25000 });
    const form = page.locator('form').filter({ has: page.locator('input[name="_token"]') }).first();
    const action = await form.getAttribute('action'); const token = await form.locator('input[name="_token"]').getAttribute('value');
    const title = (await page.locator('h1.title, h1').first().textContent().catch(()=>''))?.trim() || 'Anime episode';
    if (!action || !token) throw new Error('The source did not provide a valid download form.');
    const cookies = await context.cookies();
    const referer = page.url(); const postUrl = new URL(action, referer).href;
    if (!validAnimeUrl(postUrl)) throw new Error('The source returned an unsupported download host.');
    return { post_url: postUrl, token, title: title.slice(0,160), cookies, referer, episode_url: episodeUrl, quality_url: qualityUrl };
  } finally { await browser.close(); }
}
function cookieHeader(cookies, targetHost = '') { const host=String(targetHost||'').toLowerCase(); return (cookies || []).filter(c => { const d=String(c.domain||'').replace(/^\./,'').toLowerCase(); return !host || host===d || host.endsWith('.'+d); }).map(c => `${c.name}=${c.value}`).join('; '); }
function dispositionName(value) { const m = String(value || '').match(/filename\*?=(?:UTF-8''|\")?([^;\"]+)/i); if (!m) return ''; try { return decodeURIComponent(m[1].replace(/^"|"$/g,'')); } catch { return m[1]; } }
async function streamAnimeSource(id, job, folder) {
  const partPath = path.join(folder, `${id}_source.part`);
  let offset = 0;
  try { offset = fs.statSync(partPath).size; } catch {}
  if (offset > 0 && !job.download_url) offset = 0;
  let response;
  // Resume only when a previous request revealed a stable direct URL; otherwise refresh the one-time source form.
  if (offset > 0 && job.download_url) {
    const headers = { ...(job.download_headers || {}), Range: `bytes=${offset}-`, 'User-Agent': UA };
    response = await fetch(job.download_url, { headers, redirect: 'follow', signal: AbortSignal.timeout(120000) });
    if (response.status !== 206) { try { fs.unlinkSync(partPath); } catch {} offset = 0; response.body?.cancel().catch(()=>{}); response = null; }
  }
  if (!response || offset === 0) {
    const meta = await resolveAnimeDownload(job.episode_url, job.quality_url);
    const headers = { 'User-Agent': UA, 'Referer': meta.referer, 'Origin': new URL(meta.referer).origin, 'Cookie': cookieHeader(meta.cookies, new URL(meta.post_url).hostname), 'Content-Type': 'application/x-www-form-urlencoded', 'Accept': '*/*' };
    response = await fetch(meta.post_url, { method: 'POST', headers, body: new URLSearchParams({ _token: meta.token }), redirect: 'follow', signal: AbortSignal.timeout(120000) });
    if (!response.ok) throw new Error(`Anime source download returned HTTP ${response.status}.`);
    const type = (response.headers.get('content-type') || '').toLowerCase();
    if (type.includes('text/html') || type.includes('application/json')) throw new Error('The anime source returned a web page instead of a video file. The download link may have expired. Retry the job.');
    job.download_url = response.url;
    job.download_headers = { 'Referer': meta.referer, 'Cookie': cookieHeader(meta.cookies, new URL(meta.post_url).hostname) };
    job.source_file = partPath; updateJob(id, { download_url: job.download_url, download_headers: job.download_headers, source_file: partPath, status: 'downloading', stage: 'Downloading Anime episode' });
  }
  if (!response.ok && response.status !== 206) throw new Error(`Anime source download returned HTTP ${response.status}.`);
  const total = Number(response.headers.get('content-length') || 0) + offset;
  const disposition = dispositionName(response.headers.get('content-disposition'));
  const extMatch = (disposition || response.url || '').match(/\.(mp4|mkv|webm|m4v|mov|ts)(?:[?#]|$)/i);
  const ext = extMatch ? `.${extMatch[1].toLowerCase()}` : '.mp4';
  const write = fs.createWriteStream(partPath, { flags: offset && response.status === 206 ? 'a' : 'w' });
  let received = offset; const totalExpected = total; let lastProgressAt = 0; let lastProgressPct = -1;
  const body = response.body;
  if (!body) throw new Error('The source response had no video data.');
  const reader = body.getReader();
  try {
    while (true) {
      if (isCancelled(id)) { await reader.cancel().catch(()=>{}); write.destroy(); return { cancelled: true }; }
      const { done, value } = await reader.read(); if (done) break;
      received += value.byteLength;
      if (!write.write(Buffer.from(value))) await new Promise(resolve => write.once('drain', resolve));
      const pct = totalExpected > 0 ? Math.min(100, received / totalExpected * 100) : 0;
      const stamp = Date.now();
      if (stamp - lastProgressAt >= 1000 || pct - lastProgressPct >= 1 || (totalExpected > 0 && received >= totalExpected)) {
        updateJob(id, { status: 'downloading', progress: Math.round(pct * 0.82), stage_progress: Math.round(pct * 10)/10, downloaded_bytes: received, source_size: totalExpected || undefined, speed: '', eta: '', stage: 'Downloading Anime episode' });
        lastProgressAt = stamp; lastProgressPct = pct;
      }
    }
  } finally { write.end(); await new Promise(resolve => write.closed ? resolve() : write.once('close', resolve)).catch(()=>{}); }
  if (!fs.existsSync(partPath) || fs.statSync(partPath).size < 1024) throw new Error('Anime source returned an empty or invalid file.');
  const sourcePath = path.join(folder, `${id}_source${ext}`); fs.renameSync(partPath, sourcePath);
  return { sourcePath };
}
async function runJob(id) {
  const job = jobs.get(id); if (!job || isCancelled(id)) { if (job) updateJob(id, { status: 'cancelled', error: 'Cancelled' }); return; }
  const folder = outputDir(job.folder_name); updateJob(id, { status: 'starting', progress: 0, stage_progress: 0, error: '', eta: '', speed: '' });
  try {
    let sourcePath;
    if (job.source === 'Anime episode' && job.episode_url && job.quality_url) {
      updateJob(id, { status: 'downloading', stage: 'Resolving anime source', progress: 0 });
      const r = await streamAnimeSource(id, job, folder); if (r.cancelled) { updateJob(id, { status: 'cancelled', error: 'Cancelled' }); return; } sourcePath = r.sourcePath;
    } else {
      const r = await downloadYtDlp(id, job, folder); if (r.cancelled) { updateJob(id, { status: 'cancelled', error: 'Cancelled' }); return; } sourcePath = r.sourcePath;
    }
    if (isCancelled(id)) { updateJob(id, { status: 'cancelled', error: 'Cancelled' }); return; }
    const sourceSize = fs.statSync(sourcePath).size;
    if (job.download_mode === 'original') {
      const finalPath = sourcePath; updateJob(id, { status: 'ready', progress: 100, stage_progress: 100, speed: '', eta: '', file: path.basename(finalPath), file_path: finalPath, source_size: sourceSize, final_size: sourceSize, saved_percent: 0, stage: 'Original quality', compression_note: 'Compression skipped; original downloaded file retained.', error: '' }); return;
    }
    const c = await compressFile(id, sourcePath, folder); if (c.cancelled) { updateJob(id, { status: 'cancelled', error: 'Cancelled' }); return; }
    updateJob(id, { status: 'ready', progress: 100, stage_progress: 100, speed: '', eta: '0:00', file: path.basename(c.finalPath), file_path: c.finalPath, source_size: c.sourceSize, final_size: c.finalSize, saved_percent: Math.round(c.savedPercent*10)/10, stage: c.stage, compression_note: c.note || '', error: '' });
  } catch (e) {
    if (isCancelled(id)) updateJob(id, { status: 'cancelled', error: 'Cancelled', speed: '', eta: '' });
    else updateJob(id, { status: 'failed', error: String(e.message || 'Job failed').slice(0,500), speed: '', eta: '' });
  } finally { processes.delete(id); }
}
async function dispatcher() {
  if (dispatcherRunning || shuttingDown) return; dispatcherRunning = true;
  try {
    while (!shuttingDown) {
      const active = [...jobs.values()].filter(j => ACTIVE.has(j.status)).length;
      const max = Math.max(1, Math.min(4, Number(settings.max_concurrent) || 3));
      if (active < max) {
        const next = [...jobs.values()].filter(j => j.status === 'queued' && !j.cancel_requested).sort((a,b)=>a.created-b.created)[0];
        if (next) { runJob(next.id); await new Promise(r=>setTimeout(r,150)); continue; }
      }
      await new Promise(r=>setTimeout(r,800));
    }
  } finally { dispatcherRunning = false; }
}

async function loadState() {
  try { const data = JSON.parse(await fsp.readFile(JOBS_FILE,'utf8')); for (const [id,j] of Object.entries(data)) jobs.set(id,j); } catch {}
  try { settings = { ...settings, ...JSON.parse(await fsp.readFile(SETTINGS_FILE,'utf8')) }; } catch {}
  settings.max_concurrent = Math.max(1, Math.min(4, Number(settings.max_concurrent) || 3)); settings.folder_name = cleanFolderName(settings.folder_name);
  let changed = false;
  for (const job of jobs.values()) if (ACTIVE.has(job.status)) { job.status='queued'; job.error='Recovered after a service restart. Download resumes where the source supports it.'; job.updated=now(); job.speed=''; job.eta=''; changed=true; }
  if (changed) saveJobs(); saveSettings();
}

async function handleApi(req, res, url) {
  const method = req.method; const pathname = url.pathname;
  if (pathname === '/api/health' && method === 'GET') return sendJson(res, 200, { online: true, service: 'MY 1080p SAVER', timestamp: now(), active_jobs: [...jobs.values()].filter(j=>ACTIVE.has(j.status)).length });
  if (pathname === '/api/jobs' && method === 'GET') return sendJson(res, 200, { jobs: [...jobs.values()].map(publicJob).sort((a,b)=>b.created-a.created) });
  if (pathname === '/api/settings' && method === 'GET') return sendJson(res, 200, { max_concurrent: settings.max_concurrent, folder_name: settings.folder_name, download_path: outputDir(settings.folder_name), auth_enabled: !!APP_PASSWORD, site_token_configured: !!(settings.videodownloader_token || process.env.VIDEODOWNLOADER_TOKEN) });
  if (pathname === '/api/settings' && method === 'POST') {
    const d = await readBody(req);
    if (d.max_concurrent !== undefined) { const n=Number(d.max_concurrent); if (!Number.isInteger(n)||n<1||n>4) return sendError(res,400,'Concurrency must be between 1 and 4.'); settings.max_concurrent=n; }
    if (d.folder_name !== undefined) settings.folder_name=cleanFolderName(d.folder_name);
    if (d.videodownloader_token) settings.videodownloader_token=String(d.videodownloader_token).slice(0,5000); else if (d.clear_videodownloader_token) settings.videodownloader_token=''; saveSettings(); dispatcher();
    return sendJson(res,200,{ max_concurrent:settings.max_concurrent, folder_name:settings.folder_name, download_path:outputDir(settings.folder_name), auth_enabled:!!APP_PASSWORD, site_token_configured:!!(settings.videodownloader_token||process.env.VIDEODOWNLOADER_TOKEN) });
  }
  if (pathname === '/api/formats' && method === 'POST') {
    const d=await readBody(req); const raw=String(d.url||'').trim(); if(!raw) return sendError(res,400,'Paste a video URL first.'); const err=await validatePublicUrl(raw); if(err) return sendError(res,400,err);
    try {
      const { stdout }=await runCapture('yt-dlp',['--no-warnings','--no-playlist','--dump-single-json','--skip-download','--socket-timeout','30',raw],{timeout:90000});
      const info=JSON.parse(stdout); const byHeight=new Map();
      for(const f of info.formats||[]) { const h=Number(f.height||0); if(!h) continue; const existing=byHeight.get(h); const size=Number(f.filesize||f.filesize_approx||0); if(!existing || (f.acodec!=='none' && existing.acodec==='none') || size>(existing.filesize||0)) byHeight.set(h,{height:h,format_id:`height:${h}`,label:`${h}p`,filesize:size||null,acodec:f.acodec||'none'}); }
      const formats=[...byHeight.values()].sort((a,b)=>b.height-a.height);
      return sendJson(res,200,{title:info.title||safeLabel(raw),duration:info.duration||null,formats,message:formats.length?'Available resolutions loaded for this URL.':'No separate resolution list was provided; automatic quality remains available.'});
    } catch(e) { return sendError(res,502,'Could not read formats for this URL. It may be unsupported, private, or temporarily unavailable.'); }
  }
  if (pathname === '/api/add' && method === 'POST') {
    const d=await readBody(req); const raw=String(d.url||'').trim(); if(!raw) return sendError(res,400,'Paste a video URL first.'); const err=await validatePublicUrl(raw); if(err) return sendError(res,400,err); if(jobs.size>=MAX_JOBS) return sendError(res,429,'Queue is full. Delete old jobs before adding more.');
    const id=crypto.randomBytes(6).toString('hex'); const job={id,url:raw,title:String(d.title||safeLabel(raw)).replace(/[\r\n\t]/g,' ').slice(0,160),source:String(d.source||new URL(raw).hostname).slice(0,100),status:'queued',progress:0,stage_progress:0,speed:'',eta:'',created:now(),updated:now(),folder_name:settings.folder_name,file_path:'',error:'',format_id:String(d.format_id||'').slice(0,100),download_mode:String(d.mode||'compress').toLowerCase()==='original'?'original':'compress',cancel_requested:false};
    jobs.set(id,job); saveJobs(); dispatcher(); return sendJson(res,201,{job:publicJob(job)});
  }
  if (pathname === '/api/site/search' && method === 'GET') {
    const q=String(url.searchParams.get('q')||'').trim().slice(0,120); if(q.length<2) return sendJson(res,400,{error:'Enter at least two characters.'});
    try { const results=await animeSearch(q); return sendJson(res,200,{results}); } catch(e) { return sendError(res,502,e.message||'Anime search failed.'); }
  }
  if (pathname === '/api/site/episodes' && method === 'GET') {
    const session=String(url.searchParams.get('detailPath')||url.searchParams.get('session')||'').trim(); const id=String(url.searchParams.get('subjectId')||url.searchParams.get('id')||'').trim();
    if(!session) return sendError(res,400,'Select an anime first.');
    try { const [episodes, info]=await Promise.all([animeEpisodes(session,id), animePageInfo(session).catch(()=>({}))]); return sendJson(res,200,{episodes,info,session,subject_id:id}); } catch(e) { return sendError(res,502,e.message||'Could not load anime episodes.'); }
  }
  if (pathname === '/api/site/resolve' && method === 'POST') {
    const d=await readBody(req); const episodeUrl=String(d.episodeUrl||d.episode_url||'').trim();
    if(!episodeUrl) return sendError(res,400,'Select an episode first.');
    try { const qualities=await animeQualities(episodeUrl); return sendJson(res,200,{qualities,title:String(d.title||'Anime episode'),episode_url:episodeUrl}); } catch(e) { return sendError(res,502,e.message||'Could not read episode resolutions.'); }
  }
  if ((pathname === '/api/animepahe/qualities' || pathname === '/api/animepahe/queue') && method === 'POST') {
    const d=await readBody(req);
    if(pathname.endsWith('/qualities')) { try { return sendJson(res,200,{qualities:await animeQualities(String(d.url||d.episode_url||''))}); } catch(e) { return sendError(res,502,e.message); } }
    const episodeUrl=String(d.episode_url||''); const qualityUrl=String(d.quality_url||''); if(!validAnimeUrl(episodeUrl)||!validAnimeUrl(qualityUrl)) return sendError(res,400,'Select a valid episode and resolution.');
    if(jobs.size>=MAX_JOBS) return sendError(res,429,'Queue is full. Delete old jobs before adding more.');
    const id=crypto.randomBytes(6).toString('hex'); const mode=String(d.mode||'compress').toLowerCase()==='original'?'original':'compress'; const job={id,url:episodeUrl,episode_url:episodeUrl,quality_url:qualityUrl,source:'Anime episode',title:String(d.title||'Anime episode').slice(0,160),status:'queued',progress:0,stage_progress:0,speed:'',eta:'',created:now(),updated:now(),folder_name:settings.folder_name,file_path:'',error:'',format_id:'',download_mode:mode,cancel_requested:false}; jobs.set(id,job); saveJobs(); dispatcher(); return sendJson(res,201,{job:publicJob(job)});
  }
  const action = pathname.match(/^\/api\/jobs\/([a-f0-9]+)\/(pause|resume|cancel|retry)$/i);
  if(action && method==='POST') {
    const [,id,op]=action; const j=jobs.get(id); if(!j) return sendError(res,404,'Job not found.');
    if(op==='pause') {
      if(j.status==='queued') { updateJob(id,{status:'paused',paused_from:'queued'}); return sendJson(res,200,{ok:true}); }
      if(!ACTIVE.has(j.status)) return sendError(res,409,'This job cannot be paused in its current state.'); const p=processes.get(id); if(!p) return sendError(res,409,'The process is starting. Try again shortly.');
      try { process.kill(process.platform==='win32'?p.pid:-p.pid,'SIGSTOP'); updateJob(id,{paused_from:j.status,status:'paused'}); return sendJson(res,200,{ok:true}); } catch { return sendError(res,409,'Pause is not available for this process.'); }
    }
    if(op==='resume') { if(j.status!=='paused') return sendError(res,409,'This job is not paused.'); if(j.paused_from==='queued'||!processes.has(id)) { updateJob(id,{status:'queued',error:'',progress:0,stage_progress:0}); dispatcher(); return sendJson(res,200,{ok:true,requeued:true}); } try { const p=processes.get(id); process.kill(process.platform==='win32'?p.pid:-p.pid,'SIGCONT'); updateJob(id,{status:j.paused_from||'downloading',error:''}); return sendJson(res,200,{ok:true}); } catch { return sendError(res,409,'Could not resume this process. Retry the job.'); } }
    if(op==='cancel') { updateJob(id,{cancel_requested:true}); const p=processes.get(id); if(p) { try { process.kill(process.platform==='win32'?p.pid:-p.pid,'SIGCONT'); } catch {} try { process.kill(process.platform==='win32'?p.pid:-p.pid,'SIGTERM'); } catch {} } else if(['queued','paused'].includes(j.status)) updateJob(id,{status:'cancelled',error:'Cancelled'}); return sendJson(res,200,{ok:true}); }
    if(op==='retry') { if(!['failed','cancelled'].includes(j.status)) return sendError(res,409,'Only failed or cancelled jobs can be retried.'); updateJob(id,{status:'queued',progress:0,stage_progress:0,speed:'',eta:'',error:'',cancel_requested:false,source_size:null,downloaded_bytes:null,final_size:null,saved_percent:null,file:'',file_path:'',download_url:null,download_headers:null}); dispatcher(); return sendJson(res,200,{ok:true,job:publicJob(j)}); }
  }
  const del=pathname.match(/^\/api\/jobs\/([a-f0-9]+)$/i);
  if(del && method==='DELETE') { const id=del[1], j=jobs.get(id); if(!j) return sendError(res,404,'Job not found.'); if(ACTIVE.has(j.status)||j.status==='queued'||j.status==='paused') return sendError(res,409,'Cancel active jobs before deleting them.'); if(j.file_path) { try { await fsp.unlink(j.file_path); } catch {} } jobs.delete(id); saveJobs(); return sendJson(res,200,{ok:true}); }
  return sendError(res,404,'API route not found.');
}

async function handle(req,res) {
  const u = new URL(req.url, `http://${req.headers.host || 'localhost'}`);
  if (u.pathname === '/health' && req.method === 'GET') return sendText(res,200,'ok');
  if (u.pathname === '/login') {
    if (!APP_PASSWORD) { res.writeHead(302,{Location:'/'}); return res.end(); }
    if (req.method === 'GET') return sendText(res,200,fs.readFileSync(path.join(ROOT,'templates','login.html'),'utf8'),'text/html; charset=utf-8');
    if (req.method === 'POST') { const d=await readBody(req); if (String(d.password||'') !== APP_PASSWORD) return sendText(res,401,fs.readFileSync(path.join(ROOT,'templates','login.html'),'utf8').replace('<p>Enter your workspace password to access the download studio.</p>','<p style="color:#ff9bad">Incorrect password. Try again.</p>'),'text/html; charset=utf-8'); res.writeHead(303,{Location:'/', 'Set-Cookie':`m1080_session=${encodeURIComponent(makeSession())}; HttpOnly; SameSite=Lax; Path=/; Max-Age=604800${process.env.COOKIE_SECURE==='1'?'; Secure':''}`}); return res.end(); }
  }
  if (u.pathname === '/logout' && req.method === 'POST') { res.writeHead(303,{Location:'/login','Set-Cookie':'m1080_session=; HttpOnly; SameSite=Lax; Path=/; Max-Age=0'}); return res.end(); }
  if (u.pathname.startsWith('/api/')) {
    if (APP_PASSWORD && !validSession(req)) return sendError(res,401,'Please log in again.');
    return handleApi(req,res,u);
  }
  if (u.pathname.startsWith('/download/')) {
    if (APP_PASSWORD && !validSession(req)) { res.writeHead(302,{Location:'/login'}); return res.end(); }
    const id=u.pathname.slice('/download/'.length); const j=jobs.get(id);
    if(!j||j.status!=='ready'||!j.file_path) return sendText(res,404,'File not ready yet, or it has already been sent.');
    let stat; try { stat=await fsp.stat(j.file_path); } catch { return sendText(res,404,'File not found. The server may have restarted or storage may have changed.'); }
    const filename=`My1080pSaver-${id}${path.extname(j.file_path)||'.mkv'}`;
    res.writeHead(200,{'Content-Type':'application/octet-stream','Content-Length':stat.size,'Content-Disposition':`attachment; filename="${filename}"`,'Cache-Control':'no-store'});
    const stream=fs.createReadStream(j.file_path); stream.pipe(res);
    res.on('finish',()=>{ if(!res.writableFinished) return; fsp.unlink(j.file_path).catch(()=>{}).finally(()=>{ const current=jobs.get(id); if(current&&current.status==='ready'&&current.file_path===j.file_path) updateJob(id,{status:'downloaded',file_path:'',file:'',updated:now()}); }); });
    res.on('close',()=>{ if(!res.writableFinished) { /* Keep file/job intact if the phone/browser disconnects mid-transfer. */ } });
    return;
  }
  if (u.pathname === '/' || u.pathname === '/index.html') {
    if (APP_PASSWORD && !validSession(req)) { res.writeHead(302,{Location:'/login'}); return res.end(); }
    return sendText(res,200,fs.readFileSync(path.join(ROOT,'templates','index.html'),'utf8'),'text/html; charset=utf-8');
  }
  if (u.pathname === '/favicon.ico') return sendText(res,204,'');
  return sendText(res,404,'Not found.');
}

async function main() {
  await loadState();
  const server=http.createServer((req,res)=>{ handle(req,res).catch(e=>{ if(!res.headersSent) sendError(res,500,e.message||'Internal server error'); else res.destroy(); }); });
  server.requestTimeout=0; server.headersTimeout=65000; server.keepAliveTimeout=5000;
  server.listen(PORT,'0.0.0.0',()=>{ console.log(`MY 1080p SAVER listening on ${PORT}; data=${DATA_DIR}; downloads=${DOWNLOAD_ROOT}`); dispatcher(); });
  const stop=()=>{ shuttingDown=true; server.close(()=>process.exit(0)); setTimeout(()=>process.exit(0),10000).unref(); };
  process.on('SIGTERM',stop); process.on('SIGINT',stop);
}
main().catch(e=>{ console.error(e); process.exit(1); });

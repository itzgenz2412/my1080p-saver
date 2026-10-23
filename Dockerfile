FROM python:3.11-slim
ENV PYTHONDONTWRITEBYTECODE=1 PYTHONUNBUFFERED=1
RUN apt-get update && apt-get install -y --no-install-recommends ffmpeg ca-certificates curl unzip \
    && curl -fsSL https://deno.land/install.sh | sh \
    && rm -rf /var/lib/apt/lists/*
ENV PATH="/root/.deno/bin:${PATH}"
WORKDIR /app
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt && playwright install --with-deps chromium
COPY . .
RUN mkdir -p /app/downloads /app/data
EXPOSE 8000
CMD ["sh", "-c", "gunicorn --workers 1 --threads 12 --timeout 0 --bind 0.0.0.0:${PORT:-8000} app:app"]

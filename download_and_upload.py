#!/usr/bin/env python3
"""
download_and_upload.py
=======================
Reads tweet/X URLs from urlsnow.txt (repo root), downloads videos with yt-dlp
(retrying transient failures with backoff + a rate-limit cooldown instead of
giving up), then uploads everything into a new Google Drive folder.

Designed to run inside GitHub Actions via workflow_dispatch.

Env vars expected (set as GitHub Secrets):
    GDRIVE_CLIENT_ID
    GDRIVE_CLIENT_SECRET
    GDRIVE_REFRESH_TOKEN

CLI args (passed from workflow inputs):
    --folder-name   (required) name of the Drive folder to create & upload into
    --min-duration  (optional) seconds or mm:ss
    --max-duration  (optional) seconds or mm:ss
    --delay         (optional) seconds between videos, default 8

Progress / dedup files (committed back to the repo by the workflow):
    downloaded_videos.txt   permanent skip-list of already-downloaded URLs
    failed_videos.txt       URLs that could not be downloaded, with reason
"""

import os
import re
import sys
import time
import argparse
import zipfile
from datetime import datetime

import yt_dlp

REPO_ROOT = os.getcwd()
URLS_FILE = os.path.join(REPO_ROOT, "urlsnow.txt")
DOWNLOADED_LOG = os.path.join(REPO_ROOT, "downloaded_videos.txt")
FAILED_LOG = os.path.join(REPO_ROOT, "failed_videos.txt")
DOWNLOAD_DIR = os.path.join(REPO_ROOT, "downloads")
COOKIES_PATH = os.path.join(REPO_ROOT, "cookies.txt")  # optional, commit if you need age-restricted tweets

MAX_RETRIES = 6
RETRY_BASE_DELAY = 8
RETRY_MAX_DELAY = 90
COOLDOWN_TRIGGER = 4
COOLDOWN_SECONDS = 300

NO_VIDEO_PHRASES = [
    'no video could be found', 'no video', 'does not have a video',
    'this tweet is not available', 'tweet has been deleted',
]
RATE_LIMIT_PHRASES = [
    'rate', '429', '503', 'temporarily', 'too many requests',
    'unable to extract', 'http error 5', 'reset by peer',
    'connection', 'timed out', 'timeout',
]
TRANSIENT_PHRASES = RATE_LIMIT_PHRASES + ['login', 'log in', 'auth', 'age', '500', 'network']


# ───────────────────────── helpers ─────────────────────────

def extract_tweet_id(url: str):
    m = re.search(r'/status/(\d+)', url)
    return m.group(1) if m else None


def normalize_tweet_url(url: str) -> str:
    url = url.strip()
    m = re.match(r'(https?://(?:www\.)?(?:twitter|x)\.com/[^/]+/status/\d+)', url)
    return m.group(1) if m else url


def dedupe_preserve_order(urls):
    seen_ids, seen_urls, result, dupes = set(), set(), [], []
    for u in urls:
        u = u.strip()
        if not u:
            continue
        tid = extract_tweet_id(u)
        key = tid if tid else u
        if key in seen_ids or u in seen_urls:
            dupes.append(u)
        else:
            seen_ids.add(key)
            seen_urls.add(u)
            result.append(u)
    return result, dupes


def load_downloaded_set():
    ids, urls = set(), set()
    if os.path.exists(DOWNLOADED_LOG):
        with open(DOWNLOADED_LOG, 'r', encoding='utf-8') as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                url = line.split('\t')[0]
                urls.add(url)
                tid = extract_tweet_id(url)
                if tid:
                    ids.add(tid)
    return ids, urls


def append_downloaded(url, title=""):
    with open(DOWNLOADED_LOG, 'a', encoding='utf-8') as f:
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        f.write(f"{url}\t{title}\t{ts}\n")
        f.flush()
        os.fsync(f.fileno())


def append_failed(url, reason):
    with open(FAILED_LOG, 'a', encoding='utf-8') as f:
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        f.write(f"{url}\t{reason}\t{ts}\n")
        f.flush()
        os.fsync(f.fileno())


def parse_duration(text):
    text = (text or "").strip()
    if not text:
        return None
    try:
        if ':' in text:
            mm, ss = text.split(':')
            return int(mm) * 60 + int(ss)
        return int(float(text))
    except Exception:
        return None


def sleep_interruptible(seconds):
    # No "stop button" in CI, but kept as a single sleep point in case we
    # later want to respect a cancellation signal file, etc.
    time.sleep(seconds)


# ───────────────────────── download engine ─────────────────────────

def download_one(url, ydl_opts_extract, ydl_opts_download, min_seconds, max_seconds):
    """Returns (success: bool, was_rate_limited: bool, filepath_hint: str|None)."""
    attempt = 0
    delay = RETRY_BASE_DELAY
    while True:
        attempt += 1
        try:
            with yt_dlp.YoutubeDL(ydl_opts_extract) as ydl:
                info = ydl.extract_info(url, download=False)

            if info is None:
                print(f"❌ No info returned (deleted/private/image-only, or rate-limited).")
                if attempt < MAX_RETRIES:
                    print(f"   Retrying in {delay}s (treating as possible rate-limit)...")
                    sleep_interruptible(delay)
                    delay = min(delay * 2, RETRY_MAX_DELAY)
                    continue
                append_failed(url, "no info after retries")
                return False, True, None

            formats = info.get('formats', [])
            title = info.get('title', 'Unknown')
            video_id = info.get('id', 'unknown')
            duration = info.get('duration')

            if not formats:
                print(f"🖼️ {title} [{video_id}]: image-only tweet, no video. Skipping permanently.")
                append_failed(url, "image-only / no formats")
                return False, False, None

            if duration is not None:
                duration_int = int(duration)
                if min_seconds is not None and duration_int < min_seconds:
                    print(f"⏩ {title} [{video_id}]: shorter than min duration — skipped.")
                    return False, False, None
                if max_seconds is not None and duration_int > max_seconds:
                    print(f"⏩ {title} [{video_id}]: longer than max duration — skipped.")
                    return False, False, None

            print(f"⬇️ Downloading: {title[:60]} [{video_id}]")
            with yt_dlp.YoutubeDL(ydl_opts_download) as ydl_dl:
                result = ydl_dl.extract_info(url, download=True)
                filepath = ydl_dl.prepare_filename(result)
                # account for merge_output_format renaming to .mp4
                mp4_path = os.path.splitext(filepath)[0] + ".mp4"
                if os.path.exists(mp4_path):
                    filepath = mp4_path

            append_downloaded(url, title)
            print(f"✅ Saved: {title[:60]}")
            return True, False, filepath

        except Exception as e:
            raw = str(e)
            low = raw.lower()
            is_no_video = any(p in low for p in NO_VIDEO_PHRASES)
            is_rate_limit = any(p in low for p in RATE_LIMIT_PHRASES)
            is_transient = any(p in low for p in TRANSIENT_PHRASES)

            if is_no_video and not is_transient:
                print(f"🖼️ {url}: no video present — skipping permanently. ({raw[:120]})")
                append_failed(url, raw[:200])
                return False, False, None

            if attempt >= MAX_RETRIES:
                print(f"❌ {url}: failed after {attempt} attempts. Error: {raw[:150]}")
                append_failed(url, raw[:200])
                return False, is_rate_limit, None

            print(f"⚠️ Attempt {attempt}/{MAX_RETRIES} failed ({raw[:100]}). Retrying in {delay}s...")
            sleep_interruptible(delay)
            delay = min(delay * 2, RETRY_MAX_DELAY)


def run_downloads(urls, min_seconds, max_seconds, delay_seconds):
    os.makedirs(DOWNLOAD_DIR, exist_ok=True)
    cookiefile = COOKIES_PATH if (os.path.exists(COOKIES_PATH) and os.path.getsize(COOKIES_PATH) > 100) else None
    if not cookiefile:
        print("⚠️ cookies.txt not found — age-restricted tweets may fail.")

    ydl_opts_extract = {
        'quiet': True, 'no_warnings': True, 'skip_download': True,
        'cookiefile': cookiefile, 'nocheckcertificate': True,
    }
    ydl_opts_download = {
        'format': 'bestvideo[ext=mp4]+bestaudio[ext=m4a]/best[ext=mp4]/best',
        'outtmpl': os.path.join(DOWNLOAD_DIR, '%(uploader)s - %(upload_date)s - %(title)s [%(id)s].%(ext)s'),
        'merge_output_format': 'mp4',
        'restrictfilenames': True,
        'ignoreerrors': False,
        'cookiefile': cookiefile,
        'nocheckcertificate': True,
        'concurrent_fragments': 5,
        'quiet': True, 'no_warnings': True,
    }

    downloaded_ids, downloaded_urls = load_downloaded_set()
    stats = {'success': 0, 'skipped': 0, 'failed': 0, 'duplicates': 0}
    new_files = []
    consecutive_rate_limit = 0
    total = len(urls)

    for i, raw_url in enumerate(urls):
        url = normalize_tweet_url(raw_url)
        print(f"\n[{i + 1}/{total}] Checking: {url}")

        tid = extract_tweet_id(url)
        if url in downloaded_urls or (tid and tid in downloaded_ids):
            print("🔁 Already in downloaded_videos.txt — skipped.")
            stats['duplicates'] += 1
            stats['skipped'] += 1
            continue

        ok, was_rate_limited, filepath = download_one(url, ydl_opts_extract, ydl_opts_download, min_seconds, max_seconds)

        if ok:
            stats['success'] += 1
            downloaded_urls.add(url)
            if tid:
                downloaded_ids.add(tid)
            if filepath and os.path.exists(filepath):
                new_files.append(filepath)
        elif was_rate_limited:
            stats['failed'] += 1
        else:
            stats['skipped'] += 1

        if was_rate_limited:
            consecutive_rate_limit += 1
            if consecutive_rate_limit >= COOLDOWN_TRIGGER:
                print(f"\n🧊 {consecutive_rate_limit} rate-limit-like failures in a row — "
                      f"cooling down for {COOLDOWN_SECONDS}s...")
                sleep_interruptible(COOLDOWN_SECONDS)
                consecutive_rate_limit = 0
        else:
            consecutive_rate_limit = 0

        if delay_seconds > 0 and i < total - 1:
            sleep_interruptible(delay_seconds)

    return stats, new_files


# ───────────────────────── Google Drive upload ─────────────────────────

def get_drive_service():
    import json as _json
    from google.oauth2.credentials import Credentials
    from google.auth.transport.requests import Request
    from googleapiclient.discovery import build

    raw = os.environ.get("GDRIVE_TOKEN_JSON")
    if not raw:
        raise RuntimeError(
            "Missing GDRIVE_TOKEN_JSON environment variable. "
            "Set it as a single GitHub Secret containing the full token JSON "
            "(token, refresh_token, client_id, client_secret, token_uri, scopes)."
        )

    info = _json.loads(raw)
    creds = Credentials(
        token=info.get("token"),
        refresh_token=info["refresh_token"],
        client_id=info["client_id"],
        client_secret=info["client_secret"],
        token_uri=info.get("token_uri", "https://oauth2.googleapis.com/token"),
        scopes=info.get("scopes", ["https://www.googleapis.com/auth/drive"]),
    )
    creds.refresh(Request())
    return build("drive", "v3", credentials=creds)


def create_drive_folder(service, folder_name):
    from googleapiclient.errors import HttpError
    metadata = {"name": folder_name, "mimeType": "application/vnd.google-apps.folder"}
    folder = service.files().create(body=metadata, fields="id, webViewLink").execute()
    return folder["id"], folder.get("webViewLink")


def upload_files_to_folder(service, folder_id, filepaths):
    from googleapiclient.http import MediaFileUpload
    uploaded = []
    for fp in filepaths:
        name = os.path.basename(fp)
        print(f"☁️ Uploading to Drive: {name}")
        media = MediaFileUpload(fp, resumable=True)
        metadata = {"name": name, "parents": [folder_id]}
        f = service.files().create(body=metadata, media_body=media, fields="id, name").execute()
        uploaded.append(f["name"])
    return uploaded


# ───────────────────────── main ─────────────────────────

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--folder-name", required=True)
    parser.add_argument("--min-duration", default="")
    parser.add_argument("--max-duration", default="")
    parser.add_argument("--delay", default="8")
    args = parser.parse_args()

    folder_name = "".join(c for c in args.folder_name.strip() if c.isalnum() or c in (' ', '-', '_')).strip() or "downloads"
    min_seconds = parse_duration(args.min_duration)
    max_seconds = parse_duration(args.max_duration)
    delay_seconds = parse_duration(args.delay) or 8

    if not os.path.exists(URLS_FILE):
        print(f"❌ {URLS_FILE} not found. Add your URLs there (one per line) at the repo root.")
        sys.exit(1)

    with open(URLS_FILE, "r", encoding="utf-8") as f:
        raw_urls = [u.strip() for u in f if u.strip()]

    urls, list_dupes = dedupe_preserve_order(raw_urls)
    if list_dupes:
        print(f"🔁 Removed {len(list_dupes)} duplicate URL(s) within urlsnow.txt.")

    print(f"Starting run: {len(urls)} unique URL(s), folder='{folder_name}', "
          f"min={min_seconds}, max={max_seconds}, delay={delay_seconds}s")

    stats, new_files = run_downloads(urls, min_seconds, max_seconds, delay_seconds)

    print(f"\n📊 Download summary: success={stats['success']} skipped={stats['skipped']} "
          f"failed={stats['failed']} duplicates={stats['duplicates']}")

    summary_path = os.environ.get("GITHUB_STEP_SUMMARY")

    if not new_files:
        print("No new files downloaded — nothing to upload.")
        if summary_path:
            with open(summary_path, "a", encoding="utf-8") as f:
                f.write(f"### Download run\nNo new files downloaded.\n\n"
                        f"- Success: {stats['success']}\n- Skipped: {stats['skipped']}\n"
                        f"- Failed: {stats['failed']}\n- Duplicates: {stats['duplicates']}\n")
        return

    print(f"\nUploading {len(new_files)} file(s) to Google Drive folder '{folder_name}'...")
    service = get_drive_service()
    folder_id, folder_link = create_drive_folder(service, folder_name)
    uploaded = upload_files_to_folder(service, folder_id, new_files)

    print(f"\n✅ Uploaded {len(uploaded)} file(s) to Drive folder '{folder_name}'.")
    if folder_link:
        print(f"🔗 {folder_link}")

    if summary_path:
        with open(summary_path, "a", encoding="utf-8") as f:
            f.write(f"### Download + Upload run\n\n"
                    f"- Success: {stats['success']}\n- Skipped: {stats['skipped']}\n"
                    f"- Failed: {stats['failed']}\n- Duplicates: {stats['duplicates']}\n\n"
                    f"**Drive folder:** [{folder_name}]({folder_link})\n\n"
                    f"Uploaded files:\n" + "\n".join(f"- {n}" for n in uploaded) + "\n")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
download_and_upload.py
=======================
Reads tweet/X URLs from urlsnow.txt (repo root). For each URL:
    - Downloads images directly (no video-check first) if the URL is
      detected as image-only via cached status data
    - Downloads videos if the tweet has video/GIF
    - Filters videos by duration BEFORE downloading (metadata only)
    - Uploads everything to a new Google Drive folder

Duration filtering: uses yt-dlp metadata (no download needed) then checks
with ffprobe as a fallback. Requires ffmpeg/ffprobe to be installed for
merging best-quality video+audio streams.

Env vars expected (set as GitHub Secrets):
    GDRIVE_TOKEN_JSON   full token JSON blob

CLI args:
    --folder-name   (required) Drive folder name
    --min-duration  (optional) seconds or mm:ss
    --max-duration  (optional) seconds or mm:ss
    --delay         (optional) seconds between items, default 8
"""

import os
import re
import sys
import time
import subprocess
import argparse
from datetime import datetime
from urllib.parse import urlparse, parse_qsl, urlencode, urlunparse

import yt_dlp
import requests

REPO_ROOT = os.getcwd()
URLS_FILE = os.path.join(REPO_ROOT, "urlsnow.txt")
DOWNLOADED_LOG = os.path.join(REPO_ROOT, "downloaded_videos.txt")
FAILED_LOG = os.path.join(REPO_ROOT, "failed_videos.txt")
DOWNLOAD_DIR = os.path.join(REPO_ROOT, "downloads")
COOKIES_PATH = os.path.join(REPO_ROOT, "cookies.txt")

MAX_RETRIES = 5
RETRY_BASE_DELAY = 8
RETRY_MAX_DELAY = 90
COOLDOWN_TRIGGER = 4
COOLDOWN_SECONDS = 300

RATE_LIMIT_PHRASES = [
    'rate', '429', '503', 'temporarily', 'too many requests',
    'unable to extract', 'http error 5', 'reset by peer',
    'connection', 'timed out', 'timeout', 'bad guest token',
]
TRANSIENT_PHRASES = RATE_LIMIT_PHRASES + ['login', 'log in', 'auth', 'age', '500', 'network']


# ─────────────────────────────────── helpers ────────────────────────────────

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


def safe_filename_piece(text, max_len=80):
    text = re.sub(r'[^A-Za-z0-9._-]+', '_', text or '')
    text = re.sub(r'_+', '_', text).strip('_')
    return text[:max_len] or "untitled"


def ffprobe_duration(filepath: str):
    """Get video duration via ffprobe. Returns seconds (float) or None."""
    try:
        result = subprocess.run(
            ['ffprobe', '-v', 'error', '-show_entries', 'format=duration',
             '-of', 'default=noprint_wrappers=1:nokey=1', filepath],
            capture_output=True, text=True, timeout=30
        )
        val = result.stdout.strip()
        return float(val) if val else None
    except Exception:
        return None


def check_ffmpeg():
    """Warn if ffmpeg is not installed."""
    try:
        subprocess.run(['ffmpeg', '-version'], capture_output=True, timeout=10)
        return True
    except Exception:
        print("⚠️  ffmpeg not found — best-quality video+audio merging will fail.")
        print("   Add 'sudo apt-get install -y ffmpeg' to your workflow before running this script.")
        return False


# ──────────────────── status cache (monkeypatch) ────────────────────────────
#
# yt-dlp's TwitterIE already fetches the full tweet status internally during
# extract_info(). We cache it to read photo URLs without any extra request.

_STATUS_CACHE: dict = {}


def _install_status_cache_patch():
    from yt_dlp.extractor.twitter import TwitterIE
    if getattr(TwitterIE, "_status_cache_patched", False):
        return

    original = TwitterIE._extract_status

    def patched(self, twid, *args, **kwargs):
        status = original(self, twid, *args, **kwargs)
        if status:
            _STATUS_CACHE[twid] = status
        return status

    TwitterIE._extract_status = patched
    TwitterIE._status_cache_patched = True


def _get_media_from_status(twid: str):
    """
    Returns (photos: list[str], has_video: bool) from cached status.
    Returns (None, None) if no cached data.
    """
    status = _STATUS_CACHE.get(twid)
    if status is None:
        return None, None

    photos, has_video = [], False
    for detail in (status.get("extended_entities", {}).get("media") or []):
        mtype = detail.get("type", "")
        if mtype == "photo":
            url = detail.get("media_url_https") or detail.get("media_url")
            if url:
                photos.append(url)
        elif mtype in ("video", "animated_gif"):
            has_video = True

    return photos, has_video


# ──────────────────────── image download ────────────────────────────────────

def download_image(url: str, dest_dir: str, basename_hint: str) -> str:
    os.makedirs(dest_dir, exist_ok=True)
    parsed = urlparse(url)
    ext = os.path.splitext(parsed.path)[1].lstrip('.').lower() or "jpg"
    if ext not in ("jpg", "jpeg", "png", "webp", "gif"):
        ext = "jpg"

    # Request original-size image from Twitter CDN
    full_url = url
    if "pbs.twimg.com" in url:
        query_pairs = [(k, v) for k, v in parse_qsl(parsed.query) if k != "name"]
        query_pairs.append(("name", "orig"))
        full_url = urlunparse(parsed._replace(query=urlencode(query_pairs)))

    filepath = os.path.join(dest_dir, f"{basename_hint}.{ext}")
    resp = requests.get(full_url, timeout=30, stream=True)
    resp.raise_for_status()
    with open(filepath, "wb") as f:
        for chunk in resp.iter_content(chunk_size=1 << 16):
            if chunk:
                f.write(chunk)
    return filepath


def download_images_for_tweet(url: str, twid: str):
    """
    Returns (success: bool, filepaths: list[str]).
    Reads from cached status — NO extra network request.
    """
    photos, _ = _get_media_from_status(twid)

    if photos is None:
        print(f"   ⚠️  No cached status for {twid}. Monkeypatch may not have fired.")
        return False, []

    if not photos:
        print(f"   ℹ️  No photo media in status for {twid}.")
        return False, []

    print(f"   🖼️  Found {len(photos)} photo(s) for {twid}, downloading...")
    filepaths = []
    for idx, photo_url in enumerate(photos, 1):
        hint = safe_filename_piece(f"{twid}_img{idx}")
        try:
            fp = download_image(photo_url, DOWNLOAD_DIR, hint)
            filepaths.append(fp)
            print(f"   ✅ Image {idx}: {os.path.basename(fp)}")
        except requests.exceptions.RequestException as e:
            print(f"   ⚠️  Image {idx} fetch failed: {str(e)[:120]}")

    return len(filepaths) > 0, filepaths


# ──────────────────────── core download logic ────────────────────────────────

def _make_ydl_opts(cookiefile, download=False):
    base = {
        'quiet': True,
        'no_warnings': True,
        'nocheckcertificate': True,
        'cookiefile': cookiefile,
    }
    if not download:
        base['skip_download'] = True
        return base

    base.update({
        'format': 'bestvideo[ext=mp4]+bestaudio[ext=m4a]/best[ext=mp4]/best',
        'outtmpl': os.path.join(
            DOWNLOAD_DIR,
            '%(uploader)s_%(upload_date)s_%(title).60s_[%(id)s].%(ext)s'
        ),
        'merge_output_format': 'mp4',
        'restrictfilenames': True,
        'ignoreerrors': False,
        'concurrent_fragments': 4,
        'retries': 3,
    })
    return base


def _duration_ok(duration_sec, min_seconds, max_seconds, label=""):
    if duration_sec is None:
        return True  # unknown duration — don't filter out
    d = int(duration_sec)
    if min_seconds is not None and d < min_seconds:
        print(f"   ⏩ {label}: {d}s < min {min_seconds}s — skipped.")
        return False
    if max_seconds is not None and d > max_seconds:
        print(f"   ⏩ {label}: {d}s > max {max_seconds}s — skipped.")
        return False
    return True


def download_one(url: str, cookiefile, min_seconds, max_seconds):
    """
    Returns (kind, success, was_rate_limited, filepaths).
    kind: 'video' | 'image' | 'none'

    Strategy:
    1. Call extract_info(download=False) — this fires the monkeypatch and
       populates _STATUS_CACHE with the tweet's media list.
    2. Check cached status FIRST:
       - If photo-only → download images immediately, no video attempt.
       - If has video → proceed with video duration check + download.
    3. If no cached status (unusual) → fall back to formats list.
    """
    twid = extract_tweet_id(url)
    attempt = 0
    delay = RETRY_BASE_DELAY

    while attempt < MAX_RETRIES:
        attempt += 1
        try:
            opts = _make_ydl_opts(cookiefile, download=False)
            with yt_dlp.YoutubeDL(opts) as ydl:
                info = ydl.extract_info(url, download=False)

        except Exception as e:
            raw = str(e)
            low = raw.lower()
            is_transient = any(p in low for p in TRANSIENT_PHRASES)

            if not is_transient:
                # Hard failure (deleted, private, etc.) — try images from cache
                print(f"   ⚠️  extract_info failed: {raw[:120]}")
                if twid:
                    ok, filepaths = download_images_for_tweet(url, twid)
                    if ok:
                        append_downloaded(url, f"[{len(filepaths)} image(s)]")
                        _STATUS_CACHE.pop(twid, None)
                        return 'image', True, False, filepaths
                append_failed(url, raw[:200])
                _STATUS_CACHE.pop(twid, None)
                return 'none', False, False, []

            if attempt >= MAX_RETRIES:
                print(f"   ❌ Failed after {attempt} attempts: {raw[:120]}")
                append_failed(url, raw[:200])
                _STATUS_CACHE.pop(twid, None)
                return 'none', False, True, []

            print(f"   ⚠️  Attempt {attempt}/{MAX_RETRIES}: {raw[:80]} — retry in {delay}s")
            time.sleep(delay)
            delay = min(delay * 2, RETRY_MAX_DELAY)
            continue

        # ── We have info. Now decide: image tweet or video tweet? ──────────

        title = (info or {}).get('title', url) if info else url
        video_id = (info or {}).get('id', 'unknown') if info else 'unknown'

        # Check cached status first — most reliable signal
        if twid:
            photos, has_video = _get_media_from_status(twid)

            if photos is not None:
                # We have definitive media type info from the status object

                if photos and not has_video:
                    # ── PHOTO-ONLY TWEET ───────────────────────────────────
                    # Don't try video at all. Download images immediately.
                    print(f"   🖼️  Photo-only tweet ({len(photos)} photo(s)): {title[:60]}")
                    ok, filepaths = download_images_for_tweet(url, twid)
                    if ok:
                        append_downloaded(url, f"{title} [{len(filepaths)} image(s)]")
                        _STATUS_CACHE.pop(twid, None)
                        return 'image', True, False, filepaths
                    else:
                        append_failed(url, "image fetch failed")
                        _STATUS_CACHE.pop(twid, None)
                        return 'none', False, False, []

                # has_video is True (or photos=[] meaning no media at all)
                # Fall through to video handling below.

        # ── VIDEO (or unknown) path ────────────────────────────────────────

        if info is None:
            print(f"   ❌ No info returned and no cached images — skipping.")
            append_failed(url, "no info, no images")
            _STATUS_CACHE.pop(twid, None)
            return 'none', False, True, []

        formats = info.get('formats', [])

        if not formats:
            # No video formats — try images from cache as last resort
            print(f"   ℹ️  No video formats for {title[:60]} — trying cached images...")
            if twid:
                ok, filepaths = download_images_for_tweet(url, twid)
                if ok:
                    append_downloaded(url, f"{title} [{len(filepaths)} image(s)]")
                    _STATUS_CACHE.pop(twid, None)
                    return 'image', True, False, filepaths
            append_failed(url, "no formats and no images")
            _STATUS_CACHE.pop(twid, None)
            return 'none', False, False, []

        # ── Duration check BEFORE download ────────────────────────────────
        duration = info.get('duration')
        label = f"{title[:50]} [{video_id}]"

        if not _duration_ok(duration, min_seconds, max_seconds, label):
            _STATUS_CACHE.pop(twid, None)
            return 'none', False, False, []

        # ── Actual video download ─────────────────────────────────────────
        print(f"   ⬇️  Downloading: {label}  ({duration}s)")
        dl_opts = _make_ydl_opts(cookiefile, download=True)

        try:
            with yt_dlp.YoutubeDL(dl_opts) as ydl_dl:
                result = ydl_dl.extract_info(url, download=True)
                filepath = ydl_dl.prepare_filename(result)

            # yt-dlp may rename to .mp4 after ffmpeg merge
            mp4_path = os.path.splitext(filepath)[0] + ".mp4"
            if os.path.exists(mp4_path):
                filepath = mp4_path

            if not os.path.exists(filepath):
                # Search downloads dir for a file matching the video id
                for fn in os.listdir(DOWNLOAD_DIR):
                    if video_id in fn:
                        filepath = os.path.join(DOWNLOAD_DIR, fn)
                        break

        except Exception as e:
            raw = str(e)
            low = raw.lower()
            is_transient = any(p in low for p in TRANSIENT_PHRASES)
            if attempt < MAX_RETRIES and is_transient:
                print(f"   ⚠️  Download attempt {attempt} failed: {raw[:80]} — retry in {delay}s")
                time.sleep(delay)
                delay = min(delay * 2, RETRY_MAX_DELAY)
                continue
            append_failed(url, raw[:200])
            _STATUS_CACHE.pop(twid, None)
            return 'none', False, is_transient, []

        # ── Post-download duration check via ffprobe (belt-and-suspenders) ─
        if os.path.exists(filepath) and (min_seconds or max_seconds):
            actual_dur = ffprobe_duration(filepath)
            if actual_dur is not None and not _duration_ok(actual_dur, min_seconds, max_seconds, f"{label} (actual)"):
                os.remove(filepath)
                _STATUS_CACHE.pop(twid, None)
                return 'none', False, False, []

        append_downloaded(url, title)
        print(f"   ✅ Saved: {os.path.basename(filepath)}")
        _STATUS_CACHE.pop(twid, None)
        return 'video', True, False, [filepath]

    # Exhausted retries
    append_failed(url, "max retries exceeded")
    _STATUS_CACHE.pop(twid, None)
    return 'none', False, True, []


# ──────────────────────── run loop ──────────────────────────────────────────

def run_downloads(urls, min_seconds, max_seconds, delay_seconds):
    os.makedirs(DOWNLOAD_DIR, exist_ok=True)
    _install_status_cache_patch()
    check_ffmpeg()

    cookiefile = COOKIES_PATH if (
        os.path.exists(COOKIES_PATH) and os.path.getsize(COOKIES_PATH) > 100
    ) else None
    if not cookiefile:
        print("⚠️  cookies.txt not found — age-restricted tweets may fail.")

    downloaded_ids, downloaded_urls = load_downloaded_set()
    stats = {'success_video': 0, 'success_image': 0, 'skipped': 0, 'failed': 0, 'duplicates': 0}
    new_files = []
    consecutive_rate_limit = 0
    total = len(urls)

    for i, raw_url in enumerate(urls):
        url = normalize_tweet_url(raw_url)
        tid = extract_tweet_id(url)
        print(f"\n[{i + 1}/{total}] {url}")

        if url in downloaded_urls or (tid and tid in downloaded_ids):
            print("   🔁 Already downloaded — skipped.")
            stats['duplicates'] += 1
            stats['skipped'] += 1
            continue

        kind, ok, was_rate_limited, filepaths = download_one(
            url, cookiefile, min_seconds, max_seconds
        )

        if ok:
            if kind == 'video':
                stats['success_video'] += 1
            elif kind == 'image':
                stats['success_image'] += 1
            downloaded_urls.add(url)
            if tid:
                downloaded_ids.add(tid)
            for fp in filepaths:
                if fp and os.path.exists(fp):
                    new_files.append(fp)
        elif was_rate_limited:
            stats['failed'] += 1
        else:
            stats['skipped'] += 1

        if was_rate_limited:
            consecutive_rate_limit += 1
            if consecutive_rate_limit >= COOLDOWN_TRIGGER:
                print(f"\n🧊 {consecutive_rate_limit} rate-limit failures — cooling down {COOLDOWN_SECONDS}s...")
                time.sleep(COOLDOWN_SECONDS)
                consecutive_rate_limit = 0
        else:
            consecutive_rate_limit = 0

        if delay_seconds > 0 and i < total - 1:
            time.sleep(delay_seconds)

    return stats, new_files


# ──────────────────────── Google Drive upload ────────────────────────────────

def get_drive_service():
    import json as _json
    from google.oauth2.credentials import Credentials
    from google.auth.transport.requests import Request
    from googleapiclient.discovery import build

    raw = os.environ.get("GDRIVE_TOKEN_JSON")
    if not raw:
        raise RuntimeError("Missing GDRIVE_TOKEN_JSON environment variable.")

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
    metadata = {"name": folder_name, "mimeType": "application/vnd.google-apps.folder"}
    folder = service.files().create(body=metadata, fields="id, webViewLink").execute()
    return folder["id"], folder.get("webViewLink")


def upload_files_to_folder(service, folder_id, filepaths):
    from googleapiclient.http import MediaFileUpload
    uploaded = []
    for fp in filepaths:
        name = os.path.basename(fp)
        print(f"   ☁️  Uploading: {name}")
        media = MediaFileUpload(fp, resumable=True)
        metadata = {"name": name, "parents": [folder_id]}
        f = service.files().create(body=metadata, media_body=media, fields="id, name").execute()
        uploaded.append(f["name"])
    return uploaded


# ──────────────────────── main ───────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--folder-name", required=True)
    parser.add_argument("--min-duration", default="")
    parser.add_argument("--max-duration", default="")
    parser.add_argument("--delay", default="8")
    args = parser.parse_args()

    folder_name = (
        "".join(c for c in args.folder_name.strip() if c.isalnum() or c in (' ', '-', '_')).strip()
        or "downloads"
    )
    min_seconds = parse_duration(args.min_duration)
    max_seconds = parse_duration(args.max_duration)
    delay_seconds = parse_duration(args.delay) or 8

    if not os.path.exists(URLS_FILE):
        print(f"❌ {URLS_FILE} not found.")
        sys.exit(1)

    with open(URLS_FILE, "r", encoding="utf-8") as f:
        raw_urls = [u.strip() for u in f if u.strip() and not u.startswith('#')]

    urls, list_dupes = dedupe_preserve_order(raw_urls)
    if list_dupes:
        print(f"🔁 Removed {len(list_dupes)} duplicate(s) from urlsnow.txt.")

    print(
        f"Starting: {len(urls)} URLs | folder='{folder_name}' | "
        f"min={min_seconds}s | max={max_seconds}s | delay={delay_seconds}s"
    )

    stats, new_files = run_downloads(urls, min_seconds, max_seconds, delay_seconds)

    print(
        f"\n📊 Summary: videos={stats['success_video']} images={stats['success_image']} "
        f"skipped={stats['skipped']} failed={stats['failed']} dupes={stats['duplicates']}"
    )

    summary_path = os.environ.get("GITHUB_STEP_SUMMARY")

    if not new_files:
        print("No new files — nothing to upload.")
        if summary_path:
            with open(summary_path, "a") as f:
                f.write(
                    f"### Run complete\nNo new files.\n\n"
                    f"- Videos: {stats['success_video']}\n"
                    f"- Images: {stats['success_image']}\n"
                    f"- Skipped: {stats['skipped']}\n"
                    f"- Failed: {stats['failed']}\n"
                    f"- Duplicates: {stats['duplicates']}\n"
                )
        return

    print(f"\nUploading {len(new_files)} file(s) to Drive folder '{folder_name}'...")
    service = get_drive_service()
    folder_id, folder_link = create_drive_folder(service, folder_name)
    uploaded = upload_files_to_folder(service, folder_id, new_files)

    print(f"\n✅ Uploaded {len(uploaded)} file(s) to '{folder_name}'.")
    if folder_link:
        print(f"🔗 {folder_link}")

    if summary_path:
        with open(summary_path, "a") as f:
            f.write(
                f"### Run complete\n\n"
                f"- Videos: {stats['success_video']}\n"
                f"- Images: {stats['success_image']}\n"
                f"- Skipped: {stats['skipped']}\n"
                f"- Failed: {stats['failed']}\n"
                f"- Duplicates: {stats['duplicates']}\n\n"
                f"**Drive folder:** [{folder_name}]({folder_link})\n\n"
                + "\n".join(f"- {n}" for n in uploaded) + "\n"
            )


if __name__ == "__main__":
    main()

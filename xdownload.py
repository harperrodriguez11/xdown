#!/usr/bin/env python3
"""
download_and_upload.py
Reads tweet/X URLs from urlsnow.txt. Downloads images or videos, enforcing
duration and size limits. Uploads everything (images AND videos) to Drive.
Runs downloads concurrently for speed. Exits cleanly if nothing to do.

Filename pattern for every saved file (image or video):
    {title}_{tweet_id}_{upload_date}.{ext}
If the tweet has no meaningful title (e.g. it's just "wataa", empty, or a
generic placeholder), the title is omitted:
    {tweet_id}_{upload_date}.{ext}
"""

import os, re, sys, time, subprocess, argparse, threading
from datetime import datetime
from urllib.parse import urlparse, parse_qsl, urlencode, urlunparse
from concurrent.futures import ThreadPoolExecutor, as_completed

import yt_dlp
import requests

REPO_ROOT      = os.getcwd()
URLS_FILE      = os.path.join(REPO_ROOT, "urlsnow.txt")
DOWNLOADED_LOG = os.path.join(REPO_ROOT, "downloaded_videos.txt")
FAILED_LOG     = os.path.join(REPO_ROOT, "failed_videos.txt")
DOWNLOAD_DIR   = os.path.join(REPO_ROOT, "downloads")
COOKIES_PATH   = os.path.join(REPO_ROOT, "cookies.txt")

MAX_RETRIES      = 5
RETRY_BASE_DELAY = 8
RETRY_MAX_DELAY  = 90
COOLDOWN_TRIGGER = 4
COOLDOWN_SECONDS = 300

SIZE_LIMIT = 40 * 1024 * 1024  # 40 MB hard cap

RATE_LIMIT_PHRASES = [
    'rate','429','503','temporarily','too many requests','unable to extract',
    'http error 5','reset by peer','connection','timed out','timeout','bad guest token',
]
TRANSIENT_PHRASES = RATE_LIMIT_PHRASES + ['login','log in','auth','age','500','network']
LIMIT_PHRASES     = ['sizelimit','filesize','exceeds','fragment limit','max_fragments']

# Titles that carry no real meaning and should be dropped from the filename
GENERIC_TITLE_PLACEHOLDERS = {
    "wataa", "video", "media", "twitter", "x", "tweet", "untitled",
    "watch", "post", "nan", "none", "na",
}

# ─────────────────────── thread-safety primitives ───────────────────────────
_log_lock   = threading.Lock()
_cache_lock = threading.Lock()
_state_lock = threading.Lock()
_rename_lock = threading.Lock()

_cooldown_until  = 0.0
_consecutive_rl  = 0


# ─────────────────────────── helpers ────────────────────────────────────────

def extract_tweet_id(url):
    m = re.search(r'/status/(\d+)', url)
    return m.group(1) if m else None

def normalize_tweet_url(url):
    url = url.strip()
    m = re.match(r'(https?://(?:www\.)?(?:twitter|x)\.com/[^/]+/status/\d+)', url)
    return m.group(1) if m else url

def dedupe_preserve_order(urls):
    seen_ids, seen_urls, result, dupes = set(), set(), [], []
    for u in urls:
        u = u.strip()
        if not u: continue
        tid = extract_tweet_id(u)
        key = tid if tid else u
        if key in seen_ids or u in seen_urls:
            dupes.append(u)
        else:
            seen_ids.add(key); seen_urls.add(u); result.append(u)
    return result, dupes

def load_downloaded_set():
    ids, urls = set(), set()
    if os.path.exists(DOWNLOADED_LOG):
        with open(DOWNLOADED_LOG, 'r', encoding='utf-8') as f:
            for line in f:
                line = line.strip()
                if not line: continue
                url = line.split('\t')[0]
                urls.add(url)
                tid = extract_tweet_id(url)
                if tid: ids.add(tid)
    return ids, urls

def append_downloaded(url, title=""):
    with _log_lock:
        with open(DOWNLOADED_LOG, 'a', encoding='utf-8') as f:
            ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            f.write(f"{url}\t{title}\t{ts}\n"); f.flush(); os.fsync(f.fileno())

def append_failed(url, reason):
    with _log_lock:
        with open(FAILED_LOG, 'a', encoding='utf-8') as f:
            ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            f.write(f"{url}\t{reason}\t{ts}\n"); f.flush(); os.fsync(f.fileno())

def parse_duration(text):
    text = (text or "").strip()
    if not text: return None
    try:
        if ':' in text:
            mm, ss = text.split(':'); return int(mm)*60 + int(ss)
        return int(float(text))
    except Exception: return None

def safe_filename_piece(text, max_len=80, default="untitled"):
    text = re.sub(r'[^A-Za-z0-9._-]+', '_', text or '')
    text = re.sub(r'_+', '_', text).strip('_')
    return text[:max_len] or default

def normalize_date_str(upload_date):
    """yt-dlp upload_date is already YYYYMMDD; fall back to today's date."""
    if upload_date and re.match(r'^\d{8}$', str(upload_date)):
        return str(upload_date)
    return datetime.now().strftime("%Y%m%d")

def strip_uploader_prefix(title, uploader):
    """
    yt-dlp's Twitter extractor formats title as '{uploader} - {tweet text}'.
    We only want the tweet text in the filename, never the account name/handle.
    """
    if not title:
        return title
    title = title.strip()
    if uploader:
        for candidate in (uploader, uploader.lstrip('@')):
            prefix = f"{candidate} - "
            if title.lower().startswith(prefix.lower()):
                title = title[len(prefix):].strip()
                break
    # Fallback: also strip a generic "<handle-like-token> - " prefix even if
    # we don't have an explicit uploader field to compare against.
    m = re.match(r'^[\w.]{1,30}\s*-\s+(.*)$', title)
    if m and m.group(1):
        title = m.group(1).strip()
    return title

def build_base_name(title, twid, upload_date, uploader=None):
    """
    Produces: {title}_{id}_{date}   or   {id}_{date}  when the title is
    missing / generic (e.g. 'wataa') or turns out to just be the uploader's
    username/handle with nothing else.
    """
    date_str = normalize_date_str(upload_date)
    clean_title = strip_uploader_prefix(title, uploader)
    slug = safe_filename_piece(clean_title, max_len=100, default="")
    check = slug.lower().replace("_", "")
    if not slug or len(check) <= 2 or check in GENERIC_TITLE_PLACEHOLDERS:
        return f"{twid}_{date_str}"
    return f"{slug}_{twid}_{date_str}"

def unique_path(dest_dir, base_name, ext):
    """Avoids overwriting an existing file with the same computed name."""
    with _rename_lock:
        fp = os.path.join(dest_dir, f"{base_name}.{ext}")
        n = 2
        while os.path.exists(fp):
            fp = os.path.join(dest_dir, f"{base_name}_{n}.{ext}")
            n += 1
        # reserve the name immediately so concurrent workers don't collide
        open(fp, "a").close()
    return fp

def ffprobe_duration(filepath):
    try:
        r = subprocess.run(
            ['ffprobe','-v','error','-show_entries','format=duration',
             '-of','default=noprint_wrappers=1:nokey=1', filepath],
            capture_output=True, text=True, timeout=30)
        val = r.stdout.strip()
        return float(val) if val else None
    except Exception: return None

def check_ffmpeg():
    try:
        subprocess.run(['ffmpeg','-version'], capture_output=True, timeout=10)
        print("✅ ffmpeg found.")
    except Exception:
        print("⚠️  ffmpeg not found — add 'sudo apt-get install -y ffmpeg' to workflow.")

def _duration_ok(duration_sec, min_s, max_s, label=""):
    if duration_sec is None: return True
    d = int(duration_sec)
    if min_s is not None and d < min_s:
        print(f"   ⏩ {label}: {d}s < min {min_s}s — skipped."); return False
    if max_s is not None and d > max_s:
        print(f"   ⏩ {label}: {d}s > max {max_s}s — skipped."); return False
    return True


# ───────────────────────── rate-limit cooldown ───────────────────────────────
# Shared across all worker threads: if several workers get rate-limited close
# together, every thread pauses instead of hammering Twitter further.

def _maybe_wait_for_cooldown():
    with _state_lock:
        until = _cooldown_until
    now = time.time()
    if now < until:
        wait = until - now
        print(f"   🧊 Cooldown active — waiting {wait:.0f}s before continuing...")
        time.sleep(wait)

def _register_rate_limit_event():
    global _consecutive_rl, _cooldown_until
    with _state_lock:
        _consecutive_rl += 1
        if _consecutive_rl >= COOLDOWN_TRIGGER:
            _cooldown_until = time.time() + COOLDOWN_SECONDS
            _consecutive_rl = 0
            print(f"\n🧊 Rate-limit threshold reached — {COOLDOWN_SECONDS}s cooldown engaged for all workers.\n")

def _register_success_event():
    global _consecutive_rl
    with _state_lock:
        _consecutive_rl = 0


# ─────────────────── status cache (monkeypatch) ─────────────────────────────

_STATUS_CACHE: dict = {}

def _install_status_cache_patch():
    from yt_dlp.extractor.twitter import TwitterIE
    if getattr(TwitterIE, "_status_cache_patched", False): return
    original = TwitterIE._extract_status
    def patched(self, twid, *args, **kwargs):
        status = original(self, twid, *args, **kwargs)
        if status:
            with _cache_lock:
                _STATUS_CACHE[twid] = status
        return status
    TwitterIE._extract_status = patched
    TwitterIE._status_cache_patched = True

def _get_media_from_status(twid):
    with _cache_lock:
        status = _STATUS_CACHE.get(twid)
    if status is None: return None, None
    photos, has_video = [], False
    for m in (status.get("extended_entities", {}).get("media") or []):
        t = m.get("type", "")
        if t == "photo":
            u = m.get("media_url_https") or m.get("media_url")
            if u: photos.append(u)
        elif t in ("video", "animated_gif"):
            has_video = True
    return photos, has_video

def _pop_status_cache(twid):
    if not twid: return
    with _cache_lock:
        _STATUS_CACHE.pop(twid, None)


# ─────────────────── image download ─────────────────────────────────────────

def download_image(url, dest_dir, base_name, idx, total):
    os.makedirs(dest_dir, exist_ok=True)
    parsed = urlparse(url)
    ext = os.path.splitext(parsed.path)[1].lstrip('.').lower() or "jpg"
    if ext not in ("jpg","jpeg","png","webp","gif"): ext = "jpg"
    if "pbs.twimg.com" in url:
        qp = [(k,v) for k,v in parse_qsl(parsed.query) if k != "name"]
        qp.append(("name","orig"))
        url = urlunparse(parsed._replace(query=urlencode(qp)))
    name = base_name if total == 1 else f"{base_name}_img{idx}"
    fp = unique_path(dest_dir, name, ext)
    resp = requests.get(url, timeout=30, stream=True); resp.raise_for_status()
    with open(fp, "wb") as f:
        for chunk in resp.iter_content(chunk_size=1<<16):
            if chunk: f.write(chunk)
    return fp

def download_images_for_tweet(url, twid, title=None, upload_date=None, uploader=None):
    photos, _ = _get_media_from_status(twid)
    if photos is None:
        print(f"   ⚠️  No cached status for {twid}."); return False, []
    if not photos:
        print(f"   ℹ️  No photo media for {twid}."); return False, []
    print(f"   🖼️  {len(photos)} photo(s) found, downloading...")
    base_name = build_base_name(title, twid, upload_date, uploader)
    fps = []
    for idx, photo_url in enumerate(photos, 1):
        try:
            fp = download_image(photo_url, DOWNLOAD_DIR, base_name, idx, len(photos))
            fps.append(fp); print(f"   ✅ Image {idx}: {os.path.basename(fp)}")
        except requests.exceptions.RequestException as e:
            print(f"   ⚠️  Image {idx} failed: {str(e)[:100]}")
    return len(fps) > 0, fps


# ─────────────────── yt-dlp options ─────────────────────────────────────────

def _ydl_extract_opts(cookiefile):
    return {
        'quiet': True, 'no_warnings': True,
        'nocheckcertificate': True, 'cookiefile': cookiefile,
        'skip_download': True,
    }

def _ydl_download_opts(cookiefile, max_seconds, base_name):
    """
    Three layers of size/duration enforcement:
    1. progress_hook  — fires every chunk, aborts when downloaded bytes > SIZE_LIMIT
    2. max_fragments  — hard fragment cap for HLS livestreams (~2s per fragment)
    3. match_filter   — rejects before download if filesize/duration known upfront
    concurrent_fragments=1 is required so progress_hook byte count is accurate.

    outtmpl uses the final {title}_{id}_{date} name directly, so the file is
    saved with the right name from the start — no rename step afterward.
    """

    def _progress_hook(d):
        if d.get('status') == 'downloading':
            downloaded = d.get('downloaded_bytes', 0)
            if downloaded and downloaded > SIZE_LIMIT:
                raise yt_dlp.utils.DownloadError(
                    f"SIZELIMIT: {downloaded/1e6:.1f}MB exceeds {SIZE_LIMIT/1e6:.0f}MB cap"
                )

    opts = {
        'format': 'bestvideo[ext=mp4]+bestaudio[ext=m4a]/best[ext=mp4]/best',
        'outtmpl': os.path.join(DOWNLOAD_DIR, f'{base_name}.%(ext)s'),
        'merge_output_format': 'mp4',
        'restrictfilenames': True,
        'ignoreerrors': False,
        'cookiefile': cookiefile,
        'nocheckcertificate': True,
        'concurrent_fragments': 1,   # must be 1 for accurate progress_hook byte count
        'retries': 3,
        'quiet': False,
        'no_warnings': True,
        'max_filesize': SIZE_LIMIT,
        'progress_hooks': [_progress_hook],
    }

    if max_seconds:
        frag_limit = int((max_seconds / 2) * 1.25) + 5
        opts['max_fragments'] = frag_limit
        print(f"   🔒 Limits: max_fragments={frag_limit}, max_filesize={SIZE_LIMIT//1_048_576}MB, progress_hook active")
    else:
        print(f"   🔒 Limits: max_filesize={SIZE_LIMIT//1_048_576}MB, progress_hook active")

    def _match_filter(info, *, incomplete):
        fs = info.get('filesize') or info.get('filesize_approx')
        if fs and fs > SIZE_LIMIT:
            return f"SIZELIMIT: filesize {fs/1e6:.0f}MB > {SIZE_LIMIT/1e6:.0f}MB limit"
        dur = info.get('duration')
        if dur and max_seconds and int(dur) > max_seconds:
            return f"duration {int(dur)}s > max {max_seconds}s"
        return None

    opts['match_filter'] = _match_filter
    return opts


# ─────────────────── core download ──────────────────────────────────────────

def download_one(url, cookiefile, min_seconds, max_seconds):
    """Returns (kind, success, was_rate_limited, filepaths)."""
    twid  = extract_tweet_id(url)
    delay = RETRY_BASE_DELAY

    for attempt in range(1, MAX_RETRIES + 1):
        _maybe_wait_for_cooldown()

        # ── 1. Extract metadata ──────────────────────────────────────────
        try:
            with yt_dlp.YoutubeDL(_ydl_extract_opts(cookiefile)) as ydl:
                info = ydl.extract_info(url, download=False)
        except Exception as e:
            raw = str(e); low = raw.lower()
            # Hard non-transient failure — try image cache before giving up
            if not any(p in low for p in TRANSIENT_PHRASES):
                print(f"   ⚠️  extract_info failed: {raw[:120]}")
                if twid:
                    ok, fps = download_images_for_tweet(url, twid)
                    if ok:
                        append_downloaded(url, f"[{len(fps)} image(s)]")
                        _pop_status_cache(twid)
                        return 'image', True, False, fps
                append_failed(url, raw[:200])
                _pop_status_cache(twid)
                return 'none', False, False, []
            if attempt >= MAX_RETRIES:
                append_failed(url, raw[:200])
                _pop_status_cache(twid)
                return 'none', False, True, []
            print(f"   ⚠️  Attempt {attempt}/{MAX_RETRIES}: {raw[:80]} — retry in {delay}s")
            time.sleep(delay); delay = min(delay*2, RETRY_MAX_DELAY); continue

        title       = (info or {}).get('title', url) if info else url
        video_id    = (info or {}).get('id', 'unknown') if info else 'unknown'
        upload_date = (info or {}).get('upload_date') if info else None
        uploader    = ((info or {}).get('uploader') or (info or {}).get('uploader_id')) if info else None
        base_name   = build_base_name(title, twid or video_id, upload_date, uploader)
        label       = f"{title[:55]} [{video_id}]"

        # ── 2. Photo-only check (no video attempt at all) ────────────────
        if twid:
            photos, has_video = _get_media_from_status(twid)
            if photos and not has_video:
                print(f"   🖼️  Photo-only tweet: {label}")
                ok, fps = download_images_for_tweet(url, twid, title, upload_date, uploader)
                if ok: append_downloaded(url, f"{title} [{len(fps)} image(s)]")
                _pop_status_cache(twid)
                return ('image', True, False, fps) if ok else ('none', False, False, [])

        # ── 3. No video formats — try image fallback ─────────────────────
        if not info or not info.get('formats'):
            print(f"   ℹ️  No video formats — trying cached images...")
            if twid:
                ok, fps = download_images_for_tweet(url, twid, title, upload_date, uploader)
                if ok:
                    append_downloaded(url, f"{title} [{len(fps)} image(s)]")
                    _pop_status_cache(twid)
                    return 'image', True, False, fps
            append_failed(url, "no formats, no images")
            _pop_status_cache(twid)
            return 'none', False, False, []

        # ── 4. Metadata duration check (fast path) ───────────────────────
        duration = info.get('duration')
        if duration is not None:
            if not _duration_ok(duration, min_seconds, max_seconds, label):
                append_failed(url, f"duration {int(duration)}s out of range")
                _pop_status_cache(twid)
                return 'none', False, False, []
            print(f"   ⬇️  Downloading ({int(duration)}s): {label}")
        else:
            if max_seconds:
                frag_cap = int((max_seconds / 2) * 1.25) + 5
                print(f"   ⚠️  Duration unknown (livestream/VOD). "
                      f"Enforcing via fragment cap ({frag_cap}) + size hook.")
            print(f"   ⬇️  Downloading (duration unknown): {label}")

        # ── 5. Download ──────────────────────────────────────────────────
        dl_opts = _ydl_download_opts(cookiefile, max_seconds, base_name)
        try:
            with yt_dlp.YoutubeDL(dl_opts) as ydl_dl:
                result = ydl_dl.extract_info(url, download=True)

            if result is None:
                print(f"   ⏩ Rejected by filter before download.")
                append_failed(url, "rejected by match_filter")
                _pop_status_cache(twid)
                return 'none', False, False, []

            filepath = ydl_dl.prepare_filename(result)
            mp4 = os.path.splitext(filepath)[0] + ".mp4"
            if os.path.exists(mp4): filepath = mp4
            if not os.path.exists(filepath):
                # fall back to locating the file by its final base name
                for fn in os.listdir(DOWNLOAD_DIR):
                    if fn.startswith(base_name + "."):
                        filepath = os.path.join(DOWNLOAD_DIR, fn); break

        except yt_dlp.utils.MaxDownloadsReached:
            print(f"   ⏩ Aborted: fragment limit reached.")
            append_failed(url, "fragment limit reached — too long/large")
            _pop_status_cache(twid)
            return 'none', False, False, []

        except Exception as e:
            raw = str(e); low = raw.lower()

            # Size / fragment / duration limit hit — fail immediately, NO retry
            if any(k in low for k in LIMIT_PHRASES):
                print(f"   ⏩ Skipping permanently (size/duration limit): {raw[:120]}")
                append_failed(url, raw[:120])
                _pop_status_cache(twid)
                return 'none', False, False, []

            # Transient error — retry
            is_transient = any(p in low for p in TRANSIENT_PHRASES)
            if attempt < MAX_RETRIES and is_transient:
                print(f"   ⚠️  Download attempt {attempt} failed: {raw[:80]} — retry in {delay}s")
                time.sleep(delay); delay = min(delay*2, RETRY_MAX_DELAY); continue

            append_failed(url, raw[:200])
            _pop_status_cache(twid)
            return 'none', False, is_transient, []

        # ── 6. ffprobe post-download check ───────────────────────────────
        if os.path.exists(filepath):
            actual = ffprobe_duration(filepath)
            if actual is not None:
                print(f"   🔍 ffprobe: {int(actual)}s actual duration")
                if not _duration_ok(actual, min_seconds, max_seconds, f"{label} (actual)"):
                    print(f"   🗑️  Deleting out-of-range file.")
                    os.remove(filepath)
                    append_failed(url, f"actual duration {int(actual)}s out of range")
                    _pop_status_cache(twid)
                    return 'none', False, False, []
            else:
                print(f"   ⚠️  ffprobe couldn't read duration — keeping file.")

            # File size sanity check after download
            file_size = os.path.getsize(filepath)
            if file_size > SIZE_LIMIT:
                print(f"   🗑️  File {file_size/1e6:.1f}MB exceeds {SIZE_LIMIT/1e6:.0f}MB — deleting.")
                os.remove(filepath)
                append_failed(url, f"file {file_size/1e6:.1f}MB > size limit")
                _pop_status_cache(twid)
                return 'none', False, False, []
        else:
            print(f"   ⚠️  File not found after download: {filepath}")
            append_failed(url, "file missing after download")
            _pop_status_cache(twid)
            return 'none', False, False, []

        append_downloaded(url, title)
        print(f"   ✅ Saved: {os.path.basename(filepath)} ({os.path.getsize(filepath)/1e6:.1f}MB)")
        _pop_status_cache(twid)
        return 'video', True, False, [filepath]

    append_failed(url, "max retries exceeded")
    _pop_status_cache(twid)
    return 'none', False, True, []


# ─────────────────── run loop (concurrent) ───────────────────────────────────

def run_downloads(urls, min_seconds, max_seconds, delay_seconds, downloaded_ids, downloaded_urls, concurrency=3):
    os.makedirs(DOWNLOAD_DIR, exist_ok=True)
    _install_status_cache_patch()
    check_ffmpeg()

    cookiefile = COOKIES_PATH if (
        os.path.exists(COOKIES_PATH) and os.path.getsize(COOKIES_PATH) > 100
    ) else None
    if not cookiefile:
        print("⚠️  cookies.txt not found — age-restricted tweets may fail.")

    stats = {'success_video':0,'success_image':0,'skipped':0,'failed':0,'duplicates':0}
    new_files = []
    stats_lock = threading.Lock()
    sets_lock  = threading.Lock()
    files_lock = threading.Lock()

    pending = []
    for raw_url in urls:
        url = normalize_tweet_url(raw_url)
        tid = extract_tweet_id(url)
        if url in downloaded_urls or (tid and tid in downloaded_ids):
            stats['duplicates'] += 1; stats['skipped'] += 1
            continue
        pending.append(url)

    if not pending:
        return stats, new_files

    print(f"\n🚀 Processing {len(pending)} URL(s) with concurrency={concurrency}...")

    stagger = max(0.0, delay_seconds / max(concurrency, 1))

    def worker(idx, url):
        if stagger > 0:
            time.sleep(idx * stagger)
        tid = extract_tweet_id(url)
        print(f"\n[{idx+1}/{len(pending)}] {url}")
        kind, ok, rate_limited, fps = download_one(url, cookiefile, min_seconds, max_seconds)

        with stats_lock:
            if ok:
                stats['success_video' if kind == 'video' else 'success_image'] += 1
            elif rate_limited:
                stats['failed'] += 1
            else:
                stats['skipped'] += 1

        if ok:
            with sets_lock:
                downloaded_urls.add(url)
                if tid: downloaded_ids.add(tid)
            with files_lock:
                for fp in fps:
                    if fp and os.path.exists(fp): new_files.append(fp)
            _register_success_event()

        if rate_limited:
            _register_rate_limit_event()

    with ThreadPoolExecutor(max_workers=max(1, concurrency)) as ex:
        futures = [ex.submit(worker, i, u) for i, u in enumerate(pending)]
        for fut in as_completed(futures):
            exc = fut.exception()
            if exc:
                print(f"   ⚠️  Worker crashed: {exc}")

    return stats, new_files


# ─────────────────── Google Drive ────────────────────────────────────────────

_thread_local = threading.local()

def get_drive_service():
    import json as _json
    from google.oauth2.credentials import Credentials
    from google.auth.transport.requests import Request
    from googleapiclient.discovery import build
    raw = os.environ.get("GDRIVE_TOKEN_JSON")
    if not raw: raise RuntimeError("Missing GDRIVE_TOKEN_JSON env var.")
    info = _json.loads(raw)
    creds = Credentials(
        token=info.get("token"), refresh_token=info["refresh_token"],
        client_id=info["client_id"], client_secret=info["client_secret"],
        token_uri=info.get("token_uri","https://oauth2.googleapis.com/token"),
        scopes=info.get("scopes",["https://www.googleapis.com/auth/drive"]),
    )
    creds.refresh(Request())
    return build("drive","v3",credentials=creds, cache_discovery=False)

def _thread_drive_service():
    """A shared googleapiclient service object is NOT safe to call from
    multiple threads at once, so each worker thread gets its own instance."""
    if not hasattr(_thread_local, "service"):
        _thread_local.service = get_drive_service()
    return _thread_local.service

def create_drive_folder(service, folder_name):
    meta = {"name":folder_name,"mimeType":"application/vnd.google-apps.folder"}
    f = service.files().create(body=meta, fields="id, webViewLink").execute()
    return f["id"], f.get("webViewLink")

def upload_files_to_folder(folder_id, filepaths, concurrency=4):
    """Uploads every file (images AND videos) to the given Drive folder,
    in parallel. A failure on one file no longer blocks the rest."""
    from googleapiclient.http import MediaFileUpload

    uploaded, failed = [], []
    lock = threading.Lock()

    def _upload_one(fp):
        name = os.path.basename(fp)
        try:
            svc = _thread_drive_service()
            print(f"   ☁️  Uploading: {name}")
            f = svc.files().create(
                body={"name":name,"parents":[folder_id]},
                media_body=MediaFileUpload(fp, resumable=True),
                fields="id, name").execute()
            with lock:
                uploaded.append(f["name"])
            print(f"   ✅ Uploaded: {name}")
        except Exception as e:
            with lock:
                failed.append((name, str(e)[:150]))
            print(f"   ⚠️  Upload failed for {name}: {str(e)[:150]}")

    with ThreadPoolExecutor(max_workers=max(1, concurrency)) as ex:
        list(ex.map(_upload_one, filepaths))

    if failed:
        print(f"\n⚠️  {len(failed)} file(s) failed to upload:")
        for n, e in failed:
            print(f"   - {n}: {e}")

    return uploaded, failed


# ─────────────────── main ────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--folder-name", required=True)
    parser.add_argument("--min-duration", default="")
    parser.add_argument("--max-duration", default="")
    parser.add_argument("--delay", default="2",
                         help="Base stagger (seconds) used to spread out worker start times.")
    parser.add_argument("--concurrency", default="3",
                         help="How many tweets to download in parallel.")
    parser.add_argument("--upload-concurrency", default="4",
                         help="How many files to upload to Drive in parallel.")
    args = parser.parse_args()

    folder_name   = (
        "".join(c for c in args.folder_name.strip() if c.isalnum() or c in (' ','-','_')).strip()
        or "downloads"
    )
    min_seconds        = parse_duration(args.min_duration)
    max_seconds         = parse_duration(args.max_duration)
    delay_seconds        = parse_duration(args.delay) or 2
    concurrency          = max(1, int(parse_duration(args.concurrency) or 3))
    upload_concurrency   = max(1, int(parse_duration(args.upload_concurrency) or 4))

    # ── Early exit: no URLs file ─────────────────────────────────────────
    if not os.path.exists(URLS_FILE):
        print(f"❌ {URLS_FILE} not found.")
        sys.exit(1)

    with open(URLS_FILE,"r",encoding="utf-8") as f:
        raw_urls = [u.strip() for u in f if u.strip() and not u.startswith('#')]

    # ── Early exit: file is empty ────────────────────────────────────────
    if not raw_urls:
        print("✅ urlsnow.txt is empty — nothing to do. Exiting.")
        sys.exit(0)

    urls, dupes = dedupe_preserve_order(raw_urls)
    if dupes:
        print(f"🔁 Removed {len(dupes)} duplicate(s) from urlsnow.txt.")

    # ── Early exit: everything already downloaded ────────────────────────
    downloaded_ids, downloaded_urls = load_downloaded_set()
    pending = [
        u for u in urls
        if normalize_tweet_url(u) not in downloaded_urls
        and (not extract_tweet_id(u) or extract_tweet_id(u) not in downloaded_ids)
    ]
    if not pending:
        print("✅ All URLs already downloaded — nothing to do. Exiting.")
        sys.exit(0)

    print(f"\nStarting: {len(pending)} URL(s) pending | folder='{folder_name}' | "
          f"min={min_seconds}s | max={max_seconds}s | stagger={delay_seconds}s | "
          f"concurrency={concurrency} | size_limit={SIZE_LIMIT//1_048_576}MB\n")

    t0 = time.time()
    stats, new_files = run_downloads(
        urls, min_seconds, max_seconds, delay_seconds,
        downloaded_ids, downloaded_urls, concurrency=concurrency
    )
    elapsed = time.time() - t0

    print(f"\n📊 Summary: videos={stats['success_video']} images={stats['success_image']} "
          f"skipped={stats['skipped']} failed={stats['failed']} dupes={stats['duplicates']} "
          f"| took {elapsed:.0f}s")

    summary_path = os.environ.get("GITHUB_STEP_SUMMARY")

    # ── Early exit: nothing downloaded ──────────────────────────────────
    if not new_files:
        print("✅ No new files downloaded — skipping upload. Exiting.")
        if summary_path:
            with open(summary_path,"a") as f:
                f.write(f"### Run complete — nothing to upload\n\n"
                        f"- Videos: {stats['success_video']}\n"
                        f"- Images: {stats['success_image']}\n"
                        f"- Skipped: {stats['skipped']}\n"
                        f"- Failed: {stats['failed']}\n"
                        f"- Duplicates: {stats['duplicates']}\n")
        sys.exit(0)

    # ── Upload (images AND videos, in parallel) ────────────────────────────
    print(f"\nUploading {len(new_files)} file(s) to Drive folder '{folder_name}'...")
    service = get_drive_service()
    folder_id, folder_link = create_drive_folder(service, folder_name)
    uploaded, failed_uploads = upload_files_to_folder(folder_id, new_files, concurrency=upload_concurrency)

    print(f"\n✅ Uploaded {len(uploaded)}/{len(new_files)} file(s) to '{folder_name}'.")
    if failed_uploads:
        print(f"⚠️  {len(failed_uploads)} file(s) failed to upload — see log above.")
    if folder_link: print(f"🔗 {folder_link}")

    if summary_path:
        with open(summary_path,"a") as f:
            f.write(f"### Run complete\n\n"
                    f"- Videos: {stats['success_video']}\n"
                    f"- Images: {stats['success_image']}\n"
                    f"- Skipped: {stats['skipped']}\n"
                    f"- Failed: {stats['failed']}\n"
                    f"- Duplicates: {stats['duplicates']}\n"
                    f"- Uploaded: {len(uploaded)}/{len(new_files)}\n\n"
                    f"**Drive folder:** [{folder_name}]({folder_link})\n\n"
                    + "\n".join(f"- {n}" for n in uploaded) + "\n")
            if failed_uploads:
                f.write("\n**Upload failures:**\n" + "\n".join(f"- {n}: {e}" for n, e in failed_uploads) + "\n")

if __name__ == "__main__":
    main()

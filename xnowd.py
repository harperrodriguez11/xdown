#!/usr/bin/env python3
"""
xdownload.py
Reads pending tweet/X URLs from a Google Sheet (one tab for images, one for
videos — no more urlsnow.txt). Runs in one of two modes per invocation:

    --mode images   -> only ever attempts photo extraction/download
    --mode videos   -> only ever attempts video extraction/download

Uploads whatever it downloads to Drive, logs {file name, caption, tweet url,
type} into the existing "allmeta" metadata sheet, and writes a per-URL
success/failure row into a "Report" tab on the URLs sheet. That Report tab
is read back in at the start of every run so already-downloaded URLs are
skipped automatically — no local log files, nothing committed to the repo.

Filename pattern for every saved file (image or video):
    {title}_{tweet_id}_{upload_date}.{ext}
If the tweet has no meaningful title, the title is omitted:
    {tweet_id}_{upload_date}.{ext}

Caption handling:
    --include-urls-in-caption      true/false   (default: true)
    --include-hashtags-in-caption  true/false   (default: false)
    --full-caption                 true/false   (default: false — overrides
                                                  the two flags above and
                                                  saves the raw caption as-is)
    In every mode, the tweet's own numeric id is stripped out if it shows up
    as a stray token glued onto the caption text (a known artifact in some
    tweets' raw text field) — full_caption otherwise keeps everything
    (emojis, links, hashtags, formatting) untouched.
"""

import os, re, sys, time, subprocess, argparse, threading
from datetime import datetime
from urllib.parse import urlparse, parse_qsl, urlencode, urlunparse
from concurrent.futures import ThreadPoolExecutor, as_completed

import yt_dlp
import requests

REPO_ROOT      = os.getcwd()
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

NO_MEDIA_PHRASES  = [
    'no video could be found', 'no video formats found', 'no media found',
    "doesn't contain any video", "does not contain any video",
    'no video in this tweet', 'no video url found',
]

GENERIC_TITLE_PLACEHOLDERS = {
    "wataa", "video", "media", "twitter", "x", "tweet", "untitled",
    "watch", "post", "nan", "none", "na",
}

# ─────────────────────── thread-safety primitives ───────────────────────────
_cache_lock  = threading.Lock()
_state_lock  = threading.Lock()
_rename_lock = threading.Lock()

_cooldown_until  = 0.0
_consecutive_rl  = 0


# ─────────────────────────── helpers ────────────────────────────────────────

def _to_bool(s):
    return str(s).strip().lower() in ("1", "true", "yes", "y", "on")

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
    if upload_date and re.match(r'^\d{8}$', str(upload_date)):
        return str(upload_date)
    return datetime.now().strftime("%Y%m%d")

def strip_uploader_prefix(title, uploader):
    if not title:
        return title
    title = title.strip()
    if uploader:
        for candidate in (uploader, uploader.lstrip('@')):
            prefix = f"{candidate} - "
            if title.lower().startswith(prefix.lower()):
                title = title[len(prefix):].strip()
                break
    m = re.match(r'^[\w.]{1,30}\s*-\s+(.*)$', title)
    if m and m.group(1):
        title = m.group(1).strip()
    return title

FS_MAX_FILENAME_BYTES = 255

def build_base_name(title, twid, upload_date, uploader=None, reserved_suffix_len=0):
    date_str = normalize_date_str(upload_date)
    clean_title = strip_uploader_prefix(title, uploader)
    fixed_len = len(f"_{twid}_{date_str}") + reserved_suffix_len + 10
    title_budget = max(FS_MAX_FILENAME_BYTES - fixed_len, 20)
    slug = safe_filename_piece(clean_title, max_len=title_budget, default="")
    check = slug.lower().replace("_", "")
    if not slug or len(check) <= 2 or check in GENERIC_TITLE_PLACEHOLDERS:
        return f"{twid}_{date_str}"
    return f"{slug}_{twid}_{date_str}"

def unique_path(dest_dir, base_name, ext):
    with _rename_lock:
        fp = os.path.join(dest_dir, f"{base_name}.{ext}")
        n = 2
        while os.path.exists(fp):
            fp = os.path.join(dest_dir, f"{base_name}_{n}.{ext}")
            n += 1
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

def get_raw_caption(twid):
    if not twid:
        return ""
    with _cache_lock:
        status = _STATUS_CACHE.get(twid)
    if not status:
        return ""
    candidates = (
        lambda s: s.get('full_text'),
        lambda s: s.get('text'),
        lambda s: (s.get('legacy') or {}).get('full_text'),
        lambda s: (s.get('legacy') or {}).get('text'),
        lambda s: (((s.get('note_tweet') or {}).get('note_tweet_results') or {}).get('result') or {}).get('text'),
    )
    for get in candidates:
        try:
            val = get(status)
            if val:
                return val
        except Exception:
            continue
    return ""

_URL_REGEX     = re.compile(r'https?://\S+')
_HASHTAG_REGEX = re.compile(r'(?<!\w)#\w+')

def process_caption(raw_text, twid=None, include_urls=True, include_hashtags=False, full_caption=False):
    """
    Cleans up a raw tweet caption:
      - full_caption=True   -> kept as-is (links, emojis, hashtags, styling all
                                preserved) EXCEPT the tweet's own numeric id,
                                which is stripped if it shows up glued onto the
                                text with no separator (a raw-text artifact).
      - include_urls=False  -> strips any http(s) links (e.g. t.co links)
      - include_hashtags=False -> strips #hashtag tokens
    """
    text = (raw_text or "").strip()
    if not text:
        return text
    if twid:
        # Never let the tweet/status id leak into the caption as a stray
        # token — regardless of which mode is selected.
        text = re.sub(rf'(?<!\d){re.escape(twid)}(?!\d)', '', text)
    if full_caption:
        text = re.sub(r'[ \t]+', ' ', text)
        return text.strip()
    if not include_urls:
        text = _URL_REGEX.sub('', text)
    if not include_hashtags:
        text = _HASHTAG_REGEX.sub('', text)
    text = re.sub(r'[ \t]+', ' ', text)
    text = re.sub(r'\n\s*\n+', '\n', text)
    return text.strip()


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
    if not photos:
        return False, []
    print(f"   🖼️  {len(photos)} photo(s) found, downloading...")
    suffix_len = len(f"_img{len(photos)}") if len(photos) > 1 else 0
    base_name = build_base_name(title, twid, upload_date, uploader, reserved_suffix_len=suffix_len)
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
        'retries': 0, 'extractor_retries': 0,
    }

def _ydl_download_opts(cookiefile, max_seconds, base_name):
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
        'concurrent_fragments': 1,
        'retries': 3,
        'extractor_retries': 0,
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


# ─────────────────── core download (mode-separated) ──────────────────────────

def download_one(url, cookiefile, min_seconds, max_seconds, mode,
                  include_urls=True, include_hashtags=False, full_caption=False):
    """
    mode: 'images' -> only ever attempts photo extraction/download.
          'videos' -> only ever attempts video extraction/download.
    Returns (kind, success, was_rate_limited, filepaths, caption).
    """
    twid  = extract_tweet_id(url)
    delay = RETRY_BASE_DELAY
    caption = ""

    for attempt in range(1, MAX_RETRIES + 1):
        _maybe_wait_for_cooldown()

        # ── 1. Extract metadata ──────────────────────────────────────────
        try:
            with yt_dlp.YoutubeDL(_ydl_extract_opts(cookiefile)) as ydl:
                info = ydl.extract_info(url, download=False)
        except Exception as e:
            raw = str(e); low = raw.lower()
            no_media = any(p in low for p in NO_MEDIA_PHRASES)
            caption = process_caption(get_raw_caption(twid), twid, include_urls, include_hashtags, full_caption) if twid else ""
            if no_media or not any(p in low for p in TRANSIENT_PHRASES):
                if mode == 'images' and twid:
                    ok, fps = download_images_for_tweet(url, twid)
                    _pop_status_cache(twid)
                    if ok:
                        return 'image', True, False, fps, caption
                else:
                    print(f"   ⚠️  extract_info failed: {raw[:120]}")
                _pop_status_cache(twid)
                return 'none', False, False, [], caption
            if attempt >= MAX_RETRIES:
                _pop_status_cache(twid)
                return 'none', False, True, [], caption
            print(f"   ⚠️  Attempt {attempt}/{MAX_RETRIES}: {raw[:80]} — retry in {delay}s")
            time.sleep(delay); delay = min(delay*2, RETRY_MAX_DELAY); continue

        title       = (info or {}).get('title', url) if info else url
        video_id    = (info or {}).get('id', 'unknown') if info else 'unknown'
        upload_date = (info or {}).get('upload_date') if info else None
        uploader    = ((info or {}).get('uploader') or (info or {}).get('uploader_id')) if info else None
        label       = f"{title[:55]} [{video_id}]"
        caption     = process_caption(get_raw_caption(twid), twid, include_urls, include_hashtags, full_caption) if twid else ""

        # ── IMAGES MODE — never attempts a video download ────────────────
        if mode == 'images':
            photos, _has_video = _get_media_from_status(twid) if twid else (None, None)
            if not photos:
                print(f"   ℹ️  No photo media for {label} — skipping.")
                _pop_status_cache(twid)
                return 'none', False, False, [], caption
            ok, fps = download_images_for_tweet(url, twid, title, upload_date, uploader)
            _pop_status_cache(twid)
            return ('image', True, False, fps, caption) if ok else ('none', False, False, [], caption)

        # ── VIDEOS MODE — never attempts a photo download ────────────────
        photos, has_video = _get_media_from_status(twid) if twid else (None, False)
        if not has_video and not (info and info.get('formats')):
            print(f"   ℹ️  No video for {label} — skipping.")
            _pop_status_cache(twid)
            return 'none', False, False, [], caption

        base_name = build_base_name(title, twid or video_id, upload_date, uploader)
        duration = info.get('duration') if info else None
        if duration is not None:
            if not _duration_ok(duration, min_seconds, max_seconds, label):
                _pop_status_cache(twid)
                return 'none', False, False, [], caption
            print(f"   ⬇️  Downloading ({int(duration)}s): {label}")
        else:
            if max_seconds:
                frag_cap = int((max_seconds / 2) * 1.25) + 5
                print(f"   ⚠️  Duration unknown. Enforcing via fragment cap ({frag_cap}) + size hook.")
            print(f"   ⬇️  Downloading (duration unknown): {label}")

        dl_opts = _ydl_download_opts(cookiefile, max_seconds, base_name)
        try:
            with yt_dlp.YoutubeDL(dl_opts) as ydl_dl:
                result = ydl_dl.extract_info(url, download=True)

            if result is None:
                print(f"   ⏩ Rejected by filter before download.")
                _pop_status_cache(twid)
                return 'none', False, False, [], caption

            filepath = ydl_dl.prepare_filename(result)
            mp4 = os.path.splitext(filepath)[0] + ".mp4"
            if os.path.exists(mp4): filepath = mp4
            if not os.path.exists(filepath):
                for fn in os.listdir(DOWNLOAD_DIR):
                    if fn.startswith(base_name + "."):
                        filepath = os.path.join(DOWNLOAD_DIR, fn); break

        except yt_dlp.utils.MaxDownloadsReached:
            print(f"   ⏩ Aborted: fragment limit reached.")
            _pop_status_cache(twid)
            return 'none', False, False, [], caption

        except Exception as e:
            raw = str(e); low = raw.lower()

            if any(k in low for k in LIMIT_PHRASES):
                print(f"   ⏩ Skipping permanently (size/duration limit): {raw[:120]}")
                _pop_status_cache(twid)
                return 'none', False, False, [], caption

            if any(p in low for p in NO_MEDIA_PHRASES):
                print(f"   ℹ️  No video available — skipping.")
                _pop_status_cache(twid)
                return 'none', False, False, [], caption

            is_transient = any(p in low for p in TRANSIENT_PHRASES)
            if attempt < MAX_RETRIES and is_transient:
                print(f"   ⚠️  Download attempt {attempt} failed: {raw[:80]} — retry in {delay}s")
                time.sleep(delay); delay = min(delay*2, RETRY_MAX_DELAY); continue

            _pop_status_cache(twid)
            return 'none', False, is_transient, [], caption

        # ── ffprobe post-download check ───────────────────────────────
        if os.path.exists(filepath):
            actual = ffprobe_duration(filepath)
            if actual is not None:
                print(f"   🔍 ffprobe: {int(actual)}s actual duration")
                if not _duration_ok(actual, min_seconds, max_seconds, f"{label} (actual)"):
                    print(f"   🗑️  Deleting out-of-range file.")
                    os.remove(filepath)
                    _pop_status_cache(twid)
                    return 'none', False, False, [], caption
            else:
                print(f"   ⚠️  ffprobe couldn't read duration — keeping file.")

            file_size = os.path.getsize(filepath)
            if file_size > SIZE_LIMIT:
                print(f"   🗑️  File {file_size/1e6:.1f}MB exceeds {SIZE_LIMIT/1e6:.0f}MB — deleting.")
                os.remove(filepath)
                _pop_status_cache(twid)
                return 'none', False, False, [], caption
        else:
            print(f"   ⚠️  File not found after download: {filepath}")
            _pop_status_cache(twid)
            return 'none', False, False, [], caption

        print(f"   ✅ Saved: {os.path.basename(filepath)} ({os.path.getsize(filepath)/1e6:.1f}MB)")
        _pop_status_cache(twid)
        return 'video', True, False, [filepath], caption

    _pop_status_cache(twid)
    return 'none', False, True, [], caption


# ─────────────────── run loop (concurrent) ───────────────────────────────────

def run_downloads(urls, min_seconds, max_seconds, delay_seconds, mode, already_done,
                   concurrency=3, include_urls=True, include_hashtags=False, full_caption=False):
    os.makedirs(DOWNLOAD_DIR, exist_ok=True)
    _install_status_cache_patch()
    check_ffmpeg()

    cookiefile = COOKIES_PATH if (
        os.path.exists(COOKIES_PATH) and os.path.getsize(COOKIES_PATH) > 100
    ) else None
    if not cookiefile:
        print("⚠️  cookies.txt not found — age-restricted tweets may fail.")

    stats = {'success': 0, 'skipped': 0, 'failed': 0, 'duplicates': 0}
    new_files = []
    file_meta = []    # for the metadata ("allmeta") sheet
    report_rows = []  # for the Report tab (success + failed, drives skip logic)
    stats_lock = threading.Lock()
    files_lock = threading.Lock()
    report_lock = threading.Lock()

    pending = []
    for raw_url in urls:
        url = normalize_tweet_url(raw_url)
        if url in already_done:
            stats['duplicates'] += 1; stats['skipped'] += 1
            continue
        pending.append(url)

    if not pending:
        return stats, new_files, file_meta, report_rows

    print(f"\n🚀 Processing {len(pending)} {mode} URL(s) with concurrency={concurrency}...")
    stagger = max(0.0, delay_seconds / max(concurrency, 1))
    singular_type = "image" if mode == "images" else "video"

    def worker(idx, url):
        if stagger > 0:
            time.sleep(idx * stagger)
        print(f"\n[{idx+1}/{len(pending)}] {url}")
        kind, ok, rate_limited, fps, caption = download_one(
            url, cookiefile, min_seconds, max_seconds, mode,
            include_urls=include_urls, include_hashtags=include_hashtags, full_caption=full_caption
        )
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

        with stats_lock:
            if ok: stats['success'] += 1
            elif rate_limited: stats['failed'] += 1
            else: stats['skipped'] += 1

        if ok:
            with files_lock:
                for fp in fps:
                    if fp and os.path.exists(fp):
                        new_files.append(fp)
                        file_meta.append({
                            'filepath': fp, 'name': os.path.basename(fp),
                            'caption': caption, 'url': url, 'kind': kind,
                        })
            with report_lock:
                for fp in fps:
                    if fp and os.path.exists(fp):
                        report_rows.append([url, kind, "success", os.path.basename(fp), caption, ts])
            _register_success_event()
        else:
            with report_lock:
                report_rows.append([url, singular_type, "failed", "", caption, ts])

        if rate_limited:
            _register_rate_limit_event()

    with ThreadPoolExecutor(max_workers=max(1, concurrency)) as ex:
        futures = [ex.submit(worker, i, u) for i, u in enumerate(pending)]
        for fut in as_completed(futures):
            exc = fut.exception()
            if exc:
                print(f"   ⚠️  Worker crashed: {exc}")

    return stats, new_files, file_meta, report_rows


# ─────────────────── Google Drive ────────────────────────────────────────────

_thread_local = threading.local()

def _load_google_creds():
    import json as _json
    from google.oauth2.credentials import Credentials
    from google.auth.transport.requests import Request
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
    return creds

def get_drive_service():
    from googleapiclient.discovery import build
    return build("drive","v3",credentials=_load_google_creds(), cache_discovery=False)

def get_sheets_service():
    """Reuses the same GDRIVE_TOKEN_JSON credentials as Drive (must include the
    spreadsheets scope, or the broad drive scope which covers Sheets too)."""
    from googleapiclient.discovery import build
    return build("sheets","v4",credentials=_load_google_creds(), cache_discovery=False)

def _thread_drive_service():
    if not hasattr(_thread_local, "service"):
        _thread_local.service = get_drive_service()
    return _thread_local.service

def create_drive_folder(service, folder_name):
    meta = {"name":folder_name,"mimeType":"application/vnd.google-apps.folder"}
    f = service.files().create(body=meta, fields="id, webViewLink").execute()
    return f["id"], f.get("webViewLink")

def upload_files_to_folder(folder_id, filepaths, concurrency=4):
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

    return set(uploaded), failed


# ─────────────────── Google Sheets — URL lists + report + metadata ──────────

# Sheet holding the pending URL lists ("Images" / "Videos" tabs) and the
# "Report" tab (success/failed log used to skip already-processed URLs).
# https://docs.google.com/spreadsheets/d/17PZy32Hmr504A7gVkGoH0OMJSQPd1oZVtaVp6Cyu74Y/edit
URLS_SHEET_ID = "17PZy32Hmr504A7gVkGoH0OMJSQPd1oZVtaVp6Cyu74Y"

# Fixed metadata log sheet — {file name, caption, tweet url, type} for every
# uploaded file. We always write into this existing sheet, never create a new one.
# https://docs.google.com/spreadsheets/d/12KXL16nrcpsPXCrtycvt9it-irK4vPjJQm4anAILNFk/edit
DEFAULT_SHEET_ID = "12KXL16nrcpsPXCrtycvt9it-irK4vPjJQm4anAILNFk"

URLS_SHEET_TABS = {"images": "Images", "videos": "Videos"}
REPORT_TAB      = "Report"
REPORT_HEADER   = ["Tweet URL", "Type", "Status", "File Name", "Caption", "Timestamp"]
SHEET_HEADER    = ["File Name", "Caption", "Tweet URL", "Type"]


def ensure_tab_exists(sheets_service, spreadsheet_id, tab_name, header=None):
    """Creates the tab if it doesn't exist yet, and writes the header row if
    the tab is empty. Safe to call every run."""
    meta = sheets_service.spreadsheets().get(
        spreadsheetId=spreadsheet_id, fields="sheets(properties(title))"
    ).execute()
    titles = [s["properties"]["title"] for s in meta.get("sheets", [])]
    if tab_name not in titles:
        sheets_service.spreadsheets().batchUpdate(
            spreadsheetId=spreadsheet_id,
            body={"requests": [{"addSheet": {"properties": {"title": tab_name}}}]}
        ).execute()
        print(f"   ➕ Created missing tab '{tab_name}'.")
    if header:
        last_col = chr(ord('A') + len(header) - 1)
        result = sheets_service.spreadsheets().values().get(
            spreadsheetId=spreadsheet_id, range=f"'{tab_name}'!A1:{last_col}1"
        ).execute()
        if not result.get("values"):
            sheets_service.spreadsheets().values().update(
                spreadsheetId=spreadsheet_id, range=f"'{tab_name}'!A1",
                valueInputOption="RAW", body={"values": [header]}
            ).execute()

def read_pending_urls(sheets_service, sheet_id, tab_name):
    try:
        result = sheets_service.spreadsheets().values().get(
            spreadsheetId=sheet_id, range=f"'{tab_name}'!A2:A"
        ).execute()
    except Exception as e:
        print(f"⚠️  Could not read '{tab_name}' tab: {str(e)[:200]}")
        return []
    values = result.get("values", [])
    return [row[0].strip() for row in values if row and row[0].strip()]

def read_report_status(sheets_service, sheet_id, tab_name=REPORT_TAB):
    """Returns the set of tweet URLs already logged as 'success' in the
    Report tab, so this run can skip them."""
    try:
        result = sheets_service.spreadsheets().values().get(
            spreadsheetId=sheet_id, range=f"'{tab_name}'!A2:F"
        ).execute()
    except Exception as e:
        print(f"⚠️  Could not read '{tab_name}' tab: {str(e)[:200]}")
        return set()
    values = result.get("values", [])
    done = set()
    for row in values:
        if len(row) >= 3 and row[2].strip().lower() == "success":
            done.add(normalize_tweet_url(row[0].strip()))
    return done

def append_report_rows(sheets_service, sheet_id, tab_name, rows):
    if not rows: return
    sheets_service.spreadsheets().values().append(
        spreadsheetId=sheet_id, range=f"'{tab_name}'!A1",
        valueInputOption="RAW", insertDataOption="INSERT_ROWS",
        body={"values": rows}
    ).execute()

def get_spreadsheet_info(sheets_service, spreadsheet_id):
    meta = sheets_service.spreadsheets().get(
        spreadsheetId=spreadsheet_id,
        fields="spreadsheetUrl,sheets(properties(title))"
    ).execute()
    sheets = meta.get("sheets", [])
    tab_name = sheets[0]["properties"]["title"] if sheets else "Sheet1"
    return tab_name, meta.get("spreadsheetUrl")

def ensure_sheet_header(sheets_service, spreadsheet_id, tab_name):
    result = sheets_service.spreadsheets().values().get(
        spreadsheetId=spreadsheet_id, range=f"'{tab_name}'!A1:D1"
    ).execute()
    if not result.get("values"):
        sheets_service.spreadsheets().values().update(
            spreadsheetId=spreadsheet_id, range=f"'{tab_name}'!A1",
            valueInputOption="RAW",
            body={"values": [SHEET_HEADER]}
        ).execute()

def append_rows_to_sheet(sheets_service, spreadsheet_id, tab_name, rows):
    if not rows: return
    sheets_service.spreadsheets().values().append(
        spreadsheetId=spreadsheet_id, range=f"'{tab_name}'!A1",
        valueInputOption="RAW", insertDataOption="INSERT_ROWS",
        body={"values": rows}
    ).execute()


# ─────────────────── main ────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", required=True, choices=["images", "videos"],
                         help="Only download images, or only download videos.")
    parser.add_argument("--folder-name", required=True)
    parser.add_argument("--min-duration", default="")
    parser.add_argument("--max-duration", default="")
    parser.add_argument("--delay", default="2",
                         help="Base stagger (seconds) used to spread out worker start times.")
    parser.add_argument("--concurrency", default="3",
                         help="How many tweets to download in parallel.")
    parser.add_argument("--upload-concurrency", default="4",
                         help="How many files to upload to Drive in parallel.")
    parser.add_argument("--urls-sheet-id", default=URLS_SHEET_ID,
                         help="Spreadsheet ID holding the 'Images'/'Videos' pending-URL tabs and the 'Report' tab.")
    parser.add_argument("--meta-sheet-id", default=DEFAULT_SHEET_ID,
                         help="Spreadsheet ID to log {file name, caption, url, type} into for every uploaded file.")
    parser.add_argument("--include-urls-in-caption", default="true")
    parser.add_argument("--include-hashtags-in-caption", default="false")
    parser.add_argument("--full-caption", default="false")
    args = parser.parse_args()

    folder_name = (
        "".join(c for c in args.folder_name.strip() if c.isalnum() or c in (' ','-','_')).strip()
        or "downloads"
    )
    min_seconds        = parse_duration(args.min_duration)
    max_seconds        = parse_duration(args.max_duration)
    delay_seconds       = parse_duration(args.delay) or 2
    concurrency         = max(1, int(parse_duration(args.concurrency) or 3))
    upload_concurrency  = max(1, int(parse_duration(args.upload_concurrency) or 4))

    include_urls     = _to_bool(args.include_urls_in_caption)
    include_hashtags = _to_bool(args.include_hashtags_in_caption)
    full_caption      = _to_bool(args.full_caption)
    urls_sheet_id     = args.urls_sheet_id.strip() or URLS_SHEET_ID
    meta_sheet_id      = args.meta_sheet_id.strip() or DEFAULT_SHEET_ID
    mode               = args.mode

    caption_mode = "FULL (raw, minus stray tweet id)" if full_caption else \
        f"urls={'on' if include_urls else 'off'}, hashtags={'on' if include_hashtags else 'off'}"
    print(f"📝 Mode: {mode} | Caption: {caption_mode} | URLs sheet: {urls_sheet_id} | Meta sheet: {meta_sheet_id}")

    sheets_service = get_sheets_service()
    tab_name = URLS_SHEET_TABS[mode]
    ensure_tab_exists(sheets_service, urls_sheet_id, tab_name, header=["Tweet URL"])
    ensure_tab_exists(sheets_service, urls_sheet_id, REPORT_TAB, header=REPORT_HEADER)

    raw_urls = read_pending_urls(sheets_service, urls_sheet_id, tab_name)
    if not raw_urls:
        print(f"✅ '{tab_name}' tab is empty — nothing to do. Exiting.")
        sys.exit(0)

    urls, dupes = dedupe_preserve_order(raw_urls)
    if dupes:
        print(f"🔁 Removed {len(dupes)} duplicate(s) from the '{tab_name}' tab.")

    already_done = read_report_status(sheets_service, urls_sheet_id, REPORT_TAB)
    pending = [u for u in urls if normalize_tweet_url(u) not in already_done]
    if not pending:
        print("✅ All URLs already downloaded per the Report tab — nothing to do. Exiting.")
        sys.exit(0)

    print(f"\nStarting: {len(pending)} URL(s) pending | mode={mode} | folder='{folder_name}' | "
          f"min={min_seconds}s | max={max_seconds}s | stagger={delay_seconds}s | "
          f"concurrency={concurrency} | size_limit={SIZE_LIMIT//1_048_576}MB\n")

    t0 = time.time()
    stats, new_files, file_meta, report_rows = run_downloads(
        urls, min_seconds, max_seconds, delay_seconds, mode, already_done,
        concurrency=concurrency, include_urls=include_urls,
        include_hashtags=include_hashtags, full_caption=full_caption
    )
    elapsed = time.time() - t0

    print(f"\n📊 Summary: success={stats['success']} skipped={stats['skipped']} "
          f"failed={stats['failed']} dupes={stats['duplicates']} | took {elapsed:.0f}s")

    summary_path = os.environ.get("GITHUB_STEP_SUMMARY")

    # ── Always log the report first, so a crash later doesn't cost us the dedupe data ──
    try:
        append_report_rows(sheets_service, urls_sheet_id, REPORT_TAB, report_rows)
        print(f"\n📝 Logged {len(report_rows)} row(s) to '{REPORT_TAB}' tab.")
    except Exception as e:
        print(f"\n⚠️  Report logging failed: {str(e)[:300]}")

    if not new_files:
        print("✅ No new files downloaded — skipping upload. Exiting.")
        if summary_path:
            with open(summary_path,"a") as f:
                f.write(f"### Run complete ({mode}) — nothing to upload\n\n"
                        f"- Success: {stats['success']}\n"
                        f"- Skipped: {stats['skipped']}\n"
                        f"- Failed: {stats['failed']}\n"
                        f"- Duplicates: {stats['duplicates']}\n")
        sys.exit(0)

    # ── Upload ───────────────────────────────────────────────────────────
    print(f"\nUploading {len(new_files)} file(s) to Drive folder '{folder_name}'...")
    service = get_drive_service()
    folder_id, folder_link = create_drive_folder(service, folder_name)
    uploaded_names, failed_uploads = upload_files_to_folder(folder_id, new_files, concurrency=upload_concurrency)

    print(f"\n✅ Uploaded {len(uploaded_names)}/{len(new_files)} file(s) to '{folder_name}'.")
    if failed_uploads:
        print(f"⚠️  {len(failed_uploads)} file(s) failed to upload — see log above.")
    if folder_link: print(f"🔗 {folder_link}")

    # ── Log file name + caption + url + type into the metadata sheet ──────
    meta_link = None
    rows_logged = 0
    try:
        meta_tab, meta_link = get_spreadsheet_info(sheets_service, meta_sheet_id)
        ensure_sheet_header(sheets_service, meta_sheet_id, meta_tab)
        rows = [
            [m['name'], m['caption'], m['url'], m['kind']]
            for m in file_meta
            if m['name'] in uploaded_names
        ]
        append_rows_to_sheet(sheets_service, meta_sheet_id, meta_tab, rows)
        rows_logged = len(rows)
        print(f"\n📝 Logged {rows_logged} row(s) to metadata sheet (tab '{meta_tab}').")
        if meta_link: print(f"🔗 {meta_link}")
    except Exception as e:
        print(f"\n⚠️  Metadata sheet logging failed: {str(e)[:300]}")

    if summary_path:
        with open(summary_path,"a") as f:
            f.write(f"### Run complete ({mode})\n\n"
                    f"- Success: {stats['success']}\n"
                    f"- Skipped: {stats['skipped']}\n"
                    f"- Failed: {stats['failed']}\n"
                    f"- Duplicates: {stats['duplicates']}\n"
                    f"- Uploaded: {len(uploaded_names)}/{len(new_files)}\n"
                    f"- Metadata rows logged: {rows_logged}\n\n"
                    f"**Drive folder:** [{folder_name}]({folder_link})\n\n"
                    + "\n".join(f"- {n}" for n in sorted(uploaded_names)) + "\n")
            if meta_link:
                f.write(f"\n**Metadata sheet:** [{meta_sheet_id}]({meta_link})\n")
            if failed_uploads:
                f.write("\n**Upload failures:**\n" + "\n".join(f"- {n}: {e}" for n, e in failed_uploads) + "\n")

if __name__ == "__main__":
    main()

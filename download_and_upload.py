#!/usr/bin/env python3
"""
download_and_upload.py
Reads tweet/X URLs from urlsnow.txt. Downloads images or videos, enforcing
duration limits even when metadata is missing (livestreams/VODs) via:
  1. Metadata duration check  (fast, before any download)
  2. match_filter + max_filesize  (aborts before/during download)
  3. max_fragments cap  (hard-stops HLS/DASH streams, ~2s per fragment)
  4. ffprobe check after download  (deletes file if out of range)
"""

import os, re, sys, time, subprocess, argparse
from datetime import datetime
from urllib.parse import urlparse, parse_qsl, urlencode, urlunparse

import yt_dlp
import requests

REPO_ROOT    = os.getcwd()
URLS_FILE    = os.path.join(REPO_ROOT, "urlsnow.txt")
DOWNLOADED_LOG = os.path.join(REPO_ROOT, "downloaded_videos.txt")
FAILED_LOG   = os.path.join(REPO_ROOT, "failed_videos.txt")
DOWNLOAD_DIR = os.path.join(REPO_ROOT, "downloads")
COOKIES_PATH = os.path.join(REPO_ROOT, "cookies.txt")

MAX_RETRIES      = 5
RETRY_BASE_DELAY = 8
RETRY_MAX_DELAY  = 90
COOLDOWN_TRIGGER = 4
COOLDOWN_SECONDS = 300

# Used to derive a filesize proxy when duration metadata is absent.
# 375 KB/s ≈ 3 Mbps (typical 720p Twitter video).
BYTES_PER_SECOND = 375_000

RATE_LIMIT_PHRASES = [
    'rate','429','503','temporarily','too many requests','unable to extract',
    'http error 5','reset by peer','connection','timed out','timeout','bad guest token',
]
TRANSIENT_PHRASES = RATE_LIMIT_PHRASES + ['login','log in','auth','age','500','network']


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
    with open(DOWNLOADED_LOG, 'a', encoding='utf-8') as f:
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        f.write(f"{url}\t{title}\t{ts}\n"); f.flush(); os.fsync(f.fileno())

def append_failed(url, reason):
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

def safe_filename_piece(text, max_len=80):
    text = re.sub(r'[^A-Za-z0-9._-]+', '_', text or '')
    text = re.sub(r'_+', '_', text).strip('_')
    return text[:max_len] or "untitled"

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


# ─────────────────── status cache (monkeypatch) ─────────────────────────────

_STATUS_CACHE: dict = {}

def _install_status_cache_patch():
    from yt_dlp.extractor.twitter import TwitterIE
    if getattr(TwitterIE, "_status_cache_patched", False): return
    original = TwitterIE._extract_status
    def patched(self, twid, *args, **kwargs):
        status = original(self, twid, *args, **kwargs)
        if status: _STATUS_CACHE[twid] = status
        return status
    TwitterIE._extract_status = patched
    TwitterIE._status_cache_patched = True

def _get_media_from_status(twid):
    """Returns (photos: list, has_video: bool) or (None, None) if not cached."""
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


# ─────────────────── image download ─────────────────────────────────────────

def download_image(url, dest_dir, basename_hint):
    os.makedirs(dest_dir, exist_ok=True)
    parsed = urlparse(url)
    ext = os.path.splitext(parsed.path)[1].lstrip('.').lower() or "jpg"
    if ext not in ("jpg","jpeg","png","webp","gif"): ext = "jpg"
    if "pbs.twimg.com" in url:
        qp = [(k,v) for k,v in parse_qsl(parsed.query) if k != "name"]
        qp.append(("name","orig"))
        url = urlunparse(parsed._replace(query=urlencode(qp)))
    fp = os.path.join(dest_dir, f"{basename_hint}.{ext}")
    resp = requests.get(url, timeout=30, stream=True); resp.raise_for_status()
    with open(fp, "wb") as f:
        for chunk in resp.iter_content(chunk_size=1<<16):
            if chunk: f.write(chunk)
    return fp

def download_images_for_tweet(url, twid):
    photos, _ = _get_media_from_status(twid)
    if photos is None:
        print(f"   ⚠️  No cached status for {twid}."); return False, []
    if not photos:
        print(f"   ℹ️  No photo media for {twid}."); return False, []
    print(f"   🖼️  {len(photos)} photo(s) found, downloading...")
    fps = []
    for idx, photo_url in enumerate(photos, 1):
        try:
            fp = download_image(photo_url, DOWNLOAD_DIR, safe_filename_piece(f"{twid}_img{idx}"))
            fps.append(fp); print(f"   ✅ Image {idx}: {os.path.basename(fp)}")
        except requests.exceptions.RequestException as e:
            print(f"   ⚠️  Image {idx} failed: {str(e)[:100]}")
    return len(fps) > 0, fps


# ─────────────────── yt-dlp options ─────────────────────────────────────────

def _ydl_extract_opts(cookiefile):
    return {'quiet':True,'no_warnings':True,'nocheckcertificate':True,
            'cookiefile':cookiefile,'skip_download':True}

def _ydl_download_opts(cookiefile, max_seconds):
    SIZE_LIMIT = 40 * 1024 * 1024  # 40 MB

    def _progress_hook(d):
        if d.get('status') == 'downloading':
            downloaded = d.get('downloaded_bytes', 0)
            if downloaded and downloaded > SIZE_LIMIT:
                raise yt_dlp.utils.DownloadError(
                    f"Aborted: downloaded {downloaded/1e6:.1f}MB exceeds 40MB limit"
                )

    opts = {
        'format': 'bestvideo[ext=mp4]+bestaudio[ext=m4a]/best[ext=mp4]/best',
        'outtmpl': os.path.join(
            DOWNLOAD_DIR,
            '%(uploader)s_%(upload_date)s_%(title).60s_[%(id)s].%(ext)s'
        ),
        'merge_output_format': 'mp4',
        'restrictfilenames': True,
        'ignoreerrors': False,
        'cookiefile': cookiefile,
        'nocheckcertificate': True,
        'concurrent_fragments': 1,  # must be 1 so progress_hook byte count is accurate
        'retries': 3,
        'quiet': False,
        'no_warnings': True,
        'max_filesize': SIZE_LIMIT,
        'progress_hooks': [_progress_hook],
    }

    if max_seconds:
        frag_limit = int((max_seconds / 2) * 1.25) + 5
        opts['max_fragments'] = frag_limit
        print(f"   🔒 Limits: max_fragments={frag_limit}, max_filesize=40MB (enforced via progress hook)")
    else:
        print(f"   🔒 Limits: max_filesize=40MB (enforced via progress hook)")

    def _match_filter(info, *, incomplete):
        fs = info.get('filesize') or info.get('filesize_approx')
        if fs and fs > SIZE_LIMIT:
            return f"filesize {fs/1e6:.0f}MB > 40MB limit"
        dur = info.get('duration')
        if dur and max_seconds and int(dur) > max_seconds:
            return f"duration {int(dur)}s > max {max_seconds}s"
        return None

    opts['match_filter'] = _match_filter
    return opts


# ─────────────────── core download ──────────────────────────────────────────

def download_one(url, cookiefile, min_seconds, max_seconds):
    twid  = extract_tweet_id(url)
    delay = RETRY_BASE_DELAY

    for attempt in range(1, MAX_RETRIES + 1):

        # ── 1. Extract metadata ──────────────────────────────────────────
        try:
            with yt_dlp.YoutubeDL(_ydl_extract_opts(cookiefile)) as ydl:
                info = ydl.extract_info(url, download=False)
        except Exception as e:
            raw = str(e); low = raw.lower()
            if not any(p in low for p in TRANSIENT_PHRASES):
                print(f"   ⚠️  extract_info failed: {raw[:120]}")
                if twid:
                    ok, fps = download_images_for_tweet(url, twid)
                    if ok:
                        append_downloaded(url, f"[{len(fps)} image(s)]")
                        _STATUS_CACHE.pop(twid, None)
                        return 'image', True, False, fps
                append_failed(url, raw[:200])
                _STATUS_CACHE.pop(twid, None)
                return 'none', False, False, []
            if attempt >= MAX_RETRIES:
                append_failed(url, raw[:200]); _STATUS_CACHE.pop(twid, None)
                return 'none', False, True, []
            print(f"   ⚠️  Attempt {attempt}/{MAX_RETRIES}: {raw[:80]} — retry in {delay}s")
            time.sleep(delay); delay = min(delay*2, RETRY_MAX_DELAY); continue

        title    = (info or {}).get('title', url) if info else url
        video_id = (info or {}).get('id', 'unknown') if info else 'unknown'
        label    = f"{title[:55]} [{video_id}]"

        # ── 2. Photo-only check ──────────────────────────────────────────
        if twid:
            photos, has_video = _get_media_from_status(twid)
            if photos and not has_video:
                print(f"   🖼️  Photo-only tweet: {label}")
                ok, fps = download_images_for_tweet(url, twid)
                if ok: append_downloaded(url, f"{title} [{len(fps)} image(s)]")
                _STATUS_CACHE.pop(twid, None)
                return ('image', True, False, fps) if ok else ('none', False, False, [])

        # ── 3. No formats at all — try image fallback ────────────────────
        if not info or not info.get('formats'):
            print(f"   ℹ️  No video formats — trying cached images...")
            if twid:
                ok, fps = download_images_for_tweet(url, twid)
                if ok:
                    append_downloaded(url, f"{title} [{len(fps)} image(s)]")
                    _STATUS_CACHE.pop(twid, None)
                    return 'image', True, False, fps
            append_failed(url, "no formats, no images")
            _STATUS_CACHE.pop(twid, None)
            return 'none', False, False, []

        # ── 4. Metadata duration check ───────────────────────────────────
        duration = info.get('duration')
        if duration is not None:
            if not _duration_ok(duration, min_seconds, max_seconds, label):
                _STATUS_CACHE.pop(twid, None); return 'none', False, False, []
            print(f"   ⬇️  Downloading ({int(duration)}s): {label}")
        else:
            # Livestream or VOD — duration unknown.
            # Fragment cap + filesize limit will enforce max_seconds.
            if max_seconds:
                frag_cap = int((max_seconds / 2) * 1.25) + 5
                print(f"   ⚠️  Duration unknown (livestream/VOD). "
                      f"Enforcing via fragment cap ({frag_cap}) + filesize limit.")
            print(f"   ⬇️  Downloading (duration unknown): {label}")

        # ── 5. Download ──────────────────────────────────────────────────
        dl_opts = _ydl_download_opts(cookiefile, max_seconds)
        try:
            with yt_dlp.YoutubeDL(dl_opts) as ydl_dl:
                result = ydl_dl.extract_info(url, download=True)

            if result is None:
                print(f"   ⏩ Download filtered/aborted (duration or size limit).")
                _STATUS_CACHE.pop(twid, None); return 'none', False, False, []

            filepath = ydl_dl.prepare_filename(result)
            mp4 = os.path.splitext(filepath)[0] + ".mp4"
            if os.path.exists(mp4): filepath = mp4
            if not os.path.exists(filepath) and video_id:
                for fn in os.listdir(DOWNLOAD_DIR):
                    if video_id in fn:
                        filepath = os.path.join(DOWNLOAD_DIR, fn); break

        except yt_dlp.utils.MaxDownloadsReached:
            print(f"   ⏩ Aborted: fragment limit reached (duration cap enforced).")
            _STATUS_CACHE.pop(twid, None); return 'none', False, False, []
        except Exception as e:
            raw = str(e); low = raw.lower()
            if any(k in low for k in ('filesize','exceeds','duration','max')):
                print(f"   ⏩ Rejected by filter: {raw[:120]}")
                _STATUS_CACHE.pop(twid, None); return 'none', False, False, []
            is_transient = any(p in low for p in TRANSIENT_PHRASES)
            if attempt < MAX_RETRIES and is_transient:
                print(f"   ⚠️  Download attempt {attempt} failed: {raw[:80]} — retry in {delay}s")
                time.sleep(delay); delay = min(delay*2, RETRY_MAX_DELAY); continue
            append_failed(url, raw[:200]); _STATUS_CACHE.pop(twid, None)
            return 'none', False, is_transient, []

        # ── 6. ffprobe post-download check ──────────────────────────────
        if os.path.exists(filepath):
            actual = ffprobe_duration(filepath)
            if actual is not None:
                print(f"   🔍 ffprobe: {int(actual)}s actual duration")
                if not _duration_ok(actual, min_seconds, max_seconds, f"{label} (actual)"):
                    print(f"   🗑️  Deleting out-of-range file.")
                    os.remove(filepath); _STATUS_CACHE.pop(twid, None)
                    return 'none', False, False, []
            else:
                print(f"   ⚠️  ffprobe couldn't determine duration — keeping file.")
        else:
            print(f"   ⚠️  File not found after download: {filepath}")
            _STATUS_CACHE.pop(twid, None); return 'none', False, False, []

        append_downloaded(url, title)
        print(f"   ✅ Saved: {os.path.basename(filepath)}")
        _STATUS_CACHE.pop(twid, None)
        return 'video', True, False, [filepath]

    append_failed(url, "max retries exceeded")
    _STATUS_CACHE.pop(twid, None)
    return 'none', False, True, []


# ─────────────────── run loop ────────────────────────────────────────────────

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
    stats = {'success_video':0,'success_image':0,'skipped':0,'failed':0,'duplicates':0}
    new_files = []
    consecutive_rl = 0

    for i, raw_url in enumerate(urls):
        url = normalize_tweet_url(raw_url)
        tid = extract_tweet_id(url)
        print(f"\n[{i+1}/{len(urls)}] {url}")

        if url in downloaded_urls or (tid and tid in downloaded_ids):
            print("   🔁 Already downloaded — skipped.")
            stats['duplicates'] += 1; stats['skipped'] += 1; continue

        kind, ok, rate_limited, fps = download_one(url, cookiefile, min_seconds, max_seconds)

        if ok:
            stats['success_video' if kind=='video' else 'success_image'] += 1
            downloaded_urls.add(url)
            if tid: downloaded_ids.add(tid)
            for fp in fps:
                if fp and os.path.exists(fp): new_files.append(fp)
        elif rate_limited: stats['failed'] += 1
        else: stats['skipped'] += 1

        if rate_limited:
            consecutive_rl += 1
            if consecutive_rl >= COOLDOWN_TRIGGER:
                print(f"\n🧊 Cooling down {COOLDOWN_SECONDS}s after {consecutive_rl} rate-limits...")
                time.sleep(COOLDOWN_SECONDS); consecutive_rl = 0
        else:
            consecutive_rl = 0

        if delay_seconds > 0 and i < len(urls)-1:
            time.sleep(delay_seconds)

    return stats, new_files


# ─────────────────── Google Drive ────────────────────────────────────────────

def get_drive_service():
    import json as _json
    from google.oauth2.credentials import Credentials
    from google.auth.transport.requests import Request
    from googleapiclient.discovery import build
    raw = os.environ.get("GDRIVE_TOKEN_JSON")
    if not raw: raise RuntimeError("Missing GDRIVE_TOKEN_JSON")
    info = _json.loads(raw)
    creds = Credentials(
        token=info.get("token"), refresh_token=info["refresh_token"],
        client_id=info["client_id"], client_secret=info["client_secret"],
        token_uri=info.get("token_uri","https://oauth2.googleapis.com/token"),
        scopes=info.get("scopes",["https://www.googleapis.com/auth/drive"]),
    )
    creds.refresh(Request())
    return build("drive","v3",credentials=creds)

def create_drive_folder(service, folder_name):
    meta = {"name":folder_name,"mimeType":"application/vnd.google-apps.folder"}
    f = service.files().create(body=meta, fields="id, webViewLink").execute()
    return f["id"], f.get("webViewLink")

def upload_files_to_folder(service, folder_id, filepaths):
    from googleapiclient.http import MediaFileUpload
    uploaded = []
    for fp in filepaths:
        name = os.path.basename(fp)
        print(f"   ☁️  Uploading: {name}")
        f = service.files().create(
            body={"name":name,"parents":[folder_id]},
            media_body=MediaFileUpload(fp, resumable=True),
            fields="id, name").execute()
        uploaded.append(f["name"])
    return uploaded


# ─────────────────── main ────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--folder-name", required=True)
    parser.add_argument("--min-duration", default="")
    parser.add_argument("--max-duration", default="")
    parser.add_argument("--delay", default="8")
    args = parser.parse_args()

    folder_name = (
        "".join(c for c in args.folder_name.strip() if c.isalnum() or c in (' ','-','_')).strip()
        or "downloads"
    )
    min_seconds  = parse_duration(args.min_duration)
    max_seconds  = parse_duration(args.max_duration)
    delay_seconds = parse_duration(args.delay) or 8

    if not os.path.exists(URLS_FILE):
        print(f"❌ {URLS_FILE} not found."); sys.exit(1)

    with open(URLS_FILE,"r",encoding="utf-8") as f:
        raw_urls = [u.strip() for u in f if u.strip() and not u.startswith('#')]

    urls, dupes = dedupe_preserve_order(raw_urls)
    if dupes: print(f"🔁 Removed {len(dupes)} duplicate(s) from urlsnow.txt.")

    print(f"Starting: {len(urls)} URL(s) | folder='{folder_name}' | "
          f"min={min_seconds}s | max={max_seconds}s | delay={delay_seconds}s")

    stats, new_files = run_downloads(urls, min_seconds, max_seconds, delay_seconds)

    print(f"\n📊 Summary: videos={stats['success_video']} images={stats['success_image']} "
          f"skipped={stats['skipped']} failed={stats['failed']} dupes={stats['duplicates']}")

    summary_path = os.environ.get("GITHUB_STEP_SUMMARY")

    if not new_files:
        print("No new files — nothing to upload.")
        if summary_path:
            with open(summary_path,"a") as f:
                f.write(f"### Run complete — no new files\n\n"
                        f"- Videos: {stats['success_video']}\n- Images: {stats['success_image']}\n"
                        f"- Skipped: {stats['skipped']}\n- Failed: {stats['failed']}\n"
                        f"- Duplicates: {stats['duplicates']}\n")
        return

    print(f"\nUploading {len(new_files)} file(s) to Drive folder '{folder_name}'...")
    service = get_drive_service()
    folder_id, folder_link = create_drive_folder(service, folder_name)
    uploaded = upload_files_to_folder(service, folder_id, new_files)

    print(f"\n✅ Uploaded {len(uploaded)} file(s) to '{folder_name}'.")
    if folder_link: print(f"🔗 {folder_link}")

    if summary_path:
        with open(summary_path,"a") as f:
            f.write(f"### Run complete\n\n"
                    f"- Videos: {stats['success_video']}\n- Images: {stats['success_image']}\n"
                    f"- Skipped: {stats['skipped']}\n- Failed: {stats['failed']}\n"
                    f"- Duplicates: {stats['duplicates']}\n\n"
                    f"**Drive folder:** [{folder_name}]({folder_link})\n\n"
                    + "\n".join(f"- {n}" for n in uploaded) + "\n")

if __name__ == "__main__":
    main()

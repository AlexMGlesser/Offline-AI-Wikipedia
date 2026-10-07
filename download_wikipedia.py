#!/usr/bin/env python3
"""
Wikipedia bulk downloader + organizer for the Glesser Industries Database.

WHAT IT DOES
  1. Downloads Wikipedia in priority order (most useful first) until a 5 TB budget
     is reached:
       a. English Wikipedia - every current article (multistream XML + index)  ~25 GB
       b. English Wikipedia - Kiwix "maxi" ZIM (all articles WITH images,
          browsable offline in the free Kiwix app)                             ~110 GB
       c. (Optional, off by default) other languages - set OTHER_LANGUAGES
       d. English Wikipedia - all current pages incl. talk/user/project pages   ~45 GB
       e. (Optional, off by default) English Wikipedia full edit history (.7z)  very large
  2. Organizes ("sorts") every downloaded article dump:
       * each article is saved as its own text file, in alphabetical folders:
             organized\\en\\articles\\A\\Ab\\Abr\\Abraham Lincoln.wiki
       * a SQLite catalog (organized\\en\\enwiki.sqlite) lists every article, its
         categories, its sort key and every redirect (e.g. "JFK" -> "John F. Kennedy")
       * plain alphabetical index files (organized\\en\\alphabetical-index\\A.tsv ...)
     The Glesser librarian search app reads this organized copy.

FOLLOWS WIKIMEDIA'S DOWNLOAD RULES
  * At most 3 connections at once (Wikimedia caps dump downloads at 3 per IP).
  * Identifies itself with a contact email, pauses between requests, and backs off
    when a server has trouble. Only uses the official dump sites.
  * Writes LICENSE-AND-ATTRIBUTION.txt (Wikipedia text is CC BY-SA 4.0).

OTHER FEATURES
  * Always picks the newest COMPLETED dump automatically.
  * Resumable: stop any time with Ctrl+C and run again to continue (both downloading
    and organizing pick up where they left off).
  * Verifies every download with the checksum published by Wikimedia / Kiwix.
  * Never exceeds the 5 TB budget (downloads + organized copies) and checks free
    disk space first.

REQUIREMENTS   Python 3.8+  and  `pip install requests`

USAGE
  python download_wikipedia.py                     download, then organize
  python download_wikipedia.py --download-only     just download
  python download_wikipedia.py --organize-only     just organize what's downloaded
  python download_wikipedia.py --lookup "Albert Einstein"            find an article
  python download_wikipedia.py --category "Physicists" --lang en     list a category
"""

import argparse
import bz2
import concurrent.futures as cf
import hashlib
import json
import logging
import math
import multiprocessing as mp
import os
import re
import shutil
import sqlite3
import sys
import threading
import time
import unicodedata
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from pathlib import Path

try:
    import requests
except ImportError:
    sys.exit("This script needs the 'requests' package. Install it with:  pip install requests")

# ----------------------------------------------------------------------------
# Settings
# ----------------------------------------------------------------------------
DEST = Path(r"D:\Glesser-Industries-Database\Wikipedia")

LIMIT_BYTES = 5 * 10**12          # 5 TB budget (decimal TB, like drive makers use)
DISK_RESERVE_BYTES = 50 * 10**9   # always leave at least 50 GB free on the drive

# Wikimedia asks automated downloaders to identify themselves with a contact.
USER_AGENT = ("GlesserIndustriesWikiDownloader/2.0 (contact: you@example.com) "
              "python-requests")

# Wikimedia's downloads page: "Downloads are also rate limited and capped at
# 3 connections per-IP." This is the total for the whole script (lookups included).
# Do NOT raise it - going over the cap breaks their rules and gets you throttled.
MAX_CONNECTIONS = 3

WIKIMEDIA_BASE = "https://dumps.wikimedia.org"   # can be swapped for an official mirror
KIWIX_BASE = "https://download.kiwix.org/zim/wikipedia/"

# Other language editions to grab (current articles only), in priority order.
OTHER_LANGUAGES = []   # English only. To add others later, e.g. ["de", "fr", "es"]

INCLUDE_ENGLISH_ALL_CURRENT_PAGES = True   # talk pages, user pages, project pages, etc.
INCLUDE_FULL_HISTORY = False               # every revision ever; huge, mostly for researchers
VERIFY_CHECKSUMS = True
REFRESH_EXISTING = False                   # True = download newer versions of finished groups
POLITE_PAUSE_SECONDS = 5                   # pause before each file / lookup

# Organizer
ORGANIZE_AFTER_DOWNLOAD = True             # sort the pages once downloads finish
ORGANIZE_LANGUAGES = None                  # None = every downloaded language, or e.g. ["en", "de"]
ORGANIZE_WORKERS = max(1, (os.cpu_count() or 2) - 1)   # CPU processes used for organizing
STREAMS_PER_TASK = 20                      # dump blocks (~100 pages each) per work unit
UNCOMPRESSED_RATIO = 4.5                   # organized size ~= 4.5 x compressed dump (estimate)

CHUNK_SIZE = 8 * 1024 * 1024
MAX_RETRIES = 20
TIMEOUT = 60

LICENSE_NOTE = """Wikipedia text is licensed under CC BY-SA 4.0 (and GFDL).
Images in the Kiwix file carry their own licenses (see each file's page on Wikimedia Commons).
Personal/internal use is fine. If you redistribute or publish any of this content,
you must credit Wikipedia/its authors, link the license, and share adaptations under
the same license: https://creativecommons.org/licenses/by-sa/4.0/
Wikipedia(R) is a trademark of the Wikimedia Foundation; don't present this copy as official.
Downloaded from https://dumps.wikimedia.org and https://download.kiwix.org
"""

# ----------------------------------------------------------------------------
# Shared plumbing
# ----------------------------------------------------------------------------
MANIFEST_PATH = DEST / "manifest.json"                # finished downloads
GROUPS_PATH = DEST / "completed_groups.json"          # download groups fully finished
ORGANIZED = DEST / "organized"
ESTIMATES_PATH = ORGANIZED / "size_estimates.json"   # budget used by organized copies

log = logging.getLogger("wiki")
lock = threading.RLock()            # guards manifest, progress and budget bookkeeping
stop = threading.Event()            # set on Ctrl+C
conn_slots = threading.BoundedSemaphore(MAX_CONNECTIONS)
_tls = threading.local()


class Stopped(Exception):
    pass


class _ClearLineHandler(logging.StreamHandler):
    """Wipes the live progress line before printing a log message."""
    def emit(self, record):
        try:
            w = max(20, shutil.get_terminal_size().columns - 1)
            self.stream.write("\r" + " " * w + "\r")
        except Exception:
            pass
        super().emit(record)


def setup_logging():
    DEST.mkdir(parents=True, exist_ok=True)
    fmt = logging.Formatter("%(asctime)s  %(message)s", "%Y-%m-%d %H:%M:%S")
    h1 = _ClearLineHandler(sys.stdout)
    h1.setFormatter(fmt)
    h2 = logging.FileHandler(DEST / "download.log", encoding="utf-8")
    h2.setFormatter(fmt)
    log.handlers[:] = [h1, h2]
    log.setLevel(logging.INFO)
    log.propagate = False


def session():
    """One requests session per thread (sessions aren't thread-safe)."""
    s = getattr(_tls, "s", None)
    if s is None:
        s = requests.Session()
        s.headers["User-Agent"] = USER_AGENT
        s.headers["Connection"] = "close"   # no idle connections left open
        _tls.s = s
    return s


@dataclass
class FileSpec:
    group: str            # e.g. "enwiki-articles"
    name: str             # filename on disk
    url: str
    size: int             # bytes (0 if unknown)
    hash_type: str = ""   # "sha1", "md5", "sha256" or ""
    hash_value: str = ""


def human(n):
    n = float(n)
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if abs(n) < 1000 or unit == "TB":
            return f"{n:,.0f} B" if unit == "B" else f"{n:,.1f} {unit}"
        n /= 1000


def hms(seconds):
    if not seconds or seconds <= 0 or seconds > 10**8:
        return "--"
    h, rem = divmod(int(seconds), 3600)
    return f"{h}h{rem // 60:02d}m" if h else f"{rem // 60}m{rem % 60:02d}s"


def load_json(path, default):
    try:
        return json.loads(Path(path).read_text(encoding="utf-8"))
    except FileNotFoundError:
        return default


def save_json(path, data):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(json.dumps(data, indent=2), encoding="utf-8")
    tmp.replace(path)


def http(method, url, **kw):
    """A small request (lookup/listing) that counts toward the connection cap."""
    for attempt in range(5):
        if stop.is_set():
            raise Stopped()
        try:
            with conn_slots:
                r = session().request(method, url, timeout=TIMEOUT, **kw)
            r.raise_for_status()
            return r
        except requests.RequestException as e:
            if attempt == 4:
                raise
            log.warning(f"  retrying {url} ({e})")
            stop.wait(5 * (attempt + 1))


# ----------------------------------------------------------------------------
# Finding the newest files
# ----------------------------------------------------------------------------
def wikimedia_files(wiki, group, patterns):
    """Files matching all `patterns` from the newest dump in which they're finished."""
    listing = http("GET", f"{WIKIMEDIA_BASE}/{wiki}/").text
    dates = sorted(set(re.findall(r'href="(\d{8})/"', listing)), reverse=True)
    for date in dates[:6]:
        try:
            status = http("GET", f"{WIKIMEDIA_BASE}/{wiki}/{date}/dumpstatus.json").json()
        except Stopped:
            raise
        except Exception:
            continue
        found = {}
        for job in status.get("jobs", {}).values():
            if job.get("status") != "done":
                continue
            for fname, info in (job.get("files") or {}).items():
                if any(re.search(p, fname) for p in patterns) and info.get("url"):
                    url = info["url"]
                    if url.startswith("/"):
                        url = WIKIMEDIA_BASE + url
                    htype, hval = ("sha1", info["sha1"]) if info.get("sha1") else \
                                  ("md5", info["md5"]) if info.get("md5") else ("", "")
                    found[fname] = FileSpec(group, fname, url, int(info.get("size") or 0), htype, hval)
        if all(any(re.search(p, n) for n in found) for p in patterns):
            log.info(f"  using {wiki} dump from {date}")
            return sorted(found.values(), key=lambda f: f.name)
    raise RuntimeError(f"no completed dump found for {wiki} matching {patterns}")


def kiwix_latest(prefix, group):
    """Newest Kiwix ZIM whose name starts with `prefix` (e.g. wikipedia_en_all_maxi)."""
    listing = http("GET", KIWIX_BASE).text
    matches = re.findall(rf'href="({re.escape(prefix)}_(\d{{4}}-\d{{2}})\.zim)"', listing)
    if not matches:
        raise RuntimeError(f"no Kiwix file found for {prefix}")
    name = max(matches, key=lambda m: m[1])[0]
    url = KIWIX_BASE + name
    head = http("HEAD", url, allow_redirects=True)
    size = int(head.headers.get("Content-Length") or 0)
    hval = ""
    try:
        hval = http("GET", url + ".sha256").text.split()[0]
    except Stopped:
        raise
    except Exception:
        log.warning("  couldn't fetch Kiwix checksum; file will not be verified")
    return [FileSpec(group, name, url, size, "sha256" if hval else "", hval)]


ARTICLES = [r"-pages-articles-multistream\.xml\.bz2$",
            r"-pages-articles-multistream-index\.txt\.bz2$"]


def build_plan():
    """(group, subfolder, resolver) in priority order. Resolvers run lazily."""
    plan = [
        ("enwiki-articles", "english-articles",
         lambda: wikimedia_files("enwiki", "enwiki-articles", ARTICLES)),
        ("kiwix-en-maxi", "kiwix-offline-reader",
         lambda: kiwix_latest("wikipedia_en_all_maxi", "kiwix-en-maxi")),
    ]
    for lang in OTHER_LANGUAGES:
        wiki = f"{lang}wiki"
        plan.append((f"{wiki}-articles", f"other-languages/{lang}",
                     lambda w=wiki: wikimedia_files(w, f"{w}-articles", ARTICLES)))
    if INCLUDE_ENGLISH_ALL_CURRENT_PAGES:
        plan.append(("enwiki-meta-current", "english-all-current-pages",
                     lambda: wikimedia_files("enwiki", "enwiki-meta-current",
                                             [r"-pages-meta-current\.xml\.bz2$"])))
    if INCLUDE_FULL_HISTORY:
        plan.append(("enwiki-history", "english-full-history",
                     lambda: wikimedia_files("enwiki", "enwiki-history",
                                             [r"-pages-meta-history\d+\.xml-p\d+p\d+\.7z$"])))
    return plan


# ----------------------------------------------------------------------------
# Downloading (up to MAX_CONNECTIONS files at once)
# ----------------------------------------------------------------------------
class Progress:
    """Live one-line status for all active downloads."""
    def __init__(self):
        self.active = {}        # name -> [done, total, start_time, start_done]
        self.queued_bytes = 0   # bytes in files waiting for a free connection
        self._quit = threading.Event()
        self._t = threading.Thread(target=self._loop, daemon=True)
        self._t.start()

    def close(self):
        self._quit.set()
        self._t.join(timeout=5)

    def _loop(self):
        while not self._quit.wait(3):
            with lock:
                items = [(n, *v) for n, v in self.active.items()]
                queued = self.queued_bytes
            if not items:
                continue
            now, parts, total_rate, remaining = time.time(), [], 0.0, queued
            for name, done, total, t0, d0 in items:
                rate = (done - d0) / max(now - t0, 1e-6)
                total_rate += rate
                remaining += max(total - done, 0)
                pct = 100 * done / total if total else 0
                short = name if len(name) <= 26 else name[:12] + ".." + name[-12:]
                parts.append(f"{short} {pct:4.1f}% {human(rate)}/s")
            eta = remaining / total_rate if total_rate else 0
            line = (f"  [{len(items)}/{MAX_CONNECTIONS}] " + " | ".join(parts) +
                    f" || {human(total_rate)}/s  ETA {hms(eta)}")
            w = max(20, shutil.get_terminal_size().columns - 1)
            sys.stdout.write("\r" + line[:w].ljust(w))
            sys.stdout.flush()


def file_hash(path, htype):
    h = hashlib.new(htype)
    with open(path, "rb") as f:
        while True:
            if stop.is_set():
                raise Stopped()
            chunk = f.read(CHUNK_SIZE)
            if not chunk:
                break
            h.update(chunk)
    return h.hexdigest()


def download(spec, target, progress):
    part = target.with_name(target.name + ".part")
    for attempt in range(1, MAX_RETRIES + 1):
        if stop.is_set():
            raise Stopped()
        have = part.stat().st_size if part.exists() else 0
        if spec.size and have >= spec.size:
            break
        headers = {"Range": f"bytes={have}-"} if have else {}
        try:
            with conn_slots:   # holds one of the 3 connections while transferring
                with session().get(spec.url, headers=headers, stream=True,
                                   timeout=TIMEOUT, allow_redirects=True) as r:
                    if r.status_code == 416:      # already complete
                        break
                    r.raise_for_status()
                    if have and r.status_code != 206:
                        log.info(f"  {spec.name}: server ignored resume request; restarting file")
                        have = 0
                    total = spec.size or (have + int(r.headers.get("Content-Length") or 0))
                    with lock:
                        progress.active[spec.name] = [have, total, time.time(), have]
                    with open(part, "ab" if have else "wb") as f:
                        for chunk in r.iter_content(CHUNK_SIZE):
                            if stop.is_set():
                                raise Stopped()
                            f.write(chunk)
                            with lock:
                                progress.active[spec.name][0] += len(chunk)
            break
        except (requests.RequestException, OSError) as e:
            wait = min(300, 10 * attempt)
            log.warning(f"  {spec.name}: connection problem ({e}); "
                        f"retry {attempt}/{MAX_RETRIES} in {wait}s")
            stop.wait(wait)
        finally:
            with lock:
                progress.active.pop(spec.name, None)
    else:
        raise RuntimeError(f"giving up on {spec.name} after {MAX_RETRIES} retries")

    if spec.size and part.stat().st_size != spec.size:
        raise RuntimeError(f"size mismatch for {spec.name}: "
                           f"got {part.stat().st_size}, expected {spec.size}")
    if VERIFY_CHECKSUMS and spec.hash_type:
        log.info(f"  verifying {spec.hash_type} checksum of {spec.name} ...")
        actual = file_hash(part, spec.hash_type)
        if actual.lower() != spec.hash_value.lower():
            part.unlink()
            raise RuntimeError(f"checksum mismatch for {spec.name}; deleted, rerun to try again")
        log.info(f"  checksum OK: {spec.name}")
    part.replace(target)


class Downloader:
    def __init__(self):
        self.manifest = load_json(MANIFEST_PATH, {})
        self.completed = set(load_json(GROUPS_PATH, []))
        self.group_left = {}      # group -> names still to finish
        self.progress = None

    def used(self):
        return sum(e["size"] for e in self.manifest.values())

    def _mark_done(self, group):
        self.completed.add(group)
        save_json(GROUPS_PATH, sorted(self.completed))
        log.info(f"[{group}] group complete")

    def job(self, spec, folder):
        """Runs in a worker thread: download one file."""
        reserved = spec.size
        try:
            if stop.is_set():
                return
            target = folder / spec.name
            part = target.with_name(target.name + ".part")
            already = part.stat().st_size if part.exists() else 0
            with lock:
                self.progress.queued_bytes -= reserved
                reserved = 0
                # free space must cover this file plus what the other active files still need
                in_flight = sum(max(t - d, 0) for d, t, *_ in self.progress.active.values())
                free = shutil.disk_usage(DEST).free
                if spec.size and free - in_flight - (spec.size - already) < DISK_RESERVE_BYTES:
                    log.error(f"[{spec.group}] not enough free disk space for {spec.name} "
                              f"({human(spec.size)} needed, {human(free)} free); skipped")
                    return
            stop.wait(POLITE_PAUSE_SECONDS)
            if stop.is_set():
                return
            log.info(f"[{spec.group}] downloading {spec.name} ({human(spec.size)})")
            download(spec, target, self.progress)
            with lock:
                self.manifest[spec.name] = {
                    "group": spec.group, "size": target.stat().st_size,
                    "path": str(target), "url": spec.url,
                    "finished": time.strftime("%Y-%m-%d %H:%M:%S")}
                save_json(MANIFEST_PATH, self.manifest)
                left = self.group_left[spec.group]
                left.discard(spec.name)
                log.info(f"[{spec.group}] finished {spec.name}. "
                         f"Total downloaded: {human(self.used())}")
                if not left:
                    self._mark_done(spec.group)
        except Stopped:
            pass
        except Exception as e:
            log.error(f"[{spec.group}] {e}")
        finally:
            if reserved:
                with lock:
                    self.progress.queued_bytes -= reserved

    def run(self):
        """Returns False if interrupted with Ctrl+C."""
        reserved = self.used() + sum(load_json(ESTIMATES_PATH, {}).values())
        log.info(f"Destination: {DEST}")
        log.info(f"Budget: {human(LIMIT_BYTES)}   already used: {human(reserved)}   "
                 f"connections: {MAX_CONNECTIONS}")
        self.progress = Progress()
        pool = cf.ThreadPoolExecutor(max_workers=MAX_CONNECTIONS)
        futures = []
        try:
            for group, subdir, resolve in build_plan():
                if group in self.completed and not REFRESH_EXISTING:
                    log.info(f"[{group}] already downloaded, skipping")
                    continue
                stop.wait(POLITE_PAUSE_SECONDS)
                if stop.is_set():
                    raise Stopped()
                log.info(f"[{group}] looking up newest files...")
                try:
                    specs = resolve()
                except Stopped:
                    raise
                except Exception as e:
                    log.warning(f"[{group}] skipped: {e}")
                    continue
                folder = DEST / subdir
                todo = [s for s in specs
                        if not (s.name in self.manifest and (folder / s.name).exists())]
                if not todo:
                    with lock:
                        self._mark_done(group)
                    continue
                need = sum(s.size for s in todo)
                if reserved + need > LIMIT_BYTES:
                    log.info(f"[{group}] skipped: needs {human(need)}, "
                             f"only {human(LIMIT_BYTES - reserved)} left in budget")
                    continue
                reserved += need
                folder.mkdir(parents=True, exist_ok=True)
                with lock:
                    self.group_left[group] = {s.name for s in todo}
                    self.progress.queued_bytes += need
                for s in todo:
                    futures.append(pool.submit(self.job, s, folder))
            # wait in short steps so Ctrl+C is noticed on Windows
            while not all(f.done() for f in futures):
                cf.wait(futures, timeout=1)
        except (KeyboardInterrupt, Stopped):
            stop.set()
            log.info("Stopping... (finishing the current write; partial files will resume)")
        finally:
            pool.shutdown(wait=True)
            self.progress.close()
        if stop.is_set():
            log.info("Stopped. Run the script again to resume where it left off.")
            return False
        log.info(f"Downloads done. Total downloaded: {human(self.used())}")
        return True


# ----------------------------------------------------------------------------
# Organizer: sort every article into its own file + a searchable catalog
# ----------------------------------------------------------------------------
RESERVED = {"CON", "PRN", "AUX", "NUL", *(f"COM{i}" for i in range(1, 10)),
            *(f"LPT{i}" for i in range(1, 10))}
BAD_CHARS = re.compile(r'[<>:"/\\|?*\x00-\x1f]')
MAX_NAME = 120   # keeps full paths under Windows' 260-character limit


def fold(s):
    """Casefolded, accent-stripped text: 'Éclair' -> 'eclair'."""
    s = unicodedata.normalize("NFKD", s)
    return "".join(c for c in s if not unicodedata.combining(c)).casefold()


def _dirpart(s):
    s = "".join(c if c.isalnum() else "_" for c in s) or "_"
    s = s[:1].upper() + s[1:]
    return "_" + s if s.upper() in RESERVED else s


def letter_dirs(title):
    key = fold(title).strip() or "_"
    c = key[0]
    l1 = "0-9" if c.isdigit() else (c.upper() if c.isalnum() else "_symbols")
    if l1.upper() in RESERVED:
        l1 = "_" + l1
    return l1, _dirpart(key[:2]), _dirpart(key[:3])


def safe_filename(title):
    s = BAD_CHARS.sub("_", title).rstrip(". ") or "_"
    if s.split(".")[0].upper() in RESERVED:
        s = "_" + s
    return s[:MAX_NAME].rstrip(". ") or "_"


# --- worker side (runs in separate processes; must be top-level for Windows) ---
_W = {}


def _org_init(lang_dir, cat_names):
    names = "|".join(re.escape(n) for n in cat_names)
    _W["dir"] = Path(lang_dir)
    _W["cat"] = re.compile(r"\[\[\s*(?:" + names + r")\s*:\s*([^\]|\n]+?)\s*(?:\|[^\]]*)?\]\]",
                           re.IGNORECASE)
    _W["sort"] = re.compile(r"\{\{\s*(?:DEFAULTSORT|DEFAULTSORTKEY|DEFAULTCATEGORYSORT)\s*:\s*([^}|]*)",
                            re.IGNORECASE)


def _norm_cat(name):
    name = re.sub(r"[_\s]+", " ", name).strip()
    return name[:1].upper() + name[1:]


def _write_article(rel_dir, title, page_id, data):
    """Write text, handling Windows' case-insensitive name collisions. Returns rel path."""
    folder = _W["dir"] / rel_dir
    folder.mkdir(parents=True, exist_ok=True)
    base = safe_filename(title)
    path = folder / (base + ".wiki")
    try:
        with open(path, "xb") as f:
            f.write(data)
        return rel_dir / path.name
    except FileExistsError:
        try:
            if path.read_bytes() == data:      # same article from an interrupted run
                return rel_dir / path.name
        except OSError:
            pass
    alt = folder / (f"{base[:MAX_NAME - 14]} [{page_id}].wiki")
    with open(alt, "wb") as f:
        f.write(data)
    return rel_dir / alt.name


def _org_task(task):
    src, start, end = task
    try:
        with open(src, "rb") as f:
            f.seek(start)
            raw = f.read(end - start if end else -1)
        text = bz2.decompress(raw).decode("utf-8").replace("</mediawiki>", "")
        root = ET.fromstring("<pages>" + text + "</pages>")
        pages, cats, redirects = [], [], []
        for p in root.iter("page"):
            if (p.findtext("ns") or "").strip() != "0":
                continue
            title = p.findtext("title") or ""
            red = p.find("redirect")
            if red is not None:
                redirects.append((title, red.get("title") or ""))
                continue
            pid = int(p.findtext("id"))
            wikitext = p.findtext("revision/text") or ""
            m = _W["sort"].search(wikitext)
            sort_key = fold(m.group(1).strip() if m and m.group(1).strip() else title)
            l1, l2, l3 = letter_dirs(title)
            data = wikitext.encode("utf-8")
            rel = _write_article(Path("articles", l1, l2, l3), title, pid, data)
            pages.append((pid, title, fold(title), sort_key, l1, str(rel), len(data)))
            seen = set()
            for c in _W["cat"].findall(wikitext):
                c = _norm_cat(c)
                if c and c not in seen:
                    seen.add(c)
                    cats.append((pid, c))
        return start, pages, cats, redirects, None
    except Exception as e:   # reported by the main process; chunk is retried next run
        return start, None, None, None, f"{type(e).__name__}: {e}"


# --- main-process side ---
SCHEMA = """
CREATE TABLE IF NOT EXISTS pages(id INTEGER PRIMARY KEY, title TEXT, title_key TEXT,
    sort_key TEXT, letter TEXT, path TEXT, bytes INTEGER);
CREATE TABLE IF NOT EXISTS categories(page_id INTEGER, category TEXT);
CREATE TABLE IF NOT EXISTS redirects(title TEXT PRIMARY KEY, target TEXT);
CREATE TABLE IF NOT EXISTS meta(key TEXT PRIMARY KEY, value TEXT);
CREATE TABLE IF NOT EXISTS done_chunks(start INTEGER PRIMARY KEY);
"""
INDEXES = """
CREATE INDEX IF NOT EXISTS idx_pages_title ON pages(title);
CREATE INDEX IF NOT EXISTS idx_pages_letter_key ON pages(letter, title_key);
CREATE INDEX IF NOT EXISTS idx_pages_sort ON pages(sort_key);
CREATE INDEX IF NOT EXISTS idx_cat_cat ON categories(category, page_id);
CREATE INDEX IF NOT EXISTS idx_cat_page ON categories(page_id);
"""


def read_index_offsets(index_path):
    offsets = set()
    with bz2.open(index_path, "rt", encoding="utf-8") as f:
        for line in f:
            off = line.split(":", 2)[0]
            if off.isdigit():
                offsets.add(int(off))
    return sorted(offsets)


def category_names(xml_path, first_offset):
    """Read the dump header to learn this language's word for 'Category'."""
    names = {"Category"}
    with open(xml_path, "rb") as f:
        head = f.read(first_offset)
    try:
        text = bz2.decompress(head).decode("utf-8", "replace")
        m = re.search(r'<namespace key="14"[^>]*>([^<]+)</namespace>', text)
        if m:
            names.add(m.group(1).strip())
    except Exception:
        pass
    return sorted(names)


def dump_date(name):
    m = re.search(r"-(\d{8})-", name)
    return m.group(1) if m else "unknown"


def find_dump(lang, manifest):
    """(xml_path, index_path) of the newest finished articles dump for `lang`."""
    group = f"{lang}wiki-articles"
    xmls, idxs = {}, {}
    for name, e in manifest.items():
        if e.get("group") != group:
            continue
        if name.endswith("-pages-articles-multistream.xml.bz2"):
            xmls[dump_date(name)] = Path(e["path"])
        elif name.endswith("-pages-articles-multistream-index.txt.bz2"):
            idxs[dump_date(name)] = Path(e["path"])
    for date in sorted(set(xmls) & set(idxs), reverse=True):
        if xmls[date].exists() and idxs[date].exists():
            return xmls[date], idxs[date]
    return None


def organize_language(lang, xml_path, index_path):
    lang_dir = ORGANIZED / lang
    lang_dir.mkdir(parents=True, exist_ok=True)
    db = sqlite3.connect(lang_dir / f"{lang}wiki.sqlite")
    db.execute("PRAGMA journal_mode=WAL")
    db.execute("PRAGMA synchronous=NORMAL")
    db.executescript(SCHEMA)
    meta = dict(db.execute("SELECT key, value FROM meta"))
    source = xml_path.name

    if meta.get("source") == source and meta.get("status") == "complete":
        log.info(f"[organize {lang}] already organized ({source}), skipping")
        db.close()
        return True
    if meta.get("source") and meta.get("source") != source:
        old = lang_dir / "articles"
        if old.exists():
            moved = lang_dir / f"articles-previous-{dump_date(meta['source'])}"
            old.rename(moved)
            log.info(f"[organize {lang}] newer dump found; old copy moved to {moved} "
                     f"(you can delete that folder)")
        with db:
            for t in ("pages", "categories", "redirects", "meta", "done_chunks"):
                db.execute(f"DELETE FROM {t}")
            for idx in ("idx_pages_title", "idx_pages_letter_key", "idx_pages_sort",
                        "idx_cat_cat", "idx_cat_page"):
                db.execute(f"DROP INDEX IF EXISTS {idx}")
    with db:
        db.execute("INSERT OR REPLACE INTO meta VALUES('source', ?)", (source,))
        db.execute("INSERT OR REPLACE INTO meta VALUES('status', 'in-progress')")

    log.info(f"[organize {lang}] reading index {index_path.name} ...")
    offsets = read_index_offsets(index_path)
    if not offsets:
        log.error(f"[organize {lang}] index is empty; skipping")
        return False
    cats = category_names(xml_path, offsets[0])
    starts = offsets[::STREAMS_PER_TASK]
    tasks_all = [(str(xml_path), s, starts[i + 1] if i + 1 < len(starts) else 0)
                 for i, s in enumerate(starts)]
    done = {r[0] for r in db.execute("SELECT start FROM done_chunks")}
    tasks = [t for t in tasks_all if t[1] not in done]
    total = len(tasks_all)
    log.info(f"[organize {lang}] {total:,} work units, {len(done):,} already done, "
             f"{ORGANIZE_WORKERS} worker processes")

    n_done, n_pages, failures = len(done), 0, 0
    t0, last = time.time(), 0.0
    pool = mp.Pool(ORGANIZE_WORKERS, initializer=_org_init, initargs=(str(lang_dir), cats))
    try:
        for start, pages, cat_rows, reds, err in pool.imap_unordered(_org_task, tasks):
            if err:
                failures += 1
                log.error(f"[organize {lang}] block at byte {start} failed ({err}); "
                          f"it will be retried next run")
                continue
            with db:
                db.executemany("INSERT OR REPLACE INTO pages VALUES(?,?,?,?,?,?,?)", pages)
                db.executemany("INSERT INTO categories VALUES(?,?)", cat_rows)
                db.executemany("INSERT OR REPLACE INTO redirects VALUES(?,?)", reds)
                db.execute("INSERT OR IGNORE INTO done_chunks VALUES(?)", (start,))
            n_done += 1
            n_pages += len(pages)
            now = time.time()
            if now - last > 2:
                rate = n_pages / max(now - t0, 1e-6)
                left = total - n_done
                per_unit = (now - t0) / max(n_done - len(done), 1)
                w = max(20, shutil.get_terminal_size().columns - 1)
                sys.stdout.write("\r" + (f"  [organize {lang}] {100 * n_done / total:5.1f}%  "
                                         f"{n_pages:,} articles  {rate:,.0f}/s  "
                                         f"ETA {hms(left * per_unit)}")[:w].ljust(w))
                sys.stdout.flush()
                last = now
        pool.close()
    except KeyboardInterrupt:
        pool.terminate()
        stop.set()
        log.info(f"[organize {lang}] stopped; finished blocks are saved, rerun to continue")
        db.close()
        return False
    finally:
        pool.join()

    if failures:
        log.error(f"[organize {lang}] {failures} blocks failed; rerun to retry them")
        db.close()
        return False

    log.info(f"[organize {lang}] building catalog indexes ...")
    db.executescript(INDEXES)
    idx_dir = lang_dir / "alphabetical-index"
    idx_dir.mkdir(exist_ok=True)
    letters = [r[0] for r in db.execute("SELECT DISTINCT letter FROM pages")]
    for letter in letters:
        with open(idx_dir / f"{letter}.tsv", "w", encoding="utf-8", newline="\n") as f:
            for title, path in db.execute(
                    "SELECT title, path FROM pages WHERE letter=? ORDER BY title_key", (letter,)):
                f.write(f"{title}\t{path}\n")
    count = db.execute("SELECT COUNT(*) FROM pages").fetchone()[0]
    nred = db.execute("SELECT COUNT(*) FROM redirects").fetchone()[0]
    with db:
        db.execute("INSERT OR REPLACE INTO meta VALUES('status', 'complete')")
        db.execute("INSERT OR REPLACE INTO meta VALUES('articles', ?)", (str(count),))
        db.execute("INSERT OR REPLACE INTO meta VALUES('finished', ?)",
                   (time.strftime("%Y-%m-%d %H:%M:%S"),))
    db.close()
    log.info(f"[organize {lang}] done: {count:,} articles, {nred:,} redirects -> {lang_dir}")
    return True


def organize_all():
    manifest = load_json(MANIFEST_PATH, {})
    completed = set(load_json(GROUPS_PATH, []))
    order = ["en"] + [l for l in OTHER_LANGUAGES if l != "en"]
    langs = [l for l in order if f"{l}wiki-articles" in completed]
    if ORGANIZE_LANGUAGES is not None:
        langs = [l for l in langs if l in ORGANIZE_LANGUAGES]
    if not langs:
        log.info("Nothing to organize yet (no finished article downloads).")
        return
    estimates = load_json(ESTIMATES_PATH, {})
    for lang in langs:
        if stop.is_set():
            return
        found = find_dump(lang, manifest)
        if not found:
            log.warning(f"[organize {lang}] dump files not found on disk; skipping")
            continue
        xml_path, index_path = found
        est = int(xml_path.stat().st_size * UNCOMPRESSED_RATIO)
        used = sum(e["size"] for e in manifest.values()) + \
            sum(v for k, v in estimates.items() if k != lang)
        if used + est > LIMIT_BYTES:
            log.info(f"[organize {lang}] skipped: needs ~{human(est)}, "
                     f"only {human(LIMIT_BYTES - used)} left in budget")
            continue
        db_path = ORGANIZED / lang / f"{lang}wiki.sqlite"
        already = 0
        if db_path.exists():
            con = sqlite3.connect(db_path)
            try:
                already = con.execute("SELECT COALESCE(SUM(bytes),0) FROM pages").fetchone()[0]
            except sqlite3.Error:
                pass
            con.close()
        free = shutil.disk_usage(DEST).free
        if free - max(est - already, 0) < DISK_RESERVE_BYTES:
            log.error(f"[organize {lang}] not enough free disk space "
                      f"(~{human(est - already)} needed, {human(free)} free); skipping")
            continue
        estimates[lang] = est
        save_json(ESTIMATES_PATH, estimates)
        organize_language(lang, xml_path, index_path)


# ----------------------------------------------------------------------------
# Lookup helpers
# ----------------------------------------------------------------------------
def open_catalog(lang):
    path = ORGANIZED / lang / f"{lang}wiki.sqlite"
    if not path.exists():
        sys.exit(f"No organized catalog for '{lang}' yet ({path}). Run with --organize-only first.")
    return sqlite3.connect(path)


def lookup(title, lang):
    db = open_catalog(lang)
    q = title.strip().replace("_", " ")
    for _ in range(5):   # follow up to 5 redirects
        row = db.execute("SELECT id, title, path FROM pages WHERE title=?", (q,)).fetchone()
        if row:
            break
        red = db.execute("SELECT target FROM redirects WHERE title=?", (q,)).fetchone()
        if red:
            print(f"  '{q}' redirects to '{red[0]}'")
            q = red[0].split("#")[0]
            continue
        row = db.execute("SELECT id, title, path FROM pages WHERE title_key=? LIMIT 1",
                         (fold(q),)).fetchone()
        break
    if not row:
        print(f"No article titled '{title}'.")
        return
    pid, t, rel = row
    print(f"{t}\n  file: {ORGANIZED / lang / Path(rel)}")
    cats = [r[0] for r in db.execute(
        "SELECT category FROM categories WHERE page_id=? ORDER BY category", (pid,))]
    if cats:
        print("  categories: " + "; ".join(cats))


def list_category(name, lang):
    db = open_catalog(lang)
    name = _norm_cat(re.sub(r"^[^:]+:", "", name) if ":" in name else name)
    rows = db.execute("SELECT p.title FROM categories c JOIN pages p ON p.id=c.page_id "
                      "WHERE c.category=? ORDER BY p.sort_key", (name,)).fetchall()
    if not rows:
        print(f"No articles in category '{name}'.")
        return
    print(f"Category: {name} ({len(rows):,} articles)")
    for (t,) in rows:
        print("  " + t)


# ----------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description="Download and organize Wikipedia.")
    ap.add_argument("--download-only", action="store_true", help="download, don't organize")
    ap.add_argument("--organize-only", action="store_true", help="organize what's downloaded")
    ap.add_argument("--lookup", metavar="TITLE", help="find an article in the organized copy")
    ap.add_argument("--category", metavar="NAME", help="list the articles in a category")
    ap.add_argument("--lang", default="en", help="language for --lookup/--category (default en)")
    args = ap.parse_args()

    if args.lookup:
        return lookup(args.lookup, args.lang)
    if args.category:
        return list_category(args.category, args.lang)

    setup_logging()
    (DEST / "LICENSE-AND-ATTRIBUTION.txt").write_text(LICENSE_NOTE, encoding="utf-8")
    if not args.organize_only:
        if "you@example.com" in USER_AGENT:
            sys.exit("Please put a real contact email in USER_AGENT near the top of this script.")
        if not Downloader().run():
            return
    if not args.download_only and (args.organize_only or ORGANIZE_AFTER_DOWNLOAD):
        organize_all()
    log.info("All done.")


if __name__ == "__main__":
    mp.freeze_support()
    try:
        main()
    except KeyboardInterrupt:
        stop.set()
        print()
        print("Stopped. Run the script again to resume where it left off.")

"""
subfinder.py
mpv SubFinder | shortcut: Ctrl+S

INSTALLATION PATHS
------------------
  Windows (mpv):  %APPDATA%\\mpv\\scripts\\subfinder.py
  Windows (mpv):      %APPDATA%\\mpv\\scripts\\subfinder.py
  Linux / macOS:      ~/.config/mpv/scripts/subfinder.py

HOW IT WORKS
------------
PRIMARY:  OpenSubtitles.com REST API v1 — direct integration, no third-party
          library required. Requires an API key entered in Settings.
          Get a free key at https://www.opensubtitles.com/en/consumers
          Optional: add username + password (credentials button) for authenticated
          downloads with a higher daily quota.
          Searches by moviehash (local files) + title query for best match quality.

FALLBACK: subliminal (pip install subliminal) — used when OpenSubtitles.com
          returns 0 results or is not configured. Skipped entirely when the
          OS.com direct API returns results. Covers both legacy providers
          (opensubtitles), and when a key is available, the v3 provider
          (opensubtitlescom).

PROVIDER: SubDL — direct API integration. Runs independently alongside
          OpenSubtitles when enabled. Requires a SubDL API key which can
          be entered in Settings. Get a free key at https://subdl.com/account/api

LOGGING:  Everything is written to
          C:\\Users\\<YourName>\\AppData\\Roaming\\mpv\\scripts\\SubFinder\\logs\\subfinder.log

INSTALL subliminal (optional fallback — run once in a terminal):
  pip install subliminal babelfish dogpile.cache
"""

from __future__ import annotations
from typing import Optional, Tuple

import sys, os, re, json, shutil, hashlib, zipfile, time as _time_module, random as _random
import math as _math
import struct as _struct
import socket as _socket
import concurrent.futures as _cf
import threading, tempfile, traceback, logging, subprocess
import urllib.request, urllib.parse
import ssl as _ssl
try:
    import winsound as _winsound
except ImportError:
    _winsound = None
try:
    import win32file as _win32file_check  # noqa: F401  (import check only)
    _PYWIN32_OK = True
except ImportError:
    _PYWIN32_OK = False
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import tkinter.font
from pathlib import Path
from functools import lru_cache

# ── Version ───────────────────────────────────────────────────────────────────
__version__ = "1.0.0"

# ── Optional: pysubs2 (ASS/SSA/VTT translation support) ──────────────────────
try:
    import pysubs2 as _pysubs2
    _PYSUBS2_OK = True
except ImportError:
    _pysubs2 = None
    _PYSUBS2_OK = False

# ── Optional: charset_normalizer (subtitle encoding detection) ────────────────
# Ships with the requests library — very likely already installed.
try:
    from charset_normalizer import from_bytes as _cn_from_bytes
    _CHARSET_NORM_OK = True
except ImportError:
    _cn_from_bytes = None
    _CHARSET_NORM_OK = False

# Raised inside translate_srt_with_gemini when stop_event is set.
# Caught separately from generic Exception so the worker can post a clean
# "cancelled" status rather than an error dialog.
class TranslationCancelledError(Exception):
    pass

# ─────────────────────────────────────────────────────────────────────────────
# PLATFORM FONT FAMILIES
# ─────────────────────────────────────────────────────────────────────────────
# Segoe UI (Windows), Helvetica Neue (macOS), DejaVu Sans (Linux).
if sys.platform == "win32":
    _FONT_UI    = "Segoe UI"
    _FONT_MONO  = "Consolas"
    _FONT_EMOJI = "Segoe UI Emoji"
    _FONT_ICON  = "Segoe MDL2 Assets"  # Windows icon glyph font
elif sys.platform == "darwin":
    _FONT_UI    = "Helvetica Neue"
    _FONT_MONO  = "Menlo"
    _FONT_EMOJI = ""          # Tkinter on macOS resolves emoji via system fallback
    _FONT_ICON  = _FONT_UI    # MDL2 not available; fall back to UI font (buttons show text fallbacks)
else:                         # Linux / BSD / other POSIX
    _FONT_UI    = "DejaVu Sans"
    _FONT_MONO  = "DejaVu Sans Mono"
    _FONT_EMOJI = ""          # Noto Color Emoji is not universal; let Tk fall back
    _FONT_ICON  = _FONT_UI    # MDL2 not available; fall back to UI font

# Platform-conditional button glyphs for the Gemini popup drag/add/remove buttons.
# On Windows, Segoe MDL2 Assets renders \uE700/\uE710/\uE74D as icon glyphs.
# On Linux/macOS, _FONT_ICON falls back to _FONT_UI which has no MDL2 codepoints,
# so we substitute standard Unicode characters that are universally available.
if sys.platform == "win32":
    _GLYPH_DRAG   = "\uE700"   # Segoe MDL2: GlobalNavButton (≡ hamburger)
    _GLYPH_ADD    = "\uE710"   # Segoe MDL2: Add (+)
    _GLYPH_REMOVE = "\uE74D"   # Segoe MDL2: Delete (×)
else:
    _GLYPH_DRAG   = "≡"        # Unicode IDENTICAL TO — universally available
    _GLYPH_ADD    = "+"        # ASCII plus
    _GLYPH_REMOVE = "✕"        # Unicode MULTIPLICATION X (U+2715)

# ─────────────────────────────────────────────────────────────────────────────
# DOWNLOAD / TEMP-FILE CONSTANTS
# ─────────────────────────────────────────────────────────────────────────────
_DOWNLOAD_MAX_BYTES    = 50 * 1024 * 1024  # 50 MB hard cap on streaming downloads
_TEMP_FILE_MAX_AGE_HOURS = 48              # hours before temp files are eligible for cleanup
_INSTANCE_LOCK_PORT    = 47892             # Single-instance enforcement: bind this localhost port.

# ─────────────────────────────────────────────────────────────────────────────
# GEMINI TRANSLATION TUNING CONSTANTS
# ─────────────────────────────────────────────────────────────────────────────
_GEMINI_CHUNK_SIZE      = 300   # subtitle blocks sent per API call
_GEMINI_OVERLAP         = 10    # blocks of context prepended (not translated)
_GEMINI_MIN_SLEEP       = 4.5   # minimum seconds between API calls (rate-limit guard)
                                 # overridden at runtime by settings["gemini_min_sleep"] (with a 1.0 s floor)
_GEMINI_MAX_RETRIES     = 3     # per-chunk HTTP-level retry attempts before giving up
_GEMINI_CONTENT_RETRIES = 2     # per-chunk retries when response parses to 0 blocks
                                 # NOTE: not overridable from settings — edit this constant directly if needed
_GEMINI_TRUNC_RETRIES   = 2     # per-chunk retries on catastrophic truncation (STOP but <90% blocks)
                                 # NOTE: not overridable from settings — edit this constant directly if needed
_GEMINI_TOKEN_FALLBACK  = 65536 # used when the model metadata fetch fails

# Cache of outputTokenLimit per model name, populated lazily before translation.
# Avoids re-fetching on every chunk; survives model fallbacks within one session.
_model_token_limit_cache: dict[str, int] = {}
_model_token_limit_lock = threading.Lock()  # prevents duplicate HTTP calls on concurrent cache misses


# Explicit TLS context — ensures certificate verification is always enforced
# regardless of platform defaults or environment variables.
# Must be defined before any function that passes it to urllib.request.urlopen.
_SSL_CTX = _ssl.create_default_context()

# Sentinel returned by download_with_subdl when the downloaded file is a
# multi-subtitle archive that requires caller-side extraction rather than
# direct use. Using a typed sentinel object instead of a magic string (PEP 661).
_ARCHIVE_ONLY = object()

# ─────────────────────────────────────────────────────────────────────────────
# LOGGING
# ─────────────────────────────────────────────────────────────────────────────

SCRIPT_DIR    = Path(__file__).parent
SUBFINDER_DIR = SCRIPT_DIR / "SubFinder"
try:
    SCRIPT_DIR.mkdir(parents=True, exist_ok=True)
except OSError as _e:
    print("SubFinder FATAL: could not create SCRIPT_DIR {}: {}".format(SCRIPT_DIR, _e), file=sys.stderr)
    print("SubFinder FATAL: check disk space and directory permissions — cannot continue.", file=sys.stderr)
    sys.exit(1)

# ── One-time migration: move old flat folders into SubFinder/. Idempotent. ───
try:
    for _folder in ("logs", "config", "cache"):
        _old = SCRIPT_DIR / _folder
        _new = SUBFINDER_DIR / _folder
        if _old.is_dir() and not _new.exists():
            SUBFINDER_DIR.mkdir(parents=True, exist_ok=True)
            shutil.move(str(_old), str(_new))
            print("SubFinder: migrated {} → {}".format(_old, _new), file=sys.stderr)
except Exception as _mig_e:
    print("SubFinder: migration warning (non-fatal): {}".format(_mig_e), file=sys.stderr)

LOG_DIR    = SUBFINDER_DIR / "logs"
try:
    LOG_DIR.mkdir(parents=True, exist_ok=True)
except OSError as _e:
    print("SubFinder: could not create LOG_DIR {}: {}".format(LOG_DIR, _e), file=sys.stderr)
CONFIG_DIR = SUBFINDER_DIR / "config"
try:
    CONFIG_DIR.mkdir(parents=True, exist_ok=True)
except OSError as _e:
    print("SubFinder: could not create CONFIG_DIR {}: {}".format(CONFIG_DIR, _e), file=sys.stderr)
LOG_FILE   = LOG_DIR / "subfinder.log"

def _setup_logging():
    logger = logging.getLogger("subfinder")
    logger.setLevel(logging.DEBUG)
    logger.handlers.clear()  # clear in case of re-init (defensive; normally called once)
    fmt = logging.Formatter("%(asctime)s  %(levelname)-8s  %(name)s - %(message)s",
                            datefmt="%Y-%m-%d %H:%M:%S")
    try:
        from logging.handlers import RotatingFileHandler
        fh = RotatingFileHandler(LOG_FILE, encoding="utf-8", mode="a",
                                 maxBytes=2*1024*1024, backupCount=3)
        fh.setLevel(logging.DEBUG)
        fh.setFormatter(fmt)
        logger.addHandler(fh)
    except Exception as _fh_exc:
        # File handler failed (permissions, disk full, locked file, etc.).
        print("SubFinder: could not set up log file handler: {}".format(_fh_exc), file=sys.stderr)
    ch = logging.StreamHandler(sys.stderr)
    ch.setLevel(logging.WARNING)
    ch.setFormatter(fmt)
    logger.addHandler(ch)
    return logger

log = _setup_logging()


def _get_model_token_limit(model_name: str, api_key: str) -> int:
    """Fetch outputTokenLimit for *model_name* from the Gemini model metadata API.
    Falls back to _GEMINI_TOKEN_FALLBACK on any error.
    Thread-safe: lock prevents duplicate HTTP calls when multiple Gemini workers
    hit a cache miss for the same model simultaneously.
    """
    # Fast path: check without lock first (GIL makes dict reads atomic in CPython)
    if model_name in _model_token_limit_cache:
        return _model_token_limit_cache[model_name]
    with _model_token_limit_lock:
        # Re-check inside lock — another thread may have populated it while we waited
        if model_name in _model_token_limit_cache:
            return _model_token_limit_cache[model_name]
        url = (
            "https://generativelanguage.googleapis.com/v1beta/models/{}?key={}"
            .format(model_name, api_key)
        )
        try:
            req = urllib.request.Request(url, headers={"Accept": "application/json"})
            with urllib.request.urlopen(req, timeout=10, context=_SSL_CTX) as r:
                data = json.loads(r.read().decode("utf-8"))
            limit = int(data.get("outputTokenLimit", _GEMINI_TOKEN_FALLBACK))
            log.info("Gemini model %r outputTokenLimit=%d", model_name, limit)
        except Exception as _e:
            limit = _GEMINI_TOKEN_FALLBACK
            _safe_url = re.sub(r"(key=)[^&]+", r"\1<redacted>", url)
            # IMPORTANT: Do NOT use traceback.format_exc() here — the HTTPError
            # object's .url attribute stores the original URL with the API key.
            # Only log _e (its string repr) and the pre-redacted _safe_url.
            log.warning("Could not fetch outputTokenLimit for %r (url=%s err=%s) — using fallback %d",
                        model_name, _safe_url, _e, limit)
        _model_token_limit_cache[model_name] = limit
        return limit


def log_banner(video_path, query, lang):
    log.info("=" * 70)
    log.info("SESSION START")  # timestamp comes from the log formatter
    log.info("video  : %s", video_path or "(none)")
    log.info("query  : %s", query)
    log.info("lang   : %s", lang)
    log.info("=" * 70)

# ─────────────────────────────────────────────────────────────────────────────
# CACHE / TEMP DIRECTORIES  (defined early so subliminal block can use CACHE_DIR)
# ─────────────────────────────────────────────────────────────────────────────

CACHE_DIR  = SUBFINDER_DIR / "cache"
try:
    CACHE_DIR.mkdir(parents=True, exist_ok=True)
except OSError as _e:
    log.error("could not create CACHE_DIR %s: %s", CACHE_DIR, _e)

# ─────────────────────────────────────────────────────────────────────────────
# SUBLIMINAL
# ─────────────────────────────────────────────────────────────────────────────

SUBLIMINAL_OK = False
SUBLIMINAL_PROVIDERS_LIST = []
# subliminal's compute_score maximum — used to normalise raw scores to [0, 1].
# The theoretical max varies by provider but 120 covers all known cases.
_SUBLIMINAL_SCORE_MAX = 120.0

try:
    import subliminal
    from subliminal import Video, ProviderPool, region as subliminal_region
    from babelfish import Language

    try:
        _cache_region = subliminal_region
        _cache_region.configure("dogpile.cache.dbm", expiration_time=3600*24,
                                arguments={"filename": str(CACHE_DIR / "subliminal_cache.dbm")})
    except Exception as _ce:
        log.debug("dogpile cache setup skipped: %s", _ce)

    _wanted = ["opensubtitles", "opensubtitlescom"]
    try:
        from subliminal.core import provider_manager as _pm
        _installed = {ext.name for ext in _pm}
        SUBLIMINAL_PROVIDERS_LIST = [p for p in _wanted if p in _installed]
        log.info("subliminal installed providers: %s", sorted(_installed))
        log.info("subliminal will USE: %s", SUBLIMINAL_PROVIDERS_LIST)
    except Exception as _pe:
        SUBLIMINAL_PROVIDERS_LIST = list(_wanted)
        log.warning("provider_manager probe failed: %s", _pe)

    SUBLIMINAL_OK = True
    log.info("subliminal %s ready", subliminal.__version__)

except ImportError:
    log.warning("subliminal not found. Run: pip install subliminal babelfish dogpile.cache")
except Exception as _e:
    log.error("subliminal init error: %s\n%s", _e, traceback.format_exc())

# ─────────────────────────────────────────────────────────────────────────────
# CONSTANTS
# ─────────────────────────────────────────────────────────────────────────────

# Single source of truth for language support. CODE_TO_LANG, ISO3_TO_LANG, and
# ISO1_TO_BABELFISH are all derived from or keyed to LANGUAGES — add new languages
# here first, then add the ISO 639-1↔639-2 mapping to ISO1_TO_BABELFISH below.
LANGUAGES = {
    "Arabic": "ar", "English": "en", "French": "fr", "Spanish": "es",
    "German": "de", "Italian": "it", "Portuguese": "pt", "Russian": "ru",
    "Chinese": "zh", "Japanese": "ja", "Korean": "ko", "Turkish": "tr",
    "Hebrew": "he", "Dutch": "nl", "Polish": "pl", "Swedish": "sv",
    "Norwegian": "no", "Danish": "da", "Finnish": "fi", "Czech": "cs",
    "Hungarian": "hu", "Romanian": "ro", "Bulgarian": "bg", "Greek": "el",
    "Croatian": "hr", "Serbian": "sr", "Ukrainian": "uk", "Thai": "th",
    "Indonesian": "id", "Vietnamese": "vi", "Farsi": "fa", "Malay": "ms",
    "Urdu": "ur",
}
CODE_TO_LANG = {v: k for k, v in LANGUAGES.items()}

def _lang_code_tag(language: str) -> str:
    """Return a short 2-letter uppercase code for display in the release column.

    Handles both ISO codes ('ar' → 'AR') and full names ('Arabic' → 'AR').
    Falls back to the first 2 chars uppercased for unknown values.
    """
    if not language:
        return ""
    lc = language.strip().lower()
    # Already a short code (2–3 chars)?
    if len(lc) <= 3:
        return lc[:2].upper()
    # Full language name → look up its code
    code = LANGUAGES.get(language.strip(), "")
    if code:
        return code[:2].upper()
    # Fallback
    return language[:2].upper()

ISO1_TO_BABELFISH = {
    "ar":"ara","en":"eng","fr":"fra","es":"spa","de":"deu","it":"ita","pt":"por",
    "ru":"rus","zh":"zho","ja":"jpn","ko":"kor","tr":"tur","he":"heb","nl":"nld",
    "pl":"pol","sv":"swe","no":"nor","da":"dan","fi":"fin","cs":"ces","hu":"hun",
    "ro":"ron","bg":"bul","el":"ell","hr":"hrv","sr":"srp","uk":"ukr","th":"tha",
    "id":"ind","vi":"vie","fa":"fas","ms":"msa","ur":"urd",
}

# ISO 639-2 (three-letter) → human-readable language name.
# Built from inverting ISO1_TO_BABELFISH then overlaying the LANGUAGES dict,
# plus extras not covered by the two-letter set.
ISO3_TO_LANG: dict = {iso3: CODE_TO_LANG[iso1]
                      for iso1, iso3 in ISO1_TO_BABELFISH.items()
                      if iso1 in CODE_TO_LANG}
# Overlay explicit overrides for codes that differ from the auto-derived values
# (e.g. "zho"/"jpn"/"kor" which may not be in CODE_TO_LANG if the 2-letter codes map differently)
_ISO3_EXTRAS = {
    "zho": "Chinese", "jpn": "Japanese", "kor": "Korean",
    "por": "Portuguese", "deu": "German", "fra": "French",
    "spa": "Spanish", "rus": "Russian", "ara": "Arabic",
    "tur": "Turkish", "heb": "Hebrew", "nld": "Dutch",
    "pol": "Polish", "swe": "Swedish", "nor": "Norwegian",
    "dan": "Danish", "fin": "Finnish", "ces": "Czech",
    "hun": "Hungarian", "ron": "Romanian", "bul": "Bulgarian",
    "ell": "Greek",  "hrv": "Croatian", "srp": "Serbian",
    "ukr": "Ukrainian", "tha": "Thai",  "ind": "Indonesian",
    "vie": "Vietnamese", "fas": "Farsi", "msa": "Malay",
    "urd": "Urdu", "eng": "English", "ita": "Italian",
}
for _k, _v in _ISO3_EXTRAS.items():
    if _k not in ISO3_TO_LANG:
        ISO3_TO_LANG[_k] = _v
del _k, _v, _ISO3_EXTRAS

# Chrome UA version — bump this constant when CDNs start rejecting the current version.
# Check https://chromiumdash.appspot.com/releases for the latest stable channel version.
_CHROME_UA_VERSION = 136
# Intentionally reports Windows NT on all platforms — avoids platform-specific API
# blocks on some CDNs that reject Linux/macOS user-agents as bots.
_UA_CHROME = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/{}.0.0.0 Safari/537.36"
).format(_CHROME_UA_VERSION)

HTTP_HEADERS = {
    "User-Agent": _UA_CHROME,
    "Accept-Language": "en-US,en;q=0.9",
    "Accept": "application/json, text/html, */*",
}

# Subliminal-compatible User-Agent string.  Defined here for reference but currently
# unused — all providers send _UA_CHROME.  Kept in case a provider requires the
# subliminal UA to avoid rate-limit fragmentation with existing subliminal tokens.
_UA_SUBLIMINAL = "subliminal/2.0"

TEMP_DIR = Path(tempfile.gettempdir()) / "mpv_subs"
try:
    TEMP_DIR.mkdir(parents=True, exist_ok=True)
except OSError as _e:
    log.error("could not create TEMP_DIR %s: %s", TEMP_DIR, _e)

# Index and session cache live in cache/ — temp subtitle files are in the system temp dir.
CACHE_INDEX_FILE   = CACHE_DIR / "subtitle_cache_index.json"
SESSION_CACHE_FILE = CACHE_DIR / "last_session.json"
TRIGGER_FILE       = CACHE_DIR / "subtitle_trigger.txt"

# Used by get_playing_video() and get_mpv_title() for single-pipe IPC reads.
# load_subtitle_into_mpv() tries multiple pipe names independently.
# Windows named-pipe paths for mpv IPC.  On Linux/macOS the default Unix socket
# paths are used instead (see _ipc_command).
MPV_IPC_PIPES = [r"\\.\pipe\mpvpipe", r"\\.\pipe\mpvsocket", r"\\.\pipe\mpv-ipc"]
MPV_IPC_PIPE  = MPV_IPC_PIPES[0]   # default pipe (Windows); kept for legacy call sites

_RE_GENERIC = re.compile(
    r"^(index|play|watch|stream|video|episode|media|content|file|files|download|"
    r"hls|dash|manifest|chunk|seg|playlist|master|cdn|static|assets|v[0-9]+|dld)$", re.I)
_RE_UUID  = re.compile(r"^[0-9a-f]{8}(-[0-9a-f]{4}){3}-[0-9a-f]{12}$", re.I)
_RE_HASH  = re.compile(r"^[0-9a-f]{16,}$", re.I)
_RE_SXEX  = re.compile(r"[Ss]\d{1,2}[Ee][Pp]?\d{1,2}")
_RE_YEAR  = re.compile(r"(^|[.\-_ (])(19|20)\d{2}([.\-_ )]|$)")
_RE_VEXT  = re.compile(r"\.(mp4|mkv|avi|mov|wmv|ts|m4v|webm|flv|m3u8|mpd)$", re.I)
_RE_TAGS  = re.compile(
    r"[.\-\_\s](BluRay|BRRip|BDRip|WEBRip|WEB[\-\.]?DL|HDTV|DVDRip|HDRip|REMUX|BDREMUX|IMAX|"
    r"2160p|1080p|720p|480p|4K|UHD|x264|x265|HEVC|AVC|H\.?264|H\.?265|H265|XviD|DivX|"
    r"HDR10?|SDR|DoVi|Dolby\.?Vision|"
    r"AAC|AC3|DTS|MP3|DD5|TrueHD|Atmos|REPACK|PROPER|EXTENDED|THEATRICAL|UNRATED|DC|"
    r"NF|AMZN|HULU|DSNP|ATVP|MAX|PCOK|YTS|YIFY|RARBG|FGT|GalaxyRG|SPARKS|MVO|STEPonee)"
    r"([.\-\_\s].*)?$", re.I)
# Season/episode patterns used by parse_season_episode — compiled once at module level.
_RE_SE_PATTERNS = [
    re.compile(r"[Ss](\d{1,2})[.\-_ ]?[Ee][Pp]?(\d{1,2})(?!\d)"),
    re.compile(r"(?<!\d)(\d{1,2})[xX](\d{2})(?!\d)"),
    re.compile(r"[Ss]eason[.\s]*(\d{1,2})[.\s]*[Ee]pisode[.\s]*(\d{1,2})"),
]
# Alias for _RE_SE_PATTERNS[0] — cleaner at call sites.
_RE_SE_INLINE    = _RE_SE_PATTERNS[0]
# Resolution guard used in parse_season_episode to prevent "720p" → S07E20 false matches.
_RE_RESOLUTION   = re.compile(r"\d{3,4}p", re.I)
# Codec-string stripper used in parse_season_episode — compiled once at module level
# (not inside the function) to avoid re-compiling on every subtitle-scoring call.
_RE_CODEC_STRIP  = re.compile(r"[xXhH]\d{3,4}|[Xx][Vv][Ii][Dd]|[Dd][Ii][Vv][Xx]")
# Episode-tag detector used in _dl_worker and _dl_ok — compiled once at module level.
# The optional [.\-_ ]? between the season and episode parts mirrors _RE_SE_PATTERNS[0]
# so that dotted releases like "Show.S01.E05.HDTV" are not misclassified as season packs.
# Also covers: Ep01/EP01 prefix style, multi-episode ranges (S01E01-E03 / S01E01E02).
_RE_EP_TAG = re.compile(
    r"[Ss]\d{1,2}[.\-_ ]?[Ee][Pp]?\d{1,2}(?:[.\-_ ]?[Ee]\d{1,2})?"  # S01E05 / S01E01-E03
    r"|\d{1,2}[xX\u00d7]\d{2}"                                         # 1x05 / 1×05 (Unicode ×)
    r"|(?<![A-Za-z])[Ee][Pp]\d{1,2}(?!\d)"                            # Ep01 / EP05
)
# Valid subtitle file extensions — defined once at module level.
_SUB_EXTENSIONS = {".srt", ".ass", ".ssa", ".vtt", ".sub"}
# Bare resolution numbers that must not be parsed as season/episode (e.g. 720 → S07E20).
_BARE_RESOLUTION_BLOCK = frozenset(("480", "720", "1080", "2160",
                                    "264", "265", "360", "540"))   # also common codec numbers
# Unicode script ranges used to detect untranslated Gemini responses (Layer 8).
# Maps ISO 639-1 language code → (lo, hi) inclusive codepoint range for the
# primary script of that language.  Rebuilt once at import time, never inside loops.
_SCRIPT_RANGES: dict = {
    "ar": (0x0600, 0x06FF), "he": (0x0590, 0x05FF),
    "zh": (0x4E00, 0x9FFF), "ja": (0x4E00, 0x9FFF),
    "ko": (0xAC00, 0xD7AF), "ru": (0x0400, 0x04FF),
    "uk": (0x0400, 0x04FF), "bg": (0x0400, 0x04FF),
    "hi": (0x0900, 0x097F), "th": (0x0E00, 0x0E7F),
    "el": (0x0370, 0x03FF),
}
# Per-script wrong-language detection threshold (Layer 8).
# CJK scripts appear less frequently in mixed text, so a lower threshold avoids
# false escalation. RTL and Cyrillic scripts should dominate translated output.
_SCRIPT_WRONG_LANG_THRESHOLD: dict = {
    "zh": 0.08, "ja": 0.08, "ko": 0.08,   # CJK: mixed scripts common
    "ar": 0.20, "he": 0.20,                # RTL: should dominate
    "th": 0.15, "hi": 0.15,               # Indic
}
_SCRIPT_WRONG_LANG_THRESHOLD_DEFAULT = 0.15
# OpenSubtitles uploader ranks considered trusted for scoring purposes.
# Defined at module level so it is not rebuilt on every subtitle result scored.
_TRUSTED_RANKS: frozenset = frozenset({
    "trusted member", "administrator", "moderator",
    "translator", "application developers", "trusted",
    "super admin", "subtranslator", "os legend",
})

# Matches any URI scheme (http, https, rtsp, ftp, mms, etc.).
# Used to distinguish local file paths from network streams / URLs.
_URL_SCHEME_RE = re.compile(r"^[a-zA-Z][a-zA-Z\d+\-.]*://")

# ── Compiled geometry regex patterns ─────────────────────────────────────────
# Used in window save/restore, clamp, and resize logic throughout the GUI.
# Defined once at module level — compiled patterns are faster and avoid the
# regex cache churn of repeated re.match(r"...", ...) inline calls.
_GEO_RE      = re.compile(r"(\d+)x(\d+)([+-]\d+)([+-]\d+)")   # full WxH±X±Y  (macOS uses -N not +-N)
_GEO_SIZE_RE = re.compile(r"(\d+)x(\d+)(.*)")                  # WxH with optional tail
# These constants name every magic number used in _score_oscom_result and the
# SubDL equivalent so intent is clear and tuning happens in one place.
_SCORE_AI_TRANSLATED      = 0.45   # hard cap for machine/AI-translated subtitles
_SCORE_HASH_BASE          = 0.93   # confirmed byte-level file match (sync guaranteed)
_SCORE_HASH_TRUSTED_BONUS = 0.04   # bonus when uploader is a trusted rank
_SCORE_HASH_VOTE_BONUS    = 0.02   # bonus for highly-rated hash-matched subtitle
_SCORE_QUERY_BASE         = 0.72   # title-query match (no sync guarantee)
_SCORE_QUERY_CAP          = 0.89   # ceiling for all query-path bonuses
_SCORE_TRUSTED_BONUS      = 0.06   # uploader trusted rank bonus (query path)
_SCORE_RATING_WEIGHT      = 0.08   # max rating bonus (ratings 0–10 → 0–0.08)
_SCORE_POP_WEIGHT         = 0.05   # max popularity bonus (log-dampened)
_SCORE_MOMENTUM_BONUS     = 0.01   # recent-download momentum bonus
_SCORE_RELEASE_EXACT      = 0.15   # exact release-name match bonus (capped at 0.97)
_SCORE_RELEASE_PARTIAL    = 0.07   # partial release-name match bonus
_SCORE_RELEASE_EXACT_CAP  = 0.97   # ceiling for exact release match
_SCORE_HASH_MAX           = 0.99   # absolute ceiling for hash-matched score

# ─────────────────────────────────────────────────────────────────────────────
# THEMES
# ─────────────────────────────────────────────────────────────────────────────

THEMES = {
    "Default": {
        "bg":"#000000","surface":"#03060a","card":"#101a2b","border":"#16233a",
        "accent":"#4d9de0","danger":"#ff4d5a","text":"#eaf2ff","dim":"#8999b8",
        "green":"#53a1ed","success":"#53a1ed","yellow":"#ffd166","hover":"#15243f","sel_bg":"#1a2f57","sel_fg":"#eaf2ff",
    },
    "Deep Blue": {
        "bg":"#060912","surface":"#0b1020","card":"#101828","border":"#172240",
        "accent":"#4d9de0","danger":"#e84855","text":"#ccd6f6","dim":"#3e4d6e",
        "green":"#43d9ad","success":"#43d9ad","yellow":"#ffd166","hover":"#131d35","sel_bg":"#182650","sel_fg":"#ccd6f6",
    },

    "AMOLED": {
        "bg":"#000000","surface":"#0a0a0a","card":"#111111","border":"#222222",
        "accent":"#00bfff","danger":"#ff4444","text":"#ffffff","dim":"#666666",
        "green":"#00e676","success":"#00e676","yellow":"#ffcc00","hover":"#1a1a1a","sel_bg":"#003366","sel_fg":"#ffffff",
    },
    "Carbon": {
        "bg":"#0d0d0d","surface":"#151515","card":"#1c1c1c","border":"#2a2a2a",
        "accent":"#4cc9f0","danger":"#ff4d6d","text":"#f1f1f1","dim":"#8a8a8a",
        "green":"#38d9a9","success":"#38d9a9","yellow":"#ffd43b","hover":"#222222","sel_bg":"#2c2c2c","sel_fg":"#ffffff",
    },

    "Classic Dark": {
        "bg":"#0d1117","surface":"#161b22","card":"#1e2530","border":"#30363d",
        "accent":"#58a6ff","danger":"#f78166","text":"#e6edf3","dim":"#7d8590",
        "green":"#3fb950","success":"#3fb950","yellow":"#d29922","hover":"#2a3441","sel_bg":"#1f4068","sel_fg":"#e6edf3",
    },
    "Slate": {
        "bg":"#111827","surface":"#1f2937","card":"#273449","border":"#374151",
        "accent":"#60a5fa","danger":"#f87171","text":"#e5e7eb","dim":"#9ca3af",
        "green":"#34d399","success":"#34d399","yellow":"#fbbf24","hover":"#2c3a50","sel_bg":"#334155","sel_fg":"#e5e7eb",
    },
    "Tokyo Night": {
        "bg":"#1a1b26","surface":"#16161e","card":"#1f2335","border":"#292e42",
        "accent":"#7aa2f7","danger":"#f7768e","text":"#c0caf5","dim":"#565f89",
        "green":"#9ece6a","success":"#9ece6a","yellow":"#e0af68","hover":"#1f2335","sel_bg":"#283457","sel_fg":"#c0caf5",
    },
    "Midnight Blue": {
        "bg":"#0a0e1a","surface":"#0f1525","card":"#151d35","border":"#1e2d50",
        "accent":"#4d9de0","danger":"#e84855","text":"#ccd6f6","dim":"#4a5578",
        "green":"#43d9ad","success":"#43d9ad","yellow":"#ffd166","hover":"#1a2540","sel_bg":"#1e3060","sel_fg":"#ccd6f6",
    },
    "Obsidian": {
        "bg":"#0b0f14","surface":"#121821","card":"#161e2b","border":"#1f2a3a",
        "accent":"#5aa9ff","danger":"#ff5d73","text":"#e6edf3","dim":"#7a8599",
        "green":"#4fd1a5","success":"#4fd1a5","yellow":"#f6c177","hover":"#1b2433","sel_bg":"#22304a","sel_fg":"#e6edf3",
    },
    "Nord": {
        "bg":"#2e3440","surface":"#3b4252","card":"#434c5e","border":"#4c566a",
        "accent":"#88c0d0","danger":"#bf616a","text":"#eceff4","dim":"#616e88",
        "green":"#a3be8c","success":"#a3be8c","yellow":"#ebcb8b","hover":"#3b4252","sel_bg":"#4c566a","sel_fg":"#eceff4",
    },
    "Nordic Ice": {
        "bg":"#1e222a","surface":"#2a2f3a","card":"#313743","border":"#3e4451",
        "accent":"#88c0d0","danger":"#bf616a","text":"#e5e9f0","dim":"#81a1c1",
        "green":"#a3be8c","success":"#a3be8c","yellow":"#ebcb8b","hover":"#373d4a","sel_bg":"#434c5e","sel_fg":"#e5e9f0",
    },

    "Dracula": {
        "bg":"#282a36","surface":"#21222c","card":"#343746","border":"#44475a",
        "accent":"#bd93f9","danger":"#ff5555","text":"#f8f8f2","dim":"#6272a4",
        "green":"#50fa7b","success":"#50fa7b","yellow":"#f1fa8c","hover":"#3d3f4e","sel_bg":"#44475a","sel_fg":"#f8f8f2",
    },
    "Mocha": {
        "bg":"#1e1e2e","surface":"#181825","card":"#313244","border":"#45475a",
        "accent":"#cba6f7","danger":"#f38ba8","text":"#cdd6f4","dim":"#585b70",
        "green":"#a6e3a1","success":"#a6e3a1","yellow":"#f9e2af","hover":"#3a3c52","sel_bg":"#45475a","sel_fg":"#cdd6f4",
    },
    "Rosé Pine": {
        "bg":"#191724","surface":"#1f1d2e","card":"#26233a","border":"#403d52",
        "accent":"#c4a7e7","danger":"#eb6f92","text":"#e0def4","dim":"#6e6a86",
        "green":"#31748f","success":"#31748f","yellow":"#f6c177","hover":"#26233a","sel_bg":"#403d52","sel_fg":"#e0def4",
    },
    "Violet Haze": {
        "bg":"#140f1f","surface":"#1d1530","card":"#261c3f","border":"#3a2c5a",
        "accent":"#a78bfa","danger":"#fb7185","text":"#ede9fe","dim":"#9f7aea",
        "green":"#4ade80","success":"#4ade80","yellow":"#facc15","hover":"#2c2150","sel_bg":"#3b2f6b","sel_fg":"#ede9fe",
    },

    "Everforest": {
        "bg":"#2d353b","surface":"#272e33","card":"#343f44","border":"#4a555b",
        "accent":"#7fbbb3","danger":"#e67e80","text":"#d3c6aa","dim":"#7a8478",
        "green":"#a7c080","success":"#a7c080","yellow":"#dbbc7f","hover":"#3d484d","sel_bg":"#4a555b","sel_fg":"#d3c6aa",
    },
    "Emerald Night": {
        "bg":"#0b1412","surface":"#12201c","card":"#18302a","border":"#24423a",
        "accent":"#10b981","danger":"#ef4444","text":"#d1fae5","dim":"#6ee7b7",
        "green":"#34d399","success":"#34d399","yellow":"#facc15","hover":"#1b3a33","sel_bg":"#1f4d44","sel_fg":"#d1fae5",
    },

    "Midnight Neon": {
        "bg":"#070b14","surface":"#0f1624","card":"#151f33","border":"#1f2d4d",
        "accent":"#00e5ff","danger":"#ff3b5c","text":"#dbeafe","dim":"#5b6b8c",
        "green":"#00ffab","success":"#00ffab","yellow":"#ffe66d","hover":"#18243b","sel_bg":"#1f3a5f","sel_fg":"#dbeafe",
    },
    "Cyberpunk": {
        "bg":"#0d0d1a","surface":"#111128","card":"#16163a","border":"#2a2a6e",
        "accent":"#00ffff","danger":"#ff003c","text":"#e0e0ff","dim":"#6060a0",
        "green":"#00ff9f","success":"#00ff9f","yellow":"#ffe600","hover":"#1a1a40","sel_bg":"#1a1a6e","sel_fg":"#00ffff",
    },

    "Gruvbox": {
        "bg":"#282828","surface":"#1d2021","card":"#32302f","border":"#504945",
        "accent":"#83a598","danger":"#fb4934","text":"#ebdbb2","dim":"#928374",
        "green":"#b8bb26","success":"#b8bb26","yellow":"#fabd2f","hover":"#3c3836","sel_bg":"#504945","sel_fg":"#ebdbb2",
    },

    "Windows Light": {
        "bg":"#f3f3f3","surface":"#ffffff","card":"#fbfbfb","border":"#e5e5e5",
        "accent":"#0067c0","danger":"#c42b1c","text":"#1a1a1a","dim":"#605e5c",
        "green":"#0f7b0f","success":"#0f7b0f","yellow":"#9d5d00","hover":"#f5f5f5","sel_bg":"#cce0f2","sel_fg":"#1a1a1a",
    },
    # ── end of themes ──────────────────────────────────────────────────────────
}

C = dict(THEMES["Default"])  # active theme colours — rebound (not mutated in-place) at runtime
# All readers access C by name so they pick up the new binding automatically.
# Note: code that holds a direct reference (e.g. 'colors = C') before a theme
# change will see stale values — always read C[key] at call time, not at import.
def get_theme() -> dict:
    """Return the currently active theme colour dict.
    Prefer this over direct C access in non-App code for forward-compat."""
    return C

# ─────────────────────────────────────────────────────────────────────────────
# CACHE INDEX
# ─────────────────────────────────────────────────────────────────────────────

# If the temp dir exceeds this size, oldest indexed files are evicted until
# it fits.  Orphan/unindexed files are always subject to the 48-hour rule
# regardless of this limit.
_CACHE_MAX_BYTES       = 200 * 1024 * 1024   # 200 MB
# Compact the subliminal DBM file when it grows beyond this size.
_DBM_COMPACT_THRESHOLD = 20 * 1024 * 1024    # 20 MB
# Maximum JSON size for the multi-session cache file before oldest sessions are evicted.
_SESSION_CACHE_MAX_BYTES = 5 * 1024 * 1024   # 5 MB
# Subtitle cache index entries older than this many days are expired on load.
_CACHE_INDEX_TTL_DAYS  = 30
# Guards all load → mutate → save sequences on the cache index so that the
# background cleanup thread and main-thread downloads cannot interleave and
# cause lost-update races (VUL-04).
_cache_index_lock = threading.Lock()


def _load_cache_index(autosave: bool = True) -> dict:
    try:
        data = json.loads(CACHE_INDEX_FILE.read_text(encoding="utf-8"))
        ttl_cutoff = _time_module.time() - _CACHE_INDEX_TTL_DAYS * 86400

        # ── Pass 1: collect surviving file-path entries ───────────────────────
        # Build a set of sub_ids whose files are still alive so we can use it
        # to prune the metadata entries in pass 2.
        surviving_sub_ids = set()
        pruned = {}
        for k, v in data.items():
            if k.startswith(("dlurl:", "pack:", "direct_url:")):
                continue  # handled in pass 2
            # Guard: non-string values (corrupted cache) would raise TypeError in Path(v)
            if not isinstance(v, str):
                log.debug("cache index: skipping non-string value for key %r", k)
                continue
            p = Path(v)
            if not p.is_file():
                continue  # file gone — drop
            try:
                _mtime = p.stat().st_mtime
            except FileNotFoundError:
                continue  # deleted between is_file() and stat() — treat as gone
            if _mtime < ttl_cutoff:
                try:
                    p.unlink(missing_ok=True)
                    log.debug("cache TTL evict: %s", p)
                except Exception:
                    pass
                continue  # expired — drop
            pruned[k] = v
            surviving_sub_ids.add(k)

        # ── Pass 2: prune metadata entries whose backing data is gone ─────────
        for k, v in data.items():
            if k.startswith("dlurl:"):
                # value is a sub_id — keep only if that sub_id survived
                if v in surviving_sub_ids:
                    pruned[k] = v
                else:
                    log.debug("cache drop stale dlurl: %s", k)

            elif k.startswith("direct_url:"):
                # Keep direct download URLs unconditionally — they are metadata,
                # not file pointers.  Tying eviction to surviving_sub_ids caused
                # permanent re-download failures: the moment the temp .srt file
                # was deleted (cleanup thread, Windows, or user), the URL was
                # also evicted, so cached-session downloads would fail for any
                # subtitle whose release name does not match OpenSubtitles search
                # (e.g. Arabic releases like AvistaZ which return 0 results on
                # a text query but always work via the stored direct URL).
                pruned[k] = v

            elif k.startswith("pack:"):
                # value is JSON with a zip_key — keep only if the archive still exists
                try:
                    meta = json.loads(v)
                    zip_key = meta.get("zip_key", "")
                    zip_ext = meta.get("zip_ext", ".zip")
                    # _archive_dest_for is defined in the SubDL engine section (~line 4086).
                    # This forward reference is safe: _load_cache_index is only ever called
                    # at runtime (never at import time), by which point all module-level
                    # definitions are complete.
                    zip_path = _archive_dest_for(zip_key, zip_ext, label=meta.get("label", ""))
                    if zip_key and zip_path.is_file():
                        pruned[k] = v
                    else:
                        log.debug("cache drop stale pack: %s (archive gone)", k)
                except Exception as _pack_exc:
                    log.debug("cache drop malformed pack entry %r: %s", k, _pack_exc)

        if autosave and len(pruned) != len(data):
            _save_cache_index(pruned)
        return pruned
    except Exception as _exc:
        log.warning("cache index load failed (returning empty): %s", _exc)
        return {}

def _save_cache_index(index: dict):
    # Atomic write: write to a temp file first, then rename over the target.
    # This prevents a partial/corrupt index if the process is killed mid-write.
    # Suffix ".writing" distinguishes from SESSION_CACHE_FILE's ".tmp" in the same dir.
    tmp = CACHE_INDEX_FILE.with_name(CACHE_INDEX_FILE.name + ".writing")
    try:
        tmp.write_text(json.dumps(index, indent=2), encoding="utf-8")
        tmp.replace(CACHE_INDEX_FILE)
        log.debug("cache index saved: %d entries", len(index))
    except Exception as e:
        log.warning("cache index save failed: %s", e)
        try:
            tmp.unlink(missing_ok=True)
        except Exception:
            pass

def _primary_providers(oscom_enabled: bool, direct_ok: bool = False) -> set:
    """Single source of truth for which providers are 'primary' vs 'secondary'.

    v3 providers (opensubtitlescom) are ALWAYS primary.
    v2 providers (opensubtitles) are ALWAYS secondary (collapsed).
    SubDL and the direct OS.com engine are always primary.

    direct_ok=True means the direct engine returned results this session — in that
    case subliminal results are excluded entirely (not even shown as secondary).
    The oscom_enabled checkbox only controls whether the direct REST search fires;
    it has no effect on which generation of subliminal providers is primary.
    """
    if direct_ok:
        # Direct worked — only direct and SubDL are relevant
        return {"opensubtitlescom_direct", "subdl"}
    # v3 subliminal providers are primary regardless of the checkbox state.
    # v2 legacy providers are always secondary so they appear in the collapsed section.
    # opensubtitlescom_direct is only primary when the OS.com toggle is enabled.
    primaries = {"subdl", "opensubtitlescom"}
    if oscom_enabled:
        primaries.add("opensubtitlescom_direct")
    return primaries

def _compact_subliminal_dbm():
    """
    Rewrite the subliminal DBM cache when it exceeds _DBM_COMPACT_THRESHOLD.
    DBM files accumulate dead space as entries expire; compacting recovers it.
    Only runs when dogpile/subliminal is available and the file is large enough.

    Uses dbm.whichdb() to detect which backend wrote the file (gdbm, ndbm,
    dumbdbm, etc.) so we open it with the right module regardless of the
    suffix convention the current platform uses.
    """
    import dbm

    if not SUBLIMINAL_OK:
        return

    dbm_base = str(CACHE_DIR / "subliminal_cache.dbm")

    # Collect all files that belong to this DBM (any suffix variant).
    # Different backends produce different files:
    #   gdbm  → .dbm.db  or  .dbm       (single file)
    #   ndbm  → .dbm.dir + .dbm.pag     (two files)
    #   dumbdbm → .dbm.dat + .dbm.dir + .dbm.bak  (three files)
    candidate_files = list(CACHE_DIR.glob("subliminal_cache.dbm*"))
    if not candidate_files:
        return

    # Only compact if at least one file exceeds the threshold.
    if not any(f.is_file() and f.stat().st_size > _DBM_COMPACT_THRESHOLD
               for f in candidate_files):
        return

    log.info("subliminal DBM exceeds %d MB — compacting", _DBM_COMPACT_THRESHOLD // (1024 * 1024))

    # dbm.whichdb() identifies which backend wrote the database.
    # It returns a module name string (e.g. 'dbm.gnu', 'dbm.ndbm', 'dbm.dumb')
    # or None if the file is unrecognised.  We open with dbm.open() which
    # honours the detected backend automatically (it calls the right sub-module).
    try:
        detected = dbm.whichdb(dbm_base)
        if detected is None:
            log.debug("DBM compact: could not detect backend for %r — skipping", dbm_base)
            return
    except Exception as _we:
        log.debug("DBM compact: whichdb failed: %s — skipping", _we)
        return

    tmp_base = str(CACHE_DIR / "subliminal_cache_tmp.dbm")

    # Stream directly src → dst without loading all entries into memory (O(1) RAM).
    _kept = 0
    try:
        with dbm.open(dbm_base, "r") as src, dbm.open(tmp_base, "n") as dst:
            for key in src.keys():
                try:
                    dst[key] = src[key]
                    _kept += 1
                except Exception as _we:
                    log.warning("DBM compact: failed to copy key %r: %s — entry dropped", key, _we)
    except Exception as _re:
        log.debug("DBM compact: error during streaming copy: %s — skipping", _re)
        # Clean up any partial temp files
        for _tf in CACHE_DIR.glob("subliminal_cache_tmp.dbm*"):
            try:
                _tf.unlink(missing_ok=True)
            except Exception:
                pass
        return

    # Atomic swap: rename temp → target FIRST (overwriting), then clean up any
    # remaining tmp orphans.  Path.replace() overwrites the destination atomically
    # on POSIX (rename syscall); on Windows it is not atomic but is safe because
    # the destination is the live DBM and will be recreated by subliminal if lost.
    # This order ensures that if the process is killed after replace() but before
    # cleanup, the live cache is the compacted version and no data is lost.
    for new_f in CACHE_DIR.glob("subliminal_cache_tmp.dbm*"):
        try:
            target = CACHE_DIR / new_f.name.replace("subliminal_cache_tmp", "subliminal_cache")
            new_f.replace(target)   # overwrites target atomically on POSIX
        except Exception:
            pass
    # Clean up any remaining tmp files (e.g. if replace raised partway through)
    for tmp_f in CACHE_DIR.glob("subliminal_cache_tmp.dbm*"):
        try:
            tmp_f.unlink(missing_ok=True)
        except Exception:
            pass

    log.info("subliminal DBM compacted: %d entries kept", _kept)

def _cleanup_temp_dir(max_age_hours: int = _TEMP_FILE_MAX_AGE_HOURS):
    # Phase 1 + index read run under the lock so orphan-scan and index-read are
    # one atomic unit — a concurrent download cannot slip a new entry between the
    # cached-set build and the iterdir scan (which would cause the new file to be
    # deleted as "orphan").
    with _cache_index_lock:
        index = _load_cache_index(autosave=False)

        # Build the protected set: only direct file-path values (not dlurl:/pack:/direct_url:
        # metadata values, which are sub_ids or JSON strings, not file paths).
        # Previously used set(index.values()) which incorrectly included metadata strings.
        cached = {v for k, v in index.items()
                  if not k.startswith(("dlurl:", "pack:", "direct_url:"))}
        for key, raw_val in index.items():
            if key.startswith("pack:"):
                try:
                    meta = json.loads(raw_val)
                    zip_key = meta.get("zip_key", "")
                    zip_ext = meta.get("zip_ext", ".zip")
                    if zip_key:
                        cached.add(str(_archive_dest_for(zip_key, zip_ext, label=meta.get("label", ""))))
                except Exception:
                    pass

        # Phase 1: delete orphaned (unindexed) files older than max_age_hours.
        # Runs under _cache_index_lock (see comment above).
        cutoff = _time_module.time() - max_age_hours * 3600
        try:
            for f in TEMP_DIR.iterdir():
                # TOCTOU: f.is_file() then f.stat() — a concurrent delete between
                # the two calls raises FileNotFoundError, caught by the outer except.
                if f.is_file() and str(f) not in cached and f.stat().st_mtime < cutoff:
                    f.unlink(missing_ok=True)
        except Exception as e:
            log.debug("temp cleanup phase 1: %s", e)

    # Phase 2: size cap — lock is RELEASED before the stat/unlink loop to avoid
    # blocking download threads for the duration of all filesystem I/O.
    # Re-acquire only for the _save_cache_index write at the end.
    try:
        # Collect indexed files that actually exist in TEMP_DIR, sorted oldest first
        indexed_files = []
        for f_str in list(cached):
            f = Path(f_str)
            if f.is_file() and f.parent == TEMP_DIR:
                try:
                    indexed_files.append((f.stat().st_mtime, f))
                except Exception:
                    pass
        indexed_files.sort()   # ascending mtime → oldest first

        def _safe_size(f):
            try:
                return f.stat().st_size
            except FileNotFoundError:
                return 0  # deleted between indexed_files build and here — count as 0
        total = sum(_safe_size(f) for _, f in indexed_files)
        if total > _CACHE_MAX_BYTES:
            log.info("temp dir %.1f MB exceeds cap %.1f MB — evicting oldest files",
                     total / (1024*1024), _CACHE_MAX_BYTES / (1024*1024))
            # Re-read index under lock for the eviction path (our cached snapshot
            # may be slightly stale after releasing the lock above).
            with _cache_index_lock:
                index = _load_cache_index(autosave=False)
            # Build a reverse map: file path string → index keys that reference it.
            # Exclude metadata entries (dlurl:/pack:/direct_url:) whose values are
            # sub_ids or JSON strings — not file paths — to avoid bloating the map
            # with spurious keys that can never match str(f).
            path_to_keys: dict = {}
            for k, v in index.items():
                if not k.startswith(("dlurl:", "pack:", "direct_url:")):
                    path_to_keys.setdefault(v, []).append(k)
            for _, f in indexed_files:
                if total <= _CACHE_MAX_BYTES:
                    break
                try:
                    try:
                        sz = f.stat().st_size
                    except FileNotFoundError:
                        # File was concurrently removed — treat size as 0 so
                        # total is not decremented and we do not over-evict
                        # subsequent files to compensate for a ghost entry.
                        sz = 0
                    f.unlink(missing_ok=True)
                    total -= sz
                    log.debug("cache size evict: %s", f)
                    # Remove all index entries that pointed to this file
                    for k in path_to_keys.get(str(f), []):
                        index.pop(k, None)
                except Exception:
                    pass
            # Re-acquire for the index write only
            with _cache_index_lock:
                _save_cache_index(index)
    except Exception as e:
        log.debug("temp cleanup phase 2: %s", e)

    # Phase 3: compact subliminal DBM if it has grown too large (outside lock — no index I/O)
    _compact_subliminal_dbm()

# ─────────────────────────────────────────────────────────────────────────────
# DATA MODEL
# ─────────────────────────────────────────────────────────────────────────────

class Sub:
    __slots__ = ("provider","language","release","score","downloads",
                 "dl_url","sub_id","fmt","_sub_obj","target_episode","file_id",
                 "parent_sub_id")

    def __init__(self, **kw):
        for s in self.__slots__:
            # target_episode and parent_sub_id must default to None so that
            # "is not None" checks correctly distinguish "not set" from a
            # real value.  All other slots default to "" so score/downloads
            # coercions work without an extra None-guard.
            default = None if s in ("target_episode", "parent_sub_id") else ""
            setattr(self, s, kw.get(s, default))
        try:
            self.score = float(self.score) if self.score is not None else 0.0
        except (ValueError, TypeError):
            log.debug("Sub: non-numeric score value %r — defaulting to 0.0", self.score)
            self.score = 0.0
        try:
            self.downloads = int(self.downloads or 0)
        except (ValueError, TypeError):
            log.debug("Sub: non-numeric downloads value %r — defaulting to 0", self.downloads)
            self.downloads = 0

    def score_pct(self):
        return int(min(max(self.score, 0.0), 1.0) * 100)

    def lang_display(self):
        # For translated rows we store the full language name (e.g. "French") directly
        # in self.language.  If it's already in CODE_TO_LANG.values() or longer than 3
        # chars, it's a display name — return it as-is to avoid "FRENCH" via .upper().
        if self.language and len(self.language) > 3:
            return self.language
        # 2-letter ISO 639-1 code (e.g. "en") → look up human name
        if self.language in CODE_TO_LANG:
            return CODE_TO_LANG[self.language]
        # 3-letter ISO 639-2 code (e.g. "eng") — returned by subliminal providers
        if self.language and len(self.language) == 3:
            name = ISO3_TO_LANG.get(self.language.lower())
            if name:
                return name
        return self.language.upper() if self.language else "?"

    def fmt_display(self):
        # SubDL archives often carry no format hint until the file is extracted.
        # "-" is used for all unknown formats for consistency.
        return self.fmt.upper() if self.fmt else "—"

# ── Session-cache JSON helpers ────────────────────────────────────────────────
# JSON session cache (replaces the old pickle format).

_SESSION_CACHE_VERSION = 2   # bump if the schema changes incompatibly

def _sub_to_dict(sub: "Sub") -> dict:
    """Serialise a Sub to a plain dict (omits _sub_obj, which is not serialisable)."""
    return {s: getattr(sub, s, None) for s in Sub.__slots__ if s != "_sub_obj"}

def _dict_to_sub(d: dict) -> "Sub":
    """Deserialise a plain dict back to a Sub, with safe defaults for missing keys."""
    return Sub(**{k: v for k, v in d.items() if k in Sub.__slots__ and k != "_sub_obj"})

def _load_session_cache() -> dict:
    """Load the JSON session cache.  Returns {} on any error or version mismatch.
    Automatically deletes a legacy pickle file if found."""
    # Silently clean up the old insecure pickle file if it still exists.
    legacy_pkl = SESSION_CACHE_FILE.with_suffix(".pkl")
    if legacy_pkl.is_file():
        try:
            legacy_pkl.unlink(missing_ok=True)
            log.info("session cache: removed legacy pickle file %s", legacy_pkl.name)
        except Exception:
            pass
    if not SESSION_CACHE_FILE.is_file():
        return {}
    try:
        raw = json.loads(SESSION_CACHE_FILE.read_text(encoding="utf-8"))
        if not isinstance(raw, dict) or raw.get("_version") != _SESSION_CACHE_VERSION:
            log.info("session cache: version mismatch (expected %d, got %r) — discarding",
                     _SESSION_CACHE_VERSION, raw.get("_version") if isinstance(raw, dict) else "?")
            SESSION_CACHE_FILE.unlink(missing_ok=True)
            return {}
        sessions = raw.get("sessions", {})
        # Reconstruct Sub objects from their serialised dicts
        for vp, sess in list(sessions.items()):
            sess["results"]           = [_dict_to_sub(d) for d in sess.get("results", [])]
            sess["secondary_results"] = [_dict_to_sub(d) for d in sess.get("secondary_results", [])]
        return sessions
    except Exception as e:
        log.warning("session cache load failed (%s) — discarding", e)
        try:
            SESSION_CACHE_FILE.unlink(missing_ok=True)
        except Exception:
            pass
        return {}

def _save_session_cache(sessions: dict):
    """Save the session cache as JSON.  Enforces the _SESSION_CACHE_MAX_BYTES size cap
    by evicting the oldest session(s) until the serialised size is within budget."""
    # Serialise Sub lists to plain dicts
    serialisable = {}
    for vp, sess in sessions.items():
        serialisable[vp] = {
            "video_path":            sess.get("video_path", vp),
            "query":                 sess.get("query", ""),
            "lang":                  sess.get("lang", ""),
            "multi_lang":            sess.get("multi_lang", False),
            "results":               [_sub_to_dict(s) for s in sess.get("results", [])],
            "secondary_results":     [_sub_to_dict(s) for s in sess.get("secondary_results", [])],
            "mpv_primary_sub_id":    sess.get("mpv_primary_sub_id", ""),
            "mpv_secondary_sub_id":  sess.get("mpv_secondary_sub_id", ""),
            "mpv_primary_sids":      sess.get("mpv_primary_sids", {}),
            "mpv_secondary_sids":    sess.get("mpv_secondary_sids", {}),
        }
    payload = {"_version": _SESSION_CACHE_VERSION, "sessions": serialisable}
    # Trim oldest entries until within size cap.
    # The `len(...) <= 1` guard prevents an infinite loop when a single entry
    # already exceeds the cap — in that case we keep it rather than deleting
    # everything and ending up with an empty (but still oversized) payload.
    while True:
        # Use indent=2 to match the actual on-disk write size (avoid systematic underestimation)
        _serialised = json.dumps(payload, ensure_ascii=False, indent=2)
        encoded = _serialised.encode("utf-8")
        if len(encoded) <= _SESSION_CACHE_MAX_BYTES or len(payload["sessions"]) <= 1:
            break
        # Relies on dict insertion-order (Python 3.7+ guarantee).
        # _save_session_snapshot pops and re-inserts on access, so the most-recently-used
        # session is always last — first() == oldest. Do not change eviction order without
        # also updating _save_session_snapshot to maintain this invariant.
        oldest_key = next(iter(payload["sessions"]))
        payload["sessions"].pop(oldest_key)
        log.debug("session cache: evicted oldest entry %r to stay under size cap", oldest_key)
    # Write to a temp file then atomically rename to prevent a partial/corrupt
    # file if the process is killed mid-write.
    _sc_tmp = SESSION_CACHE_FILE.with_suffix(".tmp")
    try:
        _sc_tmp.write_text(_serialised, encoding="utf-8")
        _sc_tmp.replace(SESSION_CACHE_FILE)
    except Exception as e:
        log.warning("Could not save session cache: %s", e)
        try:
            _sc_tmp.unlink(missing_ok=True)
        except Exception:
            pass

def _find_rar_tool() -> tuple[str, str] | tuple[None, None]:
    """Search the system for WinRAR or 7-Zip and return (exe_path, tool_type).
    tool_type is one of: "winrar", "7zip", "bsdtar".
    Returns (None, None) if nothing is found."""

    def _check(path, kind):
        if path and os.path.isfile(path) and (sys.platform == "win32" or os.access(path, os.X_OK)):
            log.debug("_find_rar_tool: found %s → %r", kind, path)
            return path, kind
        return None, None

    # ── 1. Windows registry ───────────────────────────────────────────────────
    try:
        import winreg

        # WinRAR registry keys
        _winrar_reg = [
            (r"SOFTWARE\WinRAR",                                                  "InstallLocation", "winrar"),
            (r"SOFTWARE\WinRAR\Capabilities",                                    "InstallLocation", "winrar"),
            (r"SOFTWARE\Microsoft\Windows\CurrentVersion\Uninstall\WinRAR archiver", "InstallLocation", "winrar"),
            (r"SOFTWARE\WinRAR",                                                  "exe64",           "winrar"),
            (r"SOFTWARE\WinRAR",                                                  "exe32",           "winrar"),
        ]
        # 7-Zip registry keys
        _7z_reg = [
            (r"SOFTWARE\7-Zip",                    "Path",    "7zip"),
            (r"SOFTWARE\7-Zip",                    "Path64",  "7zip"),
            (r"SOFTWARE\7-Zip-Zstandard",          "Path",    "7zip"),
            (r"SOFTWARE\Microsoft\Windows\CurrentVersion\Uninstall\7-Zip", "InstallLocation", "7zip"),
            (r"SOFTWARE\Microsoft\Windows\CurrentVersion\Uninstall\7-Zip", "DisplayIcon",     "7zip"),
        ]

        for _hive, _flag in (
            (winreg.HKEY_LOCAL_MACHINE, winreg.KEY_READ | winreg.KEY_WOW64_32KEY),
            (winreg.HKEY_LOCAL_MACHINE, winreg.KEY_READ | winreg.KEY_WOW64_64KEY),
            (winreg.HKEY_CURRENT_USER,  winreg.KEY_READ | winreg.KEY_WOW64_64KEY),
            (winreg.HKEY_CURRENT_USER,  winreg.KEY_READ | winreg.KEY_WOW64_32KEY),  # 32-bit installs on 64-bit OS
        ):
            for _subkey, _val, _kind in (_winrar_reg + _7z_reg):
                try:
                    with winreg.OpenKey(_hive, _subkey, 0, _flag) as _k:
                        try:
                            _data, _ = winreg.QueryValueEx(_k, _val)
                            _data = _data.strip('"').split(',')[0].strip()
                            if _kind == "winrar":
                                _exes = (
                                    [_data] if _data.lower().endswith(".exe")
                                    else [os.path.join(_data, "UnRAR.exe"),
                                          os.path.join(_data, "Rar.exe")]
                                )
                            else:  # 7zip
                                _exes = (
                                    [_data] if _data.lower().endswith(".exe")
                                    else [os.path.join(_data, "7z.exe"),
                                          os.path.join(_data, "7za.exe")]
                                )
                            for _exe in _exes:
                                p, k = _check(_exe, _kind)
                                if p: return p, k
                        except OSError:
                            pass
                except OSError:
                    pass
    except ImportError:
        pass  # Not on Windows

    # ── 2. Fixed / common paths ───────────────────────────────────────────────
    _fixed_windows = [
        # WinRAR
        (r"C:\Program Files\WinRAR\UnRAR.exe",        "winrar"),
        (r"C:\Program Files\WinRAR\Rar.exe",          "winrar"),
        (r"C:\Program Files (x86)\WinRAR\UnRAR.exe",  "winrar"),
        (r"C:\Program Files (x86)\WinRAR\Rar.exe",    "winrar"),
        # 7-Zip standard installs
        (r"C:\Program Files\7-Zip\7z.exe",            "7zip"),
        (r"C:\Program Files (x86)\7-Zip\7z.exe",      "7zip"),
        (r"C:\Program Files\7-Zip-Zstandard\7z.exe",  "7zip"),
    ] if sys.platform == "win32" else []
    _fixed_posix = [
        # Linux / macOS
        ("/usr/bin/unrar",                                "winrar"),
        ("/usr/local/bin/unrar",                          "winrar"),
        ("/opt/homebrew/bin/unrar",                       "winrar"),
        ("/usr/bin/7z",                                   "7zip"),
        ("/usr/local/bin/7z",                             "7zip"),
        ("/opt/homebrew/bin/7z",                          "7zip"),
    ] if sys.platform != "win32" else []
    for _path, _kind in (_fixed_windows + _fixed_posix):
        p, k = _check(_path, _kind)
        if p: return p, k

    # ── 3. User profile / portable installs (Windows only) ───────────────────
    if sys.platform == "win32":
        _userprofile  = os.environ.get("USERPROFILE", "")
        _localappdata = os.environ.get("LOCALAPPDATA", "")
        _appdata      = os.environ.get("APPDATA", "")
        _portable = []
        for _base in (_userprofile, _localappdata, _appdata):
            if not _base: continue
            _portable += [
                (os.path.join(_base, "Programs", "WinRAR", "UnRAR.exe"), "winrar"),
                (os.path.join(_base, "Programs", "WinRAR", "Rar.exe"),   "winrar"),
                (os.path.join(_base, "Programs", "7-Zip", "7z.exe"),     "7zip"),
                (os.path.join(_base, "WinRAR", "UnRAR.exe"),             "winrar"),
                (os.path.join(_base, "7-Zip",  "7z.exe"),                "7zip"),
            ]
        # Chocolatey / Scoop installs
        _choco = os.path.join(os.environ.get("ChocolateyInstall", r"C:\ProgramData\chocolatey"), "bin")
        _scoop_home = os.path.join(_userprofile, "scoop") if _userprofile else ""
        _portable += [
            (os.path.join(_choco, "UnRAR.exe"), "winrar"),
            (os.path.join(_choco, "7z.exe"),    "7zip"),
        ]
        if _scoop_home:
            _portable += [
                (os.path.join(_scoop_home, "shims", "unrar.exe"), "winrar"),
                (os.path.join(_scoop_home, "shims", "7z.exe"),    "7zip"),
                (os.path.join(_scoop_home, "apps", "winrar", "current", "UnRAR.exe"), "winrar"),
                (os.path.join(_scoop_home, "apps", "7zip",   "current", "7z.exe"),   "7zip"),
            ]
        for _path, _kind in _portable:
            p, k = _check(_path, _kind)
            if p: return p, k

    # ── 4. PATH / shutil.which ────────────────────────────────────────────────
    for _name, _kind in (
        ("UnRAR.exe", "winrar"), ("unrar",    "winrar"), ("Rar.exe",  "winrar"),
        ("7z.exe",    "7zip"),   ("7z",       "7zip"),   ("7za",      "7zip"),
        ("bsdtar",    "bsdtar"),
    ):
        _found = shutil.which(_name)
        if _found:
            log.debug("_find_rar_tool: PATH → %r (%s)", _found, _kind)
            return _found, _kind

    return None, None


def download_binary(url, dest, timeout=30):
    dest = Path(dest)  # normalise — callers may pass str or Path
    try:
        req = urllib.request.Request(url, headers=dict(HTTP_HEADERS))
        with urllib.request.urlopen(req, timeout=timeout, context=_SSL_CTX) as r, open(dest, "wb") as f:
            # Stream with a byte cap to prevent runaway downloads filling disk.
            # shutil.copyfileobj has no size limit, so we loop manually.
            _written = 0
            while True:
                chunk = r.read(65536)
                if not chunk:
                    break
                _written += len(chunk)
                if _written > _DOWNLOAD_MAX_BYTES:
                    raise OSError(
                        "download_binary: response exceeds {} MB cap for {}".format(
                            _DOWNLOAD_MAX_BYTES // (1024 * 1024), url))
                f.write(chunk)
        sz = dest.stat().st_size
        ok = sz > 0
        log.debug("download_binary %s → %s (%s bytes) ok=%s", url, dest.name, sz, ok)
        return ok
    except Exception as e:
        log.debug("download_binary error  %s  —  %s", url, e)
        return False


# ─────────────────────────────────────────────────────────────────────────────
# ENCODING DETECTION & AUTO-UTF-8 RE-ENCODING
# ─────────────────────────────────────────────────────────────────────────────

def _atomic_write_text(path: "str | Path", text: str, encoding: str = "utf-8") -> bool:
    """Write *text* to *path* atomically via a temp file + rename.

    Prevents a corrupt file if the process is killed mid-write.
    On Windows, Path.replace() is not atomic but is safe: it overwrites the
    destination in a single OS call so readers see either the old or new file,
    never a partial write.

    Windows file-lock scenario: if mpv has the *target* file locked for reading,
    tmp.replace(path) raises OSError (Windows does not allow replacing a locked
    file).  The except block then falls back to path.write_text(), which also
    raises PermissionError because the file is still locked.  The outer
    ``except Exception`` catches it, logs a warning, and returns False — the
    caller should check the return value and surface the error to the user.

    Returns True on success, False on any error.
    """
    path = Path(path)
    tmp = path.with_suffix(path.suffix + ".writing")
    try:
        tmp.write_text(text, encoding=encoding)
        tmp.replace(path)
        return True
    except OSError as _rename_e:
        log.warning("_atomic_write_text: rename failed for %s (%s) — falling back to in-place write",
                    path.name, _rename_e)
        try:
            tmp.unlink(missing_ok=True)
        except Exception:
            pass
        try:
            path.write_text(text, encoding=encoding)
            return True
        except Exception as _e:
            log.warning("_atomic_write_text: in-place fallback also failed for %s: %s", path.name, _e)
            return False
    except Exception as _e:
        log.warning("_atomic_write_text: failed for %s: %s", path.name, _e)
        try:
            tmp.unlink(missing_ok=True)
        except Exception:
            pass
        return False


def _detect_encoding(raw_bytes: bytes) -> str:
    """Detect the character encoding of subtitle file bytes.

    Not decorated with @lru_cache: raw_bytes objects are not hashable in a
    stable way without hashing the content (which costs as much as detection
    itself).  Each subtitle is only detected 2–4 times per download session
    which is negligible.

    Priority:
      1. BOM detection   (authoritative when present)
      2. charset_normalizer  (handles CP-1252, ISO-8859-x, Shift-JIS, Arabic, etc.)
      3. Strict UTF-8 decode attempt
      4. latin-1 fallback   (decodes every byte — safe last resort)
    """
    if raw_bytes.startswith(b"\xef\xbb\xbf"):
        return "utf-8-sig"
    if raw_bytes.startswith(b"\xff\xfe"):
        return "utf-16-le"
    if raw_bytes.startswith(b"\xfe\xff"):
        return "utf-16-be"
    if _CHARSET_NORM_OK:
        try:
            result = _cn_from_bytes(raw_bytes).best()
            if result and result.encoding:
                return result.encoding.lower()
        except Exception as _e:
            log.debug("_detect_encoding: charset_normalizer error: %s", _e)
    try:
        raw_bytes.decode("utf-8")
        return "utf-8"
    except UnicodeDecodeError:
        pass
    return "latin-1"


def _read_subtitle_text(path: str) -> str:
    """Read a subtitle file with automatic encoding detection.
    Always returns a string; never raises on encoding errors.
    """
    try:
        raw = Path(path).read_bytes()
    except Exception as e:
        log.warning("_read_subtitle_text: cannot read %s: %s", path, e)
        return ""
    enc = _detect_encoding(raw)
    return raw.decode(enc, errors="replace")


def _ensure_utf8(path: str) -> bool:
    """Re-save a subtitle file as UTF-8 if it is not already UTF-8 / UTF-8-BOM.

    Called automatically after every successful download.  Returns True if the
    file was re-encoded (or was already clean), False on any error.
    """
    try:
        raw = Path(path).read_bytes()
        enc = _detect_encoding(raw)
        # Normalize encoding name — charset_normalizer may return "utf_8"
        # (underscore) while our guard uses "utf-8" (hyphen).  Without this,
        # a valid UTF-8 file gets "re-encoded" unnecessarily, which on Windows
        # converts \n line endings to \r\n and breaks the SRT block splitter.
        enc_norm = enc.replace("_", "-").lower()
        # Already clean — nothing to do.
        if enc_norm in ("utf-8", "utf-8-sig"):
            return True
        text = raw.decode(enc, errors="replace")
        ok = _atomic_write_text(path, text, encoding="utf-8")
        if ok:
            log.info("_ensure_utf8: re-encoded %s  (%s → utf-8)", Path(path).name, enc)
        return ok
    except Exception as e:
        log.warning("_ensure_utf8: failed for %s: %s", path, e)
        return False


# ─────────────────────────────────────────────────────────────────────────────
# HI / SDH DETECTION & STRIP
# ─────────────────────────────────────────────────────────────────────────────

_HI_DETECT_RE = re.compile(
    r"^\s*[\[\(].{1,60}[\]\)]"  # [BANG] or (applause) on its own line
    r"|^\s*\*.+\*\s*$"           # *whisper* on its own line
    r"|[\u266a\u266b]"             # ♪ or ♫ music notes anywhere
    r"|^\s*[A-Z]{2,20}:\s",        # SPEAKER: prefix — no spaces inside token to avoid UK:/US: false positives
    re.MULTILINE,
)

# HI detection tuning constants — hoisted from inline magic numbers.
# Fraction of non-timestamp/non-index lines that must match HI patterns
# before the file is considered hearing-impaired.
_HI_DETECT_THRESHOLD = 0.08   # 8% of checked text lines
# Number of subtitle cue blocks to sample from the start of the file.
_HI_DETECT_SAMPLE_BLOCKS = 80

# HI-strip patterns hoisted to module level — compiled once, reused on every call.
# Previously these were re-compiled inside _strip_hi_from_file on every invocation.
_STRIP_HI_PATTERNS = [
    re.compile(r"^\s*[\[\(][^\]\)]{0,60}[\]\)]\s*$"),  # standalone [sound]
    re.compile(r"[\[\(][^\]\)]{0,60}[\]\)]"),            # inline [sound]
    re.compile(r"^\s*\*[^*]+\*\s*$"),                      # standalone *emphasis*
    re.compile(r"\*[^*]+\*"),                                 # inline *emphasis*
    re.compile(r"^\s*[\u266a\u266b][^\n]*$"),              # ♪ music line
    re.compile(r"[\u266a\u266b]"),                           # ♪ symbol inline
    re.compile(r"^\s*[A-Z]{2,20}:\s*"),                      # SPEAKER: prefix (tightened)
]
_TS_RE = re.compile(r"^\d{1,2}:\d{2}:\d{2}[,\.]\d{3}\s*-->")

# Matches SDH/HI tags in filenames and release names.
# Used in the right-click menu to show the strip option based on filename alone.
_HI_NAME_RE = re.compile(
    r"(?:^|[\[\(\-\.\s_])"
    r"(?:sdh|hi|hearing[-_]?impaired)"
    r"(?:$|[\]\)\-\.\s_])",
    re.IGNORECASE,
)


def _detect_hi_content(path: str) -> bool:
    """Return True if the subtitle file contains HI/SDH annotations.

    Scans the first 80 text cues. Considers HI if >8% of text lines match
    known HI patterns (sound effects, music notes, speaker labels).
    """
    if not path or not Path(path).is_file():
        return False
    try:
        raw = _read_subtitle_text(path)
        blocks = [b.strip() for b in re.split(r"\n\s*\n", raw.strip()) if b.strip()]
        hits = checked = 0
        for b in blocks[:_HI_DETECT_SAMPLE_BLOCKS]:
            for line in b.splitlines():
                s = line.strip()
                if not s or s.isdigit() or _TS_RE.match(s):
                    continue
                checked += 1
                if _HI_DETECT_RE.search(s):
                    hits += 1
        return checked > 0 and (hits / checked) > _HI_DETECT_THRESHOLD
    except Exception:
        return False


def _strip_hi_from_file(path: str) -> bool:
    """Remove HI/SDH annotations from a subtitle file in-place.

    Strips: standalone [sound] / (sound) lines, inline [sound] spans,
    standalone *emphasis* lines, ♪ music lines/symbols, SPEAKER: prefixes.
    Preserves sequence numbers and timestamps untouched.
    Returns True on success.

    Format handling
    ---------------
    .srt / .vtt : processed with the regex pipeline below.
    .ass / .ssa  : processed via pysubs2 (if installed), which applies the HI
                   patterns only to the plain-text portion of each Dialogue event
                   — leaving ASS override tags, headers, and style sections intact.
                   Without pysubs2 the regex pipeline would corrupt the ASS
                   header lines (e.g. "Dialogue: ..." is removed by the
                   SPEAKER: pattern), so we bail out early and return False.
    other formats: treated as plain text (best-effort).
    """
    ext = Path(path).suffix.lower()
    is_ass = ext in (".ass", ".ssa")

    # ── ASS / SSA: use pysubs2 to avoid corrupting the header/style sections ──
    if is_ass:
        if not _PYSUBS2_OK:
            log.warning(
                "_strip_hi_from_file: cannot strip ASS/SSA file %s — "
                "pysubs2 is not installed (pip install pysubs2)",
                Path(path).name,
            )
            return False
        try:
            subs = _pysubs2.load(path)
            changed = False
            for event in subs:
                # pysubs2 exposes the plain-text content (ASS override tags stripped)
                # via event.plaintext, but we must modify event.text (which preserves
                # override tags).  Strategy: strip HI patterns from the plain-text
                # portion only by splitting on ASS override tag boundaries.
                #
                # Simpler approach that works for the vast majority of HI content:
                # apply the HI patterns to event.text directly.  ASS override tags
                # are enclosed in {…} braces so they won't be matched by our patterns
                # (which target [sound], (sound), SPEAKER:, ♪, and *emphasis*).
                original = event.text
                result = original
                for pat in _STRIP_HI_PATTERNS:
                    result = pat.sub("", result)
                result = result.strip()
                if result != original:
                    event.text = result
                    changed = True
            if not changed:
                return True   # nothing to do — file is unchanged
            subs.save(path)
            return True
        except Exception as e:
            log.warning("_strip_hi_from_file (ASS): failed for %s: %s", path, e)
            return False

    # ── SRT / VTT / plain-text formats: regex pipeline ────────────────────────
    # Use module-level _STRIP_HI_PATTERNS (compiled once at import time)
    try:
        raw = _read_subtitle_text(path)
        segments = re.split(r"(\n\s*\n)", raw)
        out = []
        for seg in segments:
            if not seg.strip():
                out.append(seg)
                continue
            new_lines = []
            for line in seg.splitlines():
                s = line.strip()
                if not s or s.isdigit() or _TS_RE.match(s):
                    new_lines.append(line)
                    continue
                result = line
                # Apply all HI-strip patterns sequentially (not as alternatives).
                # Each pattern targets a different class of HI markup:
                #   bracketed cues ([MUSIC]), parenthetical cues ((applause)),
                #   speaker labels (JOHN:), all-caps lines, etc.
                # Order matters: bracket removal runs before speaker-label removal
                # so "[JOHN]: Hello" becomes "Hello" rather than ": Hello".
                for pat in _STRIP_HI_PATTERNS:
                    result = pat.sub("", result)
                result = result.strip()
                if result:
                    new_lines.append(result)
            out.append("\n".join(new_lines))
        return _atomic_write_text(path, "".join(out), encoding="utf-8")
    except Exception as e:
        log.warning("_strip_hi_from_file: failed for %s: %s", path, e)
        return False


# ─────────────────────────────────────────────────────────────────────────────
# SUBTITLE SYNC (ffsubsync / alass)
# ─────────────────────────────────────────────────────────────────────────────

@lru_cache(maxsize=32)
def _find_pip_binary(name: str) -> "str | None":
    """Locate a pip-installed console-script binary by searching well-known
    locations that shutil.which() misses when the Scripts / bin folder is not
    on PATH.  Search order:

    1. shutil.which() — covers anything already on PATH
    2. The Scripts / bin directory of every Python interpreter we can find:
       - sys.executable's own Scripts/bin
       - Every interpreter returned by ``py --list-paths`` (Windows py launcher)
       - sys.path entries that look like site-packages → walk up to Scripts/bin
    3. Common pip user install locations (--user scheme)
    4. pyenv shims  (PYENV_ROOT / shims)
    5. Homebrew prefix bins  (macOS / Linux)
    6. Conda envs  (CONDA_PREFIX / bin or Scripts)
    7. Common absolute paths (e.g. /usr/local/bin, /opt/homebrew/bin)
    8. Scoop shims  (~/scoop/shims, Windows)
    """
    def _check(path):
        # os.X_OK always returns True on Windows, so the win32 branch short-circuits
        # before the access() call — the guard is still correct, just redundant on Windows.
        if path and os.path.isfile(path) and (sys.platform == "win32" or os.access(path, os.X_OK)):
            log.debug("_find_pip_binary: found %r → %r", name, path)
            return path
        return None

    # ── 1. PATH ──────────────────────────────────────────────────────────────
    p = shutil.which(name)
    if p:
        return p
    if sys.platform == "win32":
        p = shutil.which(name + ".exe")
        if p:
            return p

    # ── helpers ───────────────────────────────────────────────────────────────
    def _scripts_from_prefix(prefix):
        """Return the Scripts (Win) or bin (POSIX) dir under *prefix*."""
        if not prefix:
            return None
        if sys.platform == "win32":
            return os.path.join(prefix, "Scripts")
        return os.path.join(prefix, "bin")

    def _check_prefix(prefix):
        sd = _scripts_from_prefix(prefix)
        if not sd:
            return None
        if sys.platform == "win32":
            return _check(os.path.join(sd, name + ".exe")) or _check(os.path.join(sd, name))
        return _check(os.path.join(sd, name))

    # ── 2. sys.executable's own environment ──────────────────────────────────
    # Covers the venv / virtualenv that is currently active.
    found = _check_prefix(os.path.dirname(os.path.dirname(sys.executable)))
    if found:
        return found
    # Also try the direct parent of sys.executable (some flat layouts)
    found = _check(os.path.join(os.path.dirname(sys.executable), name))
    if found:
        return found
    if sys.platform == "win32":
        found = _check(os.path.join(os.path.dirname(sys.executable), name + ".exe"))
        if found:
            return found

    # ── 3. All Python prefixes visible through sys.path (site-packages) ──────
    for sp in sys.path:
        if "site-packages" in sp or "dist-packages" in sp:
            # walk up to find the interpreter root
            candidate = sp
            for _ in range(4):
                candidate = os.path.dirname(candidate)
                found = _check_prefix(candidate)
                if found:
                    return found

    # ── 4. py launcher (Windows) — enumerate all installed Pythons ───────────
    if sys.platform == "win32":
        try:
            _py = shutil.which("py")
            if _py:
                out = subprocess.check_output(
                    [_py, "--list-paths"], stderr=subprocess.DEVNULL,
                    timeout=5, text=True, creationflags=0x08000000
                )
                for line in out.splitlines():
                    parts = line.split()
                    for part in parts:
                        if os.sep in part and os.path.isdir(os.path.dirname(part)):
                            # part is the python.exe path
                            found = _check_prefix(os.path.dirname(os.path.dirname(part)))
                            if found:
                                return found
        except Exception:
            pass

    # ── 5. pip --user install locations ──────────────────────────────────────
    try:
        import site as _site
        user_base = _site.getuserbase()
        if user_base:
            found = _check_prefix(user_base)
            if found:
                return found
        # getusersitepackages() can throw if site is disabled
        try:
            user_site = _site.getusersitepackages()
            if user_site:
                for _ in range(4):
                    user_site = os.path.dirname(user_site)
                    found = _check_prefix(user_site)
                    if found:
                        return found
        except Exception:
            pass
    except Exception:
        pass

    # ── 6. Explicit per-platform user paths ──────────────────────────────────
    if sys.platform == "win32":
        _appdata   = os.environ.get("APPDATA", "")
        _localdata = os.environ.get("LOCALAPPDATA", "")
        _userprofile = os.environ.get("USERPROFILE", "")
        _pyver = "Python{}{}".format(sys.version_info.major, sys.version_info.minor)
        _candidates = []
        for _base in (_appdata, _localdata, _userprofile):
            if not _base:
                continue
            _candidates += [
                os.path.join(_base, "Programs", "Python", _pyver, "Scripts"),
                os.path.join(_base, "Programs", "Python", "Python{}{}".format(
                    sys.version_info.major, sys.version_info.minor), "Scripts"),
                os.path.join(_base, "Programs", "Python", "Scripts"),
                os.path.join(_base, "Python", "Scripts"),
                os.path.join(_base, "Python{}{}".format(
                    sys.version_info.major, sys.version_info.minor), "Scripts"),
                # pipx (use _base — _localdata is already one of the loop values)
                os.path.join(_base, "pipx", "venvs", name, "Scripts"),
            ]
        # Common system-wide locations
        for _pyver_dir in (
            r"C:\Python3{}".format(sys.version_info.minor),
            r"C:\Python{}{}".format(sys.version_info.major, sys.version_info.minor),
            r"C:\Program Files\Python{}{}".format(sys.version_info.major, sys.version_info.minor),
            r"C:\Program Files (x86)\Python{}{}".format(sys.version_info.major, sys.version_info.minor),
        ):
            _candidates.append(os.path.join(_pyver_dir, "Scripts"))
        for sd in _candidates:
            p = _check(os.path.join(sd, name + ".exe")) or _check(os.path.join(sd, name))
            if p:
                return p
    else:
        # POSIX user scheme
        _home = os.environ.get("HOME", "")
        _pyver_short = "{}.{}".format(sys.version_info.major, sys.version_info.minor)
        _posix_candidates = [
            os.path.join(_home, ".local", "bin"),
            "/usr/local/bin",
            "/usr/bin",
            "/opt/homebrew/bin",               # Apple Silicon Homebrew
            "/usr/local/homebrew/bin",          # Intel Homebrew
            os.path.join(_home, ".local", "lib", "python" + _pyver_short, "site-packages",
                         "..", "..", "..", "bin"),
            # pipx
            os.path.join(_home, ".local", "pipx", "venvs", name, "bin"),
        ]
        for bd in _posix_candidates:
            p = _check(os.path.join(bd, name))
            if p:
                return p

    # ── 7. pyenv shims ────────────────────────────────────────────────────────
    _pyenv_root = os.environ.get("PYENV_ROOT") or os.path.join(
        os.environ.get("HOME", ""), ".pyenv")
    p = _check(os.path.join(_pyenv_root, "shims", name))
    if p:
        return p

    # ── 8. Conda ─────────────────────────────────────────────────────────────
    _conda_prefix = os.environ.get("CONDA_PREFIX", "")
    if _conda_prefix:
        found = _check_prefix(_conda_prefix)
        if found:
            return found

    log.debug("_find_pip_binary: %r not found in any location", name)
    return None


def _find_ffmpeg_binary(name: str = "ffmpeg") -> "str | None":
    """Locate ffmpeg or ffprobe using the same comprehensive search as
    _find_pip_binary, extended with OS-package manager paths.
    'name' should be 'ffmpeg' or 'ffprobe'.
    """
    # ffmpeg is rarely installed via pip — check PATH first, then common system paths
    p = shutil.which(name) or shutil.which(name + ".exe")
    if p:
        return p

    if sys.platform == "win32":
        _userprofile = os.environ.get("USERPROFILE", "")
        _localdata   = os.environ.get("LOCALAPPDATA", "")
        _scoop_home  = os.path.join(_userprofile, "scoop") if _userprofile else ""
        _choco       = os.path.join(os.environ.get("ChocolateyInstall",
                                    r"C:\ProgramData\chocolatey"), "bin")
        _candidates  = [os.path.join(_choco, name + ".exe")]
        if _scoop_home:
            _candidates += [
                os.path.join(_scoop_home, "shims",  name + ".exe"),
                os.path.join(_scoop_home, "apps", "ffmpeg", "current", "bin", name + ".exe"),
            ]
        if _userprofile:
            _candidates += [
                os.path.join(_userprofile, "ffmpeg", "bin", name + ".exe"),
                os.path.join(_userprofile, "Downloads", "ffmpeg", "bin", name + ".exe"),
            ]
        _candidates += [
            r"C:\ffmpeg\bin\{}.exe".format(name),
            r"C:\Program Files\ffmpeg\bin\{}.exe".format(name),
        ]
        for c in _candidates:
            if c and os.path.isfile(c) and (sys.platform == "win32" or os.access(c, os.X_OK)):
                log.debug("_find_ffmpeg_binary: found %r → %r", name, c)
                return c
    else:
        _home = os.environ.get("HOME", "")
        _candidates = [
            "/usr/local/bin/{}".format(name),
            "/usr/bin/{}".format(name),
            "/opt/homebrew/bin/{}".format(name),
            "/usr/local/homebrew/bin/{}".format(name),
            os.path.join(_home, ".local", "bin", name),
            "/snap/bin/{}".format(name),
            "/flatpak/bin/{}".format(name),
        ]
        for c in _candidates:
            # os.X_OK always returns True on Windows (no execute-bit concept), so
            # skip that check there — matching the pattern used in _find_rar_tool.
            if c and os.path.isfile(c) and (sys.platform == "win32" or os.access(c, os.X_OK)):
                log.debug("_find_ffmpeg_binary: found %r → %r", name, c)
                return c

    log.debug("_find_ffmpeg_binary: %r not found", name)
    return None


# Module-level detection — runs once at import time so the result is available
# for both the sync menu and the warning banner without repeated disk probes.
_FFSUBSYNC_PATH: "str | None" = _find_pip_binary("ffsubsync")
_ALASS_PATH:     "str | None" = _find_pip_binary("alass")
_SYNC_TOOL_OK:   bool         = bool(_FFSUBSYNC_PATH or _ALASS_PATH)
_FFMPEG_OK:      bool         = bool(_find_ffmpeg_binary("ffmpeg"))

log.info(
    "sync tool detection: ffsubsync=%r  alass=%r",
    _FFSUBSYNC_PATH, _ALASS_PATH,
)


def _find_sync_tool() -> "tuple[str, str] | tuple[None, None]":
    """Return (path, name) for the first available sync tool, or (None, None).

    This is the authoritative runtime sync-tool detector — always use this
    function (not _find_pip_binary directly) when checking sync availability,
    because alass is commonly distributed as a standalone binary on PATH that
    _find_pip_binary may not find via the pip-path heuristics alone.

    Searches every location that _find_pip_binary covers, not just PATH.
    Results are cached in module-level _FFSUBSYNC_PATH / _ALASS_PATH so
    repeated right-click calls are instant.
    """
    if _FFSUBSYNC_PATH:
        return _FFSUBSYNC_PATH, "ffsubsync"
    if _ALASS_PATH:
        return _ALASS_PATH, "alass"
    # Fallback live probe (covers hot-installs during the same session)
    for name in ("ffsubsync", "alass"):
        p = _find_pip_binary(name)
        if p:
            return p, name
    return None, None


# Patterns that reliably identify live / non-seekable stream URLs.
# These formats cannot be seeked from the beginning, so audio extraction
# for sync would either fail or produce unreliable results.
_LIVE_STREAM_RE = re.compile(
    r"\.m3u8(\?|$)"          # HLS manifest
    r"|\.mpd(\?|$)"          # DASH manifest
    r"|/manifest(\?|$)"      # generic manifest endpoint
    r"|/live/"               # common live path segment
    r"|[?&]live=1"           # live flag in query string
    r"|/hls/"                # HLS path segment
    r"|/dash/",              # DASH path segment
    re.IGNORECASE,
)


def _is_live_stream_url(url: str) -> bool:
    """Return True if the URL looks like a live or non-seekable stream.

    Direct HTTP/HTTPS links to .mp4, .mkv, .avi etc. are seekable and
    return False.  HLS (.m3u8), DASH (.mpd), and common live-stream
    path patterns return True.
    """
    if not url:
        return False
    return bool(_LIVE_STREAM_RE.search(url))

# ─────────────────────────────────────────────────────────────────────────────
# FILENAME UTILITIES
# ─────────────────────────────────────────────────────────────────────────────

def _norm_release_name(s: str) -> str:
    """Normalise a release or filename string for comparison.

    Strips the file extension (if present), lower-cases, and collapses all
    separator characters (spaces, dots, underscores, hyphens) to single spaces.
    Used in three places: OS.com direct scoring, SubDL scoring, and the
    post-search release-hint matcher.  Defined once at module level to avoid
    recreating an identical closure on every search call.
    """
    s = Path(s).stem if Path(s).suffix.lower() in {
        ".srt", ".ass", ".ssa", ".vtt", ".sub", ".smi",
        ".mkv", ".mp4", ".avi", ".m4v", ".mov", ".wmv", ".flv",
    } else s
    return re.sub(r"[\s._\-]+", " ", s).strip().lower()


def _score_url_segment(seg: str) -> int:
    """Score a URL path segment for use as a video title (higher = more likely to be the title).
    Module-level so it is defined once, not recreated on every clean_filename call."""
    s = _RE_VEXT.sub("", seg)
    if not s or _RE_UUID.match(s) or _RE_HASH.match(s): return -1
    if _RE_GENERIC.match(s): return 0
    sc = 1
    if _RE_SXEX.search(s): sc += 10
    if _RE_YEAR.search(s): sc += 5
    if len(s) >= 5: sc += 2
    if re.fullmatch(r"\d+", s): sc -= 3
    return sc

@lru_cache(maxsize=128)
def clean_filename(raw):
    if not raw:
        return ""
    if _URL_SCHEME_RE.match(raw):
        parsed = urllib.parse.urlparse(raw)
        name = ""
        # Skip query-param extraction for YouTube/youtu.be — their params
        # are video IDs ("v="), playlist IDs, etc., never useful filenames.
        _is_yt = parsed.netloc in ("www.youtube.com", "youtube.com",
                                   "youtu.be", "m.youtube.com",
                                   "music.youtube.com")
        qp = urllib.parse.parse_qs(parsed.query)
        for key in ([] if _is_yt else ["filename","file","name","title","video"]):
            if key in qp:
                name = qp[key][0]; break
        if not name:
            segs = [s for s in urllib.parse.unquote(parsed.path).split("/") if s]
            if segs:
                scored = sorted(enumerate(segs), key=lambda t: _score_url_segment(t[1]), reverse=True)
                bi, bs = scored[0]
                best_score = _score_url_segment(bs)
                if best_score >= 1:  # reject generic (0) and UUID/hash/empty (-1) segments
                    if _RE_SXEX.search(bs) and bi > 0:
                        for ps in reversed(segs[:bi]):
                            p = _RE_VEXT.sub("", ps)
                            if p and not _RE_UUID.match(p) and not _RE_HASH.match(p) \
                                    and not _RE_GENERIC.match(p) and not _RE_SXEX.search(p) and len(p) >= 3:
                                name = p + " " + bs; break
                        else:
                            name = bs
                    else:
                        name = bs
        if not name and not _is_yt:
            name = urllib.parse.unquote(raw)
        name = _RE_VEXT.sub("", name)
    else:
        name = Path(raw).stem
    # Matches S01E05 and S01EP05 (EP variant) — consistent with _RE_SXEX
    m = _RE_SE_INLINE.search(name)
    nc = _RE_TAGS.sub("", name)
    if m:
        tp = name[:m.start()].strip(" .-_")
        ep = m.group(0).upper()
        tp = re.sub(r"[\.\\_\-]+", " ", tp).strip()
        return "{} {}".format(tp, ep).strip()
    nc = re.sub(r"\[.*?\]", "", nc)
    nc = re.sub(r"\((?!\d{4}\))[^)]*\)", "", nc)
    nc = re.sub(r"[\.\\_\-]+", " ", nc)
    return re.sub(r"\s{2,}", " ", nc).strip()

def clean_title(raw):
    """Clean a human-readable title (e.g. from mpv media-title) for use as a search query."""
    if not raw:
        return ""
    name = raw.strip()
    # Matches S01E05 and S01EP05 (EP variant) — consistent with _RE_SXEX
    m = _RE_SE_INLINE.search(name)
    nc = _RE_TAGS.sub("", name)
    nc = re.sub(r"\s+-\s+\S.*$", "", nc).strip()   # drop " - Subtitle" suffixes
    nc = re.sub(r"\s+-$", "", nc).strip()           # drop trailing " -"
    if m:
        tp = name[:m.start()].strip(" .-_")
        ep = m.group(0).upper()
        tp = re.sub(r"[\.\\_-]+", " ", tp).strip()
        return "{} {}".format(tp, ep).strip()
    nc = re.sub(r"\[.*?\]", "", nc)
    nc = re.sub(r"\((?!\d{4}\))[^)]*\)", "", nc)
    nc = re.sub(r"(?<=\w)[._](?=\w)", " ", nc)
    return re.sub(r"\s{2,}", " ", nc).strip()

def parse_season_episode(title: str) -> Tuple[Optional[int], Optional[int]]:
    """
    Detect season/episode from many formats:
      S01E05, S01EP05, S01.E05, S01-E05  (standard + EP/dot/dash variants)
      1x05, 01x05                         (NxNN)
      Season 1 Episode 5                  (written out)
      105, 205                            (bare NNN with alpha context)
      E05 alone                           (episode-only → season 1)
      Ep05, EP05                          (Ep-prefix, no season → season 1)
      2024-01-15, 15-01-2024              (date-based episodes → season 1)
    """
    for pat in _RE_SE_PATTERNS:
        m = pat.search(title)
        if m:
            return int(m.group(1)), int(m.group(2))
    # Bare NNN (e.g. 105 = S01E05): only when no resolution numbers are present.
    # Resolution patterns like 720p cause false matches (720 → S07E20).
    # Also guard against codec strings like x264/x265/h264 — "x264" must not
    # match as S02E64.  Strip those tokens before running the digit search.
    # Additionally block bare resolution numbers without the trailing 'p'
    # (e.g. "Show.H264.720" strips to "Show..720" and would match as S07E20).
    if not _RE_RESOLUTION.search(title):
        _stripped = _RE_CODEC_STRIP.sub("", title)
        m = re.search(r"(?<!\d)([1-9])(\d{2})(?!\d)", _stripped)
        if m and re.search(r"[A-Za-z]", _stripped):
            if m.group(0) not in _BARE_RESOLUTION_BLOCK:
                return int(m.group(1)), int(m.group(2))
    # Episode-only E05 → assume season 1
    m = re.search(r"(?<![A-Za-z])[Ee](\d{1,2})(?!\d)", title)
    if m:
        return 1, int(m.group(1))
    # Ep05 / EP05 prefix (no season number) → assume season 1
    m = re.search(r"(?<![A-Za-z])[Ee][Pp](\d{1,2})(?!\d)", title)
    if m:
        return 1, int(m.group(1))
    # Date-based episodes: YYYY-MM-DD or DD-MM-YYYY → treat as season 1, no episode number
    m = re.search(r"(?<!\d)(?:19|20)\d{2}[.\-_](0[1-9]|1[0-2])[.\-_](0[1-9]|[12]\d|3[01])(?!\d)", title)
    if not m:
        m = re.search(r"(?<!\d)(0[1-9]|[12]\d|3[01])[.\-_](0[1-9]|1[0-2])[.\-_](?:19|20)\d{2}(?!\d)", title)
    if m:
        return 1, None
    return None, None

# ─────────────────────────────────────────────────────────────────────────────
# SUBLIMINAL ENGINE
# ─────────────────────────────────────────────────────────────────────────────

def search_with_subliminal(query, lang_code, video_path="", providers=None):
    """Search via subliminal.
    lang_code may be a single ISO-639-1 string OR a list of them.
    All languages are fetched in a single ProviderPool call.
    """
    if not SUBLIMINAL_OK:
        return []
    results = []
    use_providers = providers if providers is not None else SUBLIMINAL_PROVIDERS_LIST

    # Normalise to list
    if isinstance(lang_code, str):
        lang_codes = [lang_code]
    else:
        lang_codes = list(lang_code)

    log.info("subliminal search  query=%r  langs=%s  providers=%s", query, lang_codes, use_providers)

    lang_set = set()
    for lc in lang_codes:
        bf_code = ISO1_TO_BABELFISH.get(lc, lc)
        try:
            lang_set.add(Language(bf_code))
        except Exception as e:
            log.error("babelfish Language(%r) failed: %s", bf_code, e)
    if not lang_set:
        return []

    # Build a reverse map: babelfish alpha3 → iso1 code so we can tag each result
    bf_to_iso1 = {ISO1_TO_BABELFISH.get(lc, lc): lc for lc in lang_codes}

    video_obj = None
    if video_path and Path(video_path).is_file():
        try:
            video_obj = Video.fromname(video_path)
        except Exception:
            pass
    if video_obj is None:
        try:
            nq = re.sub(r"([Ss]\d{1,2})[Ee][Pp](\d{1,2})",
                        lambda m: m.group(1)+"E"+m.group(2), query, flags=re.I)
            video_obj = Video.fromname("{}.mkv".format(re.sub(r"\s+", ".", nq)))
        except Exception as e:
            log.error("Cannot create subliminal Video object: %s", e); return []

    raw_subs = []
    def _flatten_subliminal_results(rd):
        """Flatten ProviderPool.list_subtitles() result and filter out non-Subtitle objects."""
        try:
            from subliminal.subtitle import Subtitle as _SubtitleBase
        except ImportError:
            _SubtitleBase = object
        flat = []
        for slist in (rd.values() if isinstance(rd, dict) else [rd]):
            if not isinstance(slist, (list, tuple)):
                continue
            for s in slist:
                if isinstance(s, _SubtitleBase):
                    flat.append(s)
                else:
                    log.debug("subliminal: skipping non-Subtitle object: %r", s)
        return flat

    try:
        with ProviderPool(providers=use_providers) as pool:
            rd = pool.list_subtitles(video_obj, lang_set)
            raw_subs.extend(_flatten_subliminal_results(rd))
            log.info("subliminal ProviderPool: %d subtitle(s)", len(raw_subs))
    except Exception as e:
        log.warning("subliminal ProviderPool bulk error (%s) — retrying per-provider", e)
        for pname in use_providers:
            try:
                with ProviderPool(providers=[pname]) as pool:
                    rd = pool.list_subtitles(video_obj, lang_set)
                    raw_subs.extend(_flatten_subliminal_results(rd))
            except Exception as pe:
                log.warning("  [%s] failed: %s", pname, pe)

    try:
        from subliminal.score import compute_score
        for sub_obj in raw_subs:
            # ── signal-based scoring (mirrors direct OS.com algorithm) ────────
            # Use subliminal's matches set to extract the same signals used by
            # the direct OS.com scorer so results from both paths are comparable.
            try:
                _matches = set(sub_obj.get_matches(video_obj))
            except Exception:
                try:
                    _matches = getattr(sub_obj, "matches", set()) or set()
                except Exception:
                    _matches = set()

            hash_match    = "hash" in _matches
            # Hearing-impaired and machine/AI translation flags
            hi_flag       = bool(getattr(sub_obj, "hearing_impaired", False))
            mach_flag     = bool(getattr(sub_obj, "machine_translated", False)
                                 or getattr(sub_obj, "ai_translated", False))
            # Download count
            dl_count      = int(getattr(sub_obj, "download_count", 0) or 0)
            # Uploader trust (subliminal providers rarely expose this; default False)
            uploader_ok   = bool(getattr(sub_obj, "trusted", False)
                                 or getattr(sub_obj, "from_trusted", False))
            # Rating (0–10 scale, default 0)
            rating        = float(getattr(sub_obj, "rating", 0) or 0)
            votes         = int(getattr(sub_obj, "votes", 0) or 0)

            if mach_flag:
                score_norm = _SCORE_AI_TRANSLATED
            elif hash_match:
                score_norm = _SCORE_HASH_BASE
                if uploader_ok:
                    score_norm = min(score_norm + _SCORE_HASH_TRUSTED_BONUS, _SCORE_HASH_MAX)
                if votes > 0 and rating >= 8.0:
                    score_norm = min(score_norm + _SCORE_HASH_VOTE_BONUS, _SCORE_HASH_MAX)
            else:
                score_norm = _SCORE_QUERY_BASE
                if uploader_ok:
                    score_norm = min(score_norm + _SCORE_TRUSTED_BONUS, _SCORE_QUERY_CAP)
                if votes > 0:
                    score_norm = min(score_norm + (rating / 10.0) * _SCORE_RATING_WEIGHT, _SCORE_QUERY_CAP)
                if dl_count > 0:
                    score_norm = min(score_norm + _SCORE_POP_WEIGHT * (_math.log10(dl_count + 1) / 6.0), _SCORE_QUERY_CAP)

            # Demote hearing-impaired slightly (same cap as machine-translated path)
            if hi_flag and not mach_flag:
                score_norm = min(score_norm, 0.69)

            score_norm = min(max(score_norm, 0.0), 1.0)
            provider_name = getattr(sub_obj, "provider_name", "subliminal")
            release = (getattr(sub_obj,"release","") or getattr(sub_obj,"name","") or
                       getattr(sub_obj,"filename","") or getattr(sub_obj,"movie_name","") or
                       getattr(sub_obj,"series_name","") or getattr(sub_obj,"episode_title","") or "")
            page_link = str(getattr(sub_obj,"page_link","") or "")
            _raw_id   = getattr(sub_obj,"id","") or getattr(sub_obj,"subtitle_id","") or ""
            # Resolve the per-result ISO-1 language code from the subliminal object
            _sub_lang = getattr(sub_obj, "language", None)
            _bf_alpha3 = str(_sub_lang.alpha3) if _sub_lang else ""
            result_lang = bf_to_iso1.get(_bf_alpha3, lang_codes[0])
            _stable   = "{}_{}_{}_{}".format(provider_name, result_lang, release, _raw_id)
            sub_id    = "subliminal_" + hashlib.md5(_stable.encode("utf-8")).hexdigest()
            fmt_attr  = getattr(sub_obj,"format",None)
            fmt       = str(fmt_attr).lower() if fmt_attr else "srt"
            _file_id  = (getattr(sub_obj,"file_id",None) or getattr(sub_obj,"id",None) or "")
            results.append(Sub(provider=str(provider_name), language=result_lang,
                               release=release, score=score_norm, dl_url=page_link,
                               sub_id=sub_id, fmt=fmt, _sub_obj=sub_obj,
                               file_id=str(_file_id) if _file_id else "",
                               ))
            log.debug("  [%s] %r  lang=%s  hash=%s  dl=%d  norm=%.3f", provider_name, release, result_lang, hash_match, dl_count, score_norm)
    except Exception as e:
        log.error("subliminal scoring error: %s\n%s", e, traceback.format_exc())

    results.sort(key=lambda s: s.score, reverse=True)
    log.info("subliminal returned %d results after scoring", len(results))
    return results

_settings_cache: dict = {}  # module-level cache to avoid re-reading settings on every key lookup
_settings_cache_lock = threading.Lock()  # guards the non-atomic clear+update sequence

import copy as _copy  # used by _get_settings_cached for deep copy of nested mutable values

def _get_settings_cached() -> dict:
    """Return settings dict, reading from disk only if the file changed since last read.
    Disk I/O and JSON parsing are performed OUTSIDE the lock to keep the critical
    section as short as possible.  The lock only guards the dict mutation so two
    concurrent readers cannot observe a partially-cleared cache (VUL-03).
    Returns a snapshot copy so callers cannot mutate the shared cache.

    Issue 12 fix: FileNotFoundError uses a -1 sentinel mtime instead of clearing
    the full cache, breaking the repeated-clear loop during settings-file creation.

    Issue 3 fix: We re-stat() inside the commit lock to ensure the mtime we tag
    matches the data we just read, closing the TOCTOU window where the file could
    change between our read and our commit.
    """
    settings_file = CONFIG_DIR / "subfinder_settings.json"
    # Fast path: read mtime under lock; if unchanged return snapshot immediately.
    with _settings_cache_lock:
        try:
            mtime = settings_file.stat().st_mtime
        except FileNotFoundError:
            # Use sentinel -1 so we don’t clear _mtime and re-trigger on every call
            # during the window when settings file is being created for the first time.
            if _settings_cache.get("_mtime") != -1:
                _settings_cache.clear()
                _settings_cache["_mtime"] = -1
            return _copy.deepcopy(_settings_cache)
        except Exception as _e:
            log.warning("_get_settings_cached: stat error on settings file: %s", _e)
            return _copy.deepcopy(_settings_cache)
        if _settings_cache.get("_mtime") == mtime:
            return _copy.deepcopy(_settings_cache)

    # Slow path: file changed — read and parse OUTSIDE the lock.
    try:
        data = json.loads(settings_file.read_text(encoding="utf-8"))
    except FileNotFoundError:
        with _settings_cache_lock:
            if _settings_cache.get("_mtime") != -1:
                _settings_cache.clear()
                _settings_cache["_mtime"] = -1
        # Return empty dict — all callers use .get(key, default) so no KeyError.
        # This is the normal first-launch path before settings.json is created.
        return {}
    except Exception as _e:
        log.debug("_get_settings_cached: read/parse error: %s", _e)
        with _settings_cache_lock:
            return _copy.deepcopy(_settings_cache)

    # Re-acquire to commit. Re-stat() inside the lock to get the mtime of the
    # data we actually read — this closes the TOCTOU window: if the file changed
    # between our read and this point, the new mtime won’t match our data, and the
    # next caller will trigger a fresh slow-path read instead of caching stale data.
    with _settings_cache_lock:
        try:
            commit_mtime = settings_file.stat().st_mtime
        except OSError:
            commit_mtime = mtime  # file disappeared right after we read it; use original
        if _settings_cache.get("_mtime") != commit_mtime:
            _settings_cache.clear()
            _settings_cache.update(data)
            _settings_cache["_mtime"] = commit_mtime
        return _copy.deepcopy(_settings_cache)

def _get_oscom_key():
    """Read the OpenSubtitles API key from cached settings."""
    return _get_settings_cached().get("oscom_api_key", "") or ""

# Module-level JWT cache.  Paired with an expiry timestamp so stale tokens
# are never reused across a 24-hour session boundary.  OpenSubtitles JWTs are
# valid for 24 hours; we treat them as expired after 23 hours (5-minute buffer
# on top of that) to avoid using a token in its final seconds.
_oscom_jwt_token:  str   = ""
_oscom_jwt_expiry: float = 0.0   # epoch seconds; 0 means "not set / expired"
_oscom_jwt_lock = threading.Lock()
_OSCOM_JWT_TTL  = 23 * 3600      # 23 hours in seconds

# base_url returned by /login — may be "vip-api.opensubtitles.com" for VIP
# users.  The API docs require all subsequent requests to use this host.
# Defaults to the standard host; updated on every successful login.
_oscom_base_url: str = "api.opensubtitles.com"
# Reads of _oscom_base_url are un-locked. In CPython, str reads are effectively
# atomic under the GIL. PEP 703 no-GIL is available in Python 3.13+ as an opt-in
# build flag (python3.13t). If running a no-GIL build, protect this with _oscom_jwt_lock.

def _get_oscom_jwt() -> str:
    """Return a valid cached JWT token for OpenSubtitles, logging in if needed.

    Returns empty string if username/password are not configured or login fails.
    Token is cached in memory and automatically refreshed when it is within
    one hour of its 24-hour expiry (i.e. after 23 hours).

    Also stores the base_url returned by the login response into _oscom_base_url
    so that subsequent API calls route to the correct host (standard or VIP).
    """
    global _oscom_jwt_token, _oscom_jwt_expiry, _oscom_base_url
    # Fast path: check under lock (microseconds).
    with _oscom_jwt_lock:
        if _oscom_jwt_token and _time_module.time() < _oscom_jwt_expiry:
            return _oscom_jwt_token
        # Token absent/expired — read credentials while still under lock, then release.
        _oscom_jwt_token  = ""
        _oscom_jwt_expiry = 0.0
        s = _get_settings_cached()
        username = s.get("oscom_username", "").strip()
        password = s.get("oscom_password", "").strip()
        api_key  = s.get("oscom_api_key",  "").strip()
    # Credentials check outside lock — no I/O penalty.
    if not (username and password and api_key):
        return ""
    # HTTP call happens OUTSIDE the lock so other threads are not blocked for up to 15 s.
    try:
        payload = json.dumps({"username": username, "password": password}).encode()
        req = urllib.request.Request(
            "https://api.opensubtitles.com/api/v1/login",
            data=payload,
            headers={
                "Content-Type": "application/json",
                "Api-Key": api_key,
                "User-Agent": _UA_CHROME,
            },
            method="POST",
        )
        with urllib.request.urlopen(req, timeout=15, context=_SSL_CTX) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        token = data.get("token", "")
        returned_base = data.get("base_url", "").strip()
    except urllib.error.HTTPError as e:
        _body = ""
        try:
            _body = e.read(256).decode("utf-8", errors="replace")
        except Exception:
            pass
        log.warning("OpenSubtitles: JWT login HTTP %d: %s — %s", e.code, e.reason, _body)
        return ""
    except Exception as e:
        log.warning("OpenSubtitles: JWT login failed: %s", e)
        return ""
    # Write results back under lock.
    with _oscom_jwt_lock:
        if token:
            _oscom_jwt_token  = token
            _oscom_jwt_expiry = _time_module.time() + _OSCOM_JWT_TTL
            if returned_base:
                _oscom_base_url = returned_base
                log.info("OpenSubtitles: JWT login successful (valid for 23 h, base_url=%s)",
                         _oscom_base_url)
            else:
                log.info("OpenSubtitles: JWT login successful (valid for 23 h)")
        else:
            log.warning("OpenSubtitles: login succeeded but no token in response")
        return _oscom_jwt_token

def _get_subdl_key():
    """Read the SubDL API key from cached settings."""
    return _get_settings_cached().get("subdl_api_key", "") or ""

def _get_gemini_key():
    """Read the primary Gemini API key from cached settings.
    Returns the first key from gemini_api_keys list if present,
    otherwise falls back to the legacy gemini_api_key field.
    """
    s = _get_settings_cached()
    keys = [k.strip() for k in s.get("gemini_api_keys", []) if k.strip()]
    if keys:
        return keys[0]
    return s.get("gemini_api_key", "") or ""


def _get_gemini_keys() -> list:
    """Return all configured Gemini API keys as a list (non-empty strings only).
    Merges gemini_api_keys list with legacy gemini_api_key for backward compat.
    """
    s = _get_settings_cached()
    keys = [k.strip() for k in s.get("gemini_api_keys", []) if k.strip()]
    if not keys:
        legacy = s.get("gemini_api_key", "").strip()
        if legacy:
            keys = [legacy]
    return keys

def _content_key(video_path: str) -> str:
    """Return a normalised content identity string for *video_path* that is
    stable across different CDN/stream URLs for the same show episode.

    Strategy (conservative — requires identical cleaned title + episode tag):
      • Local files  → cleaned filename stem, lowercased.
      • HTTP URLs    → run through clean_filename() which scores path segments
                       and prefers ones that contain SxxExx / year signals.
                       The result is lowercased and whitespace-collapsed.
      • Fallback     → raw video_path as-is (no match risk, no regression).

    Only returns the raw path when clean_filename() yields an empty string
    (e.g. pure-UUID URLs with no recognisable tokens) so there is zero risk
    of accidentally cross-contaminating sessions for unrelated content.
    """
    if not video_path:
        return video_path
    try:
        cleaned = clean_filename(video_path)
        if not cleaned:
            # Raw fallback: truncate to 512 chars to guard against giant CDN/OAuth URLs
            return video_path[:512]
        # Normalise: lowercase, collapse runs of whitespace
        key = re.sub(r"\s{2,}", " ", cleaned.lower()).strip()
        return key if key else video_path[:512]
    except Exception:
        return video_path[:512]


def _translation_output_path(srt_path: str, target_lang_code: str) -> Path:
    """Return the expected output path for a translated subtitle.

    Single source of truth used by both _translate_subtitle (cache-check) and
    translate_srt_with_gemini (write path).  If either drifts, the cache always
    produces a miss and translation is re-run from scratch — this helper prevents
    that by keeping both callers in sync automatically.
    """
    src = Path(srt_path)
    stem_parts = src.stem.split(".")
    # Only treat the last dot-segment as a language tag if it is a 2-letter ISO code
    # present in CODE_TO_LANG (e.g. "en", "fr").  Locale tags like "pt-BR" are NOT
    # in CODE_TO_LANG so they fall through to the else branch, which preserves the
    # full stem (including "pt-BR") and appends the target code — correct behaviour.
    if len(stem_parts) >= 2 and stem_parts[-1] in CODE_TO_LANG:
        src_lang_tag = stem_parts[-1]
        base_stem    = ".".join(stem_parts[:-1])
        out_name     = "{}.{}.{}.srt".format(base_stem, src_lang_tag, target_lang_code)
    else:
        out_name = "{}.{}.srt".format(src.stem, target_lang_code)
    return src.parent / out_name

def translate_srt_with_gemini(srt_path: str, target_lang_code: str,
                              api_key: str,
                              model_chain: list = None,
                              progress_cb=None,
                              stop_event=None,
                              warn_cb=None,
                              chunk_size: int = None,
                              api_keys: list = None) -> str:
    """Translate an SRT file to *target_lang_code* using Gemini.

    Tries each model in *model_chain* (primary -> fallback 1 -> fallback 2).
    Falls back to the next model on 404.

    If *stop_event* is a threading.Event, it is checked between chunks and
    between HTTP retry attempts.  When set, raises TranslationCancelledError
    so the caller can cleanly cancel without leaving a partial file on disk.

    Returns a 3-tuple (str path, int dropped_blocks, int total_blocks), or raises on error.
    Callers must unpack: ``out_path, dropped, total = translate_srt_with_gemini(...)``.
    """
    if model_chain is None:
        model_chain = ["gemini-2.5-flash-lite", "gemini-2.5-flash", "gemini-2.5-pro"]

    # Build effective key list for rotation.
    # api_keys overrides api_key if provided; otherwise wrap api_key as a single-item list.
    _all_keys: list = [k.strip() for k in (api_keys or []) if k.strip()]
    if not _all_keys:
        _all_keys = [api_key] if api_key else []
    # Mutable cell so inner closure can advance key index on 429 exhaustion.
    _key_idx = [0]

    log.info(
        "translate_srt_with_gemini: keys=%d  model_chain=%s  chunk_size=%s  lang=%s",
        len(_all_keys),
        model_chain,
        chunk_size if chunk_size is not None else _GEMINI_CHUNK_SIZE,
        target_lang_code,
    )

    GEMINI_BASE  = "https://generativelanguage.googleapis.com/v1beta/models/"
    CHUNK_SIZE   = chunk_size if chunk_size is not None else _GEMINI_CHUNK_SIZE
    # Read settings override but enforce a hard floor of 1.0 s to prevent
    # rate-limit hammering if the user manually sets gemini_min_sleep to 0.
    _settings_sleep = _get_settings_cached().get("gemini_min_sleep", _GEMINI_MIN_SLEEP)
    MIN_SLEEP    = max(1.0, float(_settings_sleep) if _settings_sleep else _GEMINI_MIN_SLEEP)
    MAX_RETRIES  = _GEMINI_MAX_RETRIES

    target_lang_name = CODE_TO_LANG.get(target_lang_code, target_lang_code)

    # ── Parse SRT into blocks ─────────────────────────────────────────────────
    raw = Path(srt_path).read_text(encoding="utf-8", errors="replace")
    raw_blocks = [b.strip() for b in re.split(r"\n\s*\n", raw.strip()) if b.strip()]

    # ── Build source lookup: seq -> (timestamp_line, [text_lines]) ───────────
    # Timestamps are owned entirely by the source file and never sent to Gemini.
    # This makes timestamp corruption by the model architecturally impossible.
    _TS_RE = re.compile(r"^\d{1,2}:\d{2}:\d{2}[,\.]\d{3}\s*-->")
    src_meta = {}   # seq_str -> (timestamp_line, [text_lines])
    src_order = []  # seq_str in original file order
    for b in raw_blocks:
        lines = b.splitlines()
        if not lines or not lines[0].strip().isdigit():
            continue
        seq = lines[0].strip()
        ts  = lines[1] if len(lines) > 1 and _TS_RE.match(lines[1].strip()) else ""
        txt = lines[2:] if len(lines) > 2 else (lines[1:] if not ts else [""])
        src_meta[seq] = (ts, txt)
        src_order.append(seq)

    # ── Strip timestamps from blocks before chunking ──────────────────────────
    # Send Gemini only: "seq_number\ntext_line(s)" — no timestamps at all.
    def _strip_ts(block):
        lines = block.splitlines()
        if len(lines) >= 2 and _TS_RE.match(lines[1].strip()):
            return "\n".join([lines[0]] + lines[2:])
        return block

    stripped_blocks = [_strip_ts(b) for b in raw_blocks]

    # ── Build chunks with 10-line overlap ────────────────────────────────────
    OVERLAP = _GEMINI_OVERLAP
    chunks = []
    i = 0
    while i < len(stripped_blocks):
        context = stripped_blocks[max(0, i - OVERLAP):i] if i > 0 else []
        body    = stripped_blocks[i:i + CHUNK_SIZE]
        chunks.append((context, body))
        i += CHUNK_SIZE

    total = len(chunks)
    log.info("translate_srt_with_gemini: %d blocks -> %d chunk(s)  target=%s",
             len(raw_blocks), total, target_lang_code)

    # Accumulate translated text keyed by seq number
    translated_text = {}  # seq_str -> [text_lines]
    _translated_text_lock = threading.Lock()  # guards multi-worker concurrent .update() calls

    def _parse_gemini_response(response_text):
        """Parse Gemini's timestamp-free response into {seq: [text_lines]}.

        Handles: markdown fences, duplicate seq numbers (keeps first),
        blank translations, non-seq leading lines, reordered blocks.
        """
        # Strip markdown fences Gemini sometimes wraps output in.
        # Both patterns use re.M so intermediate fences between blocks are removed,
        # not just the first opening fence and the final closing fence.
        text = re.sub(r"^```[^\n]*\n?", "", response_text.strip(), flags=re.M)
        text = re.sub(r"\n?```$", "", text.strip(), flags=re.M)
        result = {}
        for b in re.split(r"\n\s*\n", text.strip()):
            # Check the seq number using non-blank lines only, but preserve
            # blank body lines.  A block whose translation is legitimately
            # empty (e.g. [Music] -> nothing) must be stored as [""] so the
            # outer reattach loop does not fall back to the original English.
            all_lines  = b.strip().splitlines()
            non_blank  = [l for l in all_lines if l.strip()]
            if not non_blank or not non_blank[0].strip().isdigit():
                continue
            seq = non_blank[0].strip()
            # seq is guaranteed to appear in all_lines because non_blank is a
            # filtered view of all_lines — next() will never raise StopIteration here.
            seq_pos  = next(i for i, l in enumerate(all_lines) if l.strip() == seq)
            body     = all_lines[seq_pos + 1:]
            txt      = body if body else [""]
            if seq not in result:  # keep first occurrence; discard hallucinated dupes
                result[seq] = txt
        return result

    def _translate_blocks(body_blocks, context_blocks, chunk_idx, chunk_total,
                          is_retry_half=False, is_retry_prohibited=False,
                          split_depth=0, _model_idx=None, _trunc_retries_used=0):
        """Translate *body_blocks* via Gemini, returning {seq: [text_lines]}.

        Handles 8 layers of robustness: dynamic token limits, thinking budget
        control per model tier, MAX_TOKENS halving, content retries with format
        reminders, thought-entry skipping, raised timeouts, catastrophic truncation
        detection, and wrong-language escalation.

        Each recursive call receives its own independent _model_idx cursor so
        sibling calls (e.g. left/right halves) cannot corrupt each other's
        position in the model chain.
        """
        # Each call owns its own model-chain cursor.  Using a mutable [int] cell
        # (rather than a plain int) lets the inner HTTP/model-fallback loops
        # increment it in place without needing nonlocal.
        active_model_idx = [_model_idx if _model_idx is not None else 0]

        system_instruction = (
            "You are a professional subtitle translator. "
            "Your only job is to translate subtitle dialogue into {lang}. "
            "You never explain, never add markdown, never modify sequence numbers."
        ).format(lang=target_lang_name)

        context_text = ""
        if context_blocks:
            context_text = (
                "[CONTEXT ONLY - already translated, do NOT include in output]\n"
                + "\n\n".join(context_blocks)
                + "\n[END CONTEXT]\n\n"
            )

        def _build_user_message(format_reminder=False):
            reminder = ""
            if format_reminder:
                reminder = (
                    "\n\nIMPORTANT: Your previous response contained no parseable blocks. "
                    "You MUST output each block as:\n"
                    "  <sequence number>\n"
                    "  <translated text>\n\n"
                    "Example:\n42\nمرحباً بالعالم\n\n43\nكيف حالك؟\n\n"
                    "Do NOT omit sequence numbers under any circumstances.\n"
                )
            return (
                "Translate the following subtitles to {lang}.{reminder}\n\n"
                "CRITICAL REQUIREMENTS:\n"
                "1. Output ONLY the translated blocks — no explanations, no markdown, no code fences\n"
                "2. Keep every sequence number EXACTLY as-is\n"
                "3. Each block is: a sequence number on the first line, then the translated text\n"
                "4. Do NOT add or remove subtitle blocks\n"
                "5. Translate ONLY the dialogue text lines\n"
                "6. Use correct grammatical gender based on context clues such as names, "
                "pronouns, and character roles. When gender is ambiguous, choose the form "
                "most natural for the character's established context. Maintain gender "
                "consistency for recurring characters throughout the subtitles.\n\n"
                "{context}{blocks}"
            ).format(
                lang=target_lang_name,
                reminder=reminder,
                context=context_text,
                blocks="\n\n".join(body_blocks),
            )

        result_text = None
        finish_reason = ""

        for content_attempt in range(_GEMINI_CONTENT_RETRIES + 1):
            # Build payload fresh per attempt (and per model, since generationConfig
            # varies by model — thinkingBudget differs between Flash and Pro).
            # Payload is built inside the while loop so model fallbacks get
            # the correct generationConfig for whichever model is now active.

            while active_model_idx[0] < len(model_chain):
                model_name = model_chain[active_model_idx[0]]
                url = GEMINI_BASE + model_name + ":generateContent"

                # Layer 1: fetch real outputTokenLimit for this model dynamically.
                _active_key = _all_keys[_key_idx[0]] if _all_keys else api_key
                max_out = _get_model_token_limit(model_name, _active_key)

                # Layer 2: configure thinking budget per model tier.
                #
                # Gemini 3.x models use thinkingLevel (string: "minimal"/"low"/
                # "medium"/"high"). Sending thinkingBudget (the 2.5-era integer)
                # to a Gemini 3 model causes a 400 error. Sending nothing causes
                # Gemini 3 flash-lite to default to "high" thinking depth, eating
                # output tokens and causing catastrophic truncation on subtitles.
                #
                # Gemini 2.5 models use thinkingBudget (integer):
                #   flash-lite: omit thinkingConfig entirely (thinking off by default)
                #   flash non-lite: thinkingBudget=-1 (dynamic, allocates only when needed)
                #   pro: omit thinkingConfig (min budget 128, model manages internally)
                gen_cfg: dict = {"temperature": 0.1, "maxOutputTokens": max_out}
                _mn_lower = model_name.lower()
                _is_gemini3 = re.search(r"gemini-3", _mn_lower) is not None
                if _is_gemini3:
                    # Gemini 3.x: use thinkingLevel string.
                    # "minimal" suppresses reasoning overhead for flash/lite —
                    # translation does not benefit from deep reasoning and we
                    # need to preserve output tokens for subtitle text.
                    if "pro" in _mn_lower:
                        gen_cfg["thinkingConfig"] = {"thinkingLevel": "low"}
                    else:
                        # flash and flash-lite: minimal — fastest, cheapest,
                        # avoids the "high" default that truncates subtitle output.
                        gen_cfg["thinkingConfig"] = {"thinkingLevel": "minimal"}
                elif "flash" in _mn_lower and "pro" not in _mn_lower:
                    if "lite" not in _mn_lower:
                        # Gemini 2.5 flash non-lite: dynamic thinking budget
                        gen_cfg["thinkingConfig"] = {"thinkingBudget": -1}
                    # Gemini 2.5 flash-lite: omit thinkingConfig entirely (off by default)

                payload = json.dumps({
                    "system_instruction": {"parts": [{"text": system_instruction}]},
                    "contents": [{"role": "user", "parts": [{"text": _build_user_message(
                        format_reminder=(content_attempt > 0)
                    )}]}],
                    "generationConfig": gen_cfg,
                    # Explicitly disable all adjustable harm filters.  Without this,
                    # flash-lite on free-tier keys applies overly aggressive defaults
                    # that produce false PROHIBITED_CONTENT on normal dramatic dialogue.
                    # BLOCK_NONE only disables the *adjustable* layer — Google built-in
                    # protections (e.g. child safety) remain active regardless.
                    "safetySettings": [
                        {"category": "HARM_CATEGORY_HARASSMENT",        "threshold": "BLOCK_NONE"},
                        {"category": "HARM_CATEGORY_HATE_SPEECH",       "threshold": "BLOCK_NONE"},
                        {"category": "HARM_CATEGORY_SEXUALLY_EXPLICIT", "threshold": "BLOCK_NONE"},
                        {"category": "HARM_CATEGORY_DANGEROUS_CONTENT", "threshold": "BLOCK_NONE"},
                    ],
                }).encode("utf-8")

                success = False
                _503_exhausted = False  # set True when all retries were 503s → distinct error

                for attempt in range(MAX_RETRIES):
                    # Honour cancellation before each HTTP attempt so the
                    # user's stop request takes effect promptly mid-chunk.
                    if stop_event is not None and stop_event.is_set():
                        raise TranslationCancelledError("stopped by user")
                    t_start = _time_module.time()
                    log.debug(
                        "gemini request: chunk %d  attempt %d/%d  key#%d  model=%s",
                        chunk_idx, attempt + 1, MAX_RETRIES,
                        _key_idx[0] + 1, model_name,
                    )
                    try:
                        req = urllib.request.Request(
                            url, data=payload,
                            headers={
                                "Content-Type": "application/json",
                                "x-goog-api-key": _all_keys[_key_idx[0]] if _all_keys else api_key,
                            },
                            method="POST",
                        )
                        # Layer 6: raised timeout — large chunks can take >60s on
                        # thinking-disabled Flash when the model is under load.
                        with urllib.request.urlopen(req, timeout=120,
                                                    context=_SSL_CTX) as resp:
                            body = json.loads(resp.read().decode("utf-8"))

                        # Layer 5: iterate parts[], skip thought entries.
                        # On thinking-enabled models parts[0] is the internal
                        # reasoning ("thought": True) — reading it produces gibberish.
                        _parts = (
                            body.get("candidates", [{}])[0]
                                .get("content", {})
                                .get("parts", [{}])
                        )
                        result_text = ""
                        for _part in _parts:
                            if not _part.get("thought", False) and _part.get("text"):
                                result_text = _part["text"]
                                break

                        # Layer 3: detect output truncation via finishReason.
                        finish_reason = (
                            body.get("candidates", [{}])[0]
                                .get("finishReason", "")
                        )
                        if finish_reason == "MAX_TOKENS" and not is_retry_half:
                            # Recursion depth guard: each split doubles the number of
                            # API calls. Cap at depth 4 (300 -> 150 -> 75 -> 37 -> 18
                            # blocks). Beyond that the chunk is tiny enough that
                            # MAX_TOKENS indicates a model-level problem, not size --
                            # accept whatever was returned and let the reattach pass
                            # fall back to original text for the missing blocks.
                            # Total recursion depth is bounded by:
                            #   _MAX_SPLIT_DEPTH × (_GEMINI_TRUNC_RETRIES + 1) × len(model_chain)
                            # With defaults 4 × 3 × 3 = 36 — well within Python's recursion limit.
                            _MAX_SPLIT_DEPTH = 4
                            if split_depth >= _MAX_SPLIT_DEPTH:
                                log.warning(
                                    "Gemini MAX_TOKENS on chunk %d (model %s) at "
                                    "split_depth=%d >= %d -- depth limit reached, "
                                    "accepting partial result (%d blocks)",
                                    chunk_idx, model_name, split_depth,
                                    _MAX_SPLIT_DEPTH, len(body_blocks),
                                )
                                return _parse_gemini_response(result_text) if result_text else {}
                            log.warning(
                                "Gemini MAX_TOKENS on chunk %d (model %s) -- "
                                "splitting in half and retrying each half "
                                "(split_depth=%d)",
                                chunk_idx, model_name, split_depth,
                            )
                            mid = len(body_blocks) // 2
                            left  = body_blocks[:mid]
                            right = body_blocks[mid:]
                            merged = {}
                            # Pass current model index forward -- MAX_TOKENS is a
                            # size problem, not a model failure, so no need to reset.
                            # Pass split_depth+1 so the depth guard applies if a
                            # half also hits MAX_TOKENS.
                            _cur_idx = active_model_idx[0]
                            merged.update(_translate_blocks(
                                left,  context_blocks, chunk_idx, chunk_total,
                                is_retry_half=True,
                                split_depth=split_depth + 1,
                                _model_idx=_cur_idx))
                            merged.update(_translate_blocks(
                                right, left[-_GEMINI_OVERLAP:] if left else [],
                                chunk_idx, chunk_total,
                                is_retry_half=True,
                                split_depth=split_depth + 1,
                                _model_idx=_cur_idx))
                            return merged

                        if finish_reason == "PROHIBITED_CONTENT":
                            if len(body_blocks) == 1:
                                # Single offending block — return empty so the
                                # dropped-block fallback keeps the original English.
                                log.warning(
                                    "Gemini PROHIBITED_CONTENT on chunk %d single block"
                                    " — keeping original English for this block",
                                    chunk_idx,
                                )
                                return {}
                            # If this is already a retry half, don't split again —
                            # escalate to the next model instead.  One split max.
                            if is_retry_prohibited:
                                next_idx = active_model_idx[0] + 1
                                if next_idx < len(model_chain):
                                    log.warning(
                                        "Gemini PROHIBITED_CONTENT on chunk %d retry-half"
                                        " (model %s, %d blocks)"
                                        " — escalating to next model: %s",
                                        chunk_idx, model_name, len(body_blocks),
                                        model_chain[next_idx],
                                    )
                                    return _translate_blocks(
                                        body_blocks, context_blocks,
                                        chunk_idx, chunk_total,
                                        is_retry_prohibited=True,
                                        _model_idx=next_idx,
                                    )
                                log.warning(
                                    "Gemini PROHIBITED_CONTENT on chunk %d retry-half"
                                    " — all models exhausted"
                                    " — keeping original English for %d block(s)",
                                    chunk_idx, len(body_blocks),
                                )
                                if warn_cb:
                                    warn_cb(
                                        "A content block in chunk {} was flagged by Gemini's safety filter "
                                        "and could not be translated. The original text has been kept.\n\n"
                                        "If this happens often, try lowering \"Blocks per request\" in "
                                        "Settings \u2192 Configure Gemini \u2014 smaller chunks isolate flagged lines "
                                        "more precisely.".format(chunk_idx + 1)
                                    )
                                return {}
                            log.warning(
                                "Gemini PROHIBITED_CONTENT on chunk %d (model %s, %d blocks)"
                                " — splitting in half to isolate offending block(s)",
                                chunk_idx, model_name, len(body_blocks),
                            )
                            mid = len(body_blocks) // 2
                            left  = body_blocks[:mid]
                            right = body_blocks[mid:]
                            merged = {}
                            merged.update(_translate_blocks(
                                left,  context_blocks, chunk_idx, chunk_total,
                                is_retry_prohibited=True,
                                _model_idx=active_model_idx[0]))
                            merged.update(_translate_blocks(
                                right, left[-_GEMINI_OVERLAP:] if left else [],
                                chunk_idx, chunk_total,
                                is_retry_prohibited=True,
                                _model_idx=active_model_idx[0]))
                            return merged

                        # Guard: HTTP 200 but no usable text extracted (Shapes B–F:
                        # missing candidates key, no content.parts, empty parts list,
                        # thought-only parts, or empty-string text part).
                        # Shape A (candidates: []) already raises IndexError above and
                        # is retried by the generic except handler — no fix needed there.
                        # Treating this as a transient server-side failure and retrying
                        # the HTTP call is correct; burning a content_attempt here would
                        # be wrong because the prompt is not the problem.
                        if not result_text:
                            log.warning(
                                "Gemini chunk %d returned HTTP 200 but no usable text "
                                "(finishReason=%r, attempt %d/%d, model %s) — retrying",
                                chunk_idx, finish_reason, attempt + 1, MAX_RETRIES, model_name,
                            )
                            if attempt < MAX_RETRIES - 1:
                                elapsed = _time_module.time() - t_start
                                _time_module.sleep(max(0.0, MIN_SLEEP - elapsed))
                                continue
                            # Exhausted HTTP retries with no text — fall through to
                            # model fallback by not setting success=True.
                            break

                        success = True

                        elapsed_req = _time_module.time() - t_start
                        log.debug(
                            "gemini response: chunk %d  key#%d  model=%s  "
                            "finishReason=%r  elapsed=%.1fs",
                            chunk_idx, _key_idx[0] + 1, model_name,
                            finish_reason, elapsed_req,
                        )

                        if chunk_idx < chunk_total - 1:
                            elapsed = _time_module.time() - t_start
                            remaining = max(0.0, MIN_SLEEP - elapsed)
                            if remaining > 0:
                                _time_module.sleep(remaining)
                        break

                    except urllib.error.HTTPError as e:
                        err_body = ""
                        try:
                            err_body = e.read().decode("utf-8", errors="replace")
                        except Exception:
                            pass
                        try:
                            err_code = json.loads(err_body).get("error", {}).get("code", e.code)
                        except Exception:
                            err_code = e.code

                        if err_code == 404:
                            log.warning("Gemini 404: model %r not found - trying next fallback",
                                        model_name)
                            break

                        if err_code in (429, 503):
                            reason = "rate-limited" if err_code == 429 else "overloaded"

                            if err_code == 429:
                                # ── Parse the structured error body Google returns ──
                                # details[].violations[].quotaId tells us which limit
                                # was hit:
                                #   "...PerMinute..."  → RPM or TPM (transient, ~60s)
                                #   "...PerDay..."     → RPD (daily quota exhausted)
                                #   anything else      → treat as transient
                                # details[].retryDelay (e.g. "34s") is Google's own
                                # recommended wait — use it instead of guessing.
                                quota_id   = ""
                                retry_secs = None
                                try:
                                    err_json = json.loads(err_body)
                                    details  = (err_json.get("error", {})
                                                        .get("details", []))
                                    for d in details:
                                        if d.get("@type", "").endswith("QuotaFailure"):
                                            viols = d.get("violations", [])
                                            if viols:
                                                quota_id = viols[0].get("quotaId", "")
                                        if d.get("@type", "").endswith("RetryInfo"):
                                            rd = d.get("retryDelay", "")
                                            # retryDelay is a string like "34s"
                                            m = re.match(r"(\d+)", rd)
                                            if m:
                                                retry_secs = int(m.group(1))
                                            elif rd:
                                                log.warning(
                                                    "Gemini retryDelay present but unrecognised "
                                                    "format %r — falling back to exponential backoff",
                                                    rd,
                                                )
                                except Exception:
                                    pass

                                is_rpd = "PerDay" in quota_id

                                if is_rpd:
                                    # Daily quota exhausted on this (key, model).
                                    # Mark it so other threads skip it too, then
                                    # try the next key on the same model.
                                    cur_key = _all_keys[_key_idx[0]] if _all_keys else ""
                                    if cur_key:
                                        _rpd_add(cur_key, model_name)
                                        log.warning(
                                            "Gemini RPD exhausted: key #%d model %s "
                                            "(chunk %d) — marking dead for today",
                                            _key_idx[0] + 1, model_name, chunk_idx)

                                    # Try the next key that is not RPD-exhausted
                                    # on this model.
                                    rotated = False
                                    if len(_all_keys) > 1:
                                        for _ki in range(1, len(_all_keys)):
                                            candidate_idx = (_key_idx[0] + _ki) % len(_all_keys)
                                            candidate_key = _all_keys[candidate_idx]
                                            if not _rpd_check(candidate_key, model_name):
                                                log.warning(
                                                    "Gemini RPD: rotating to key #%d "
                                                    "for model %s (chunk %d)",
                                                    candidate_idx + 1, model_name, chunk_idx)
                                                _key_idx[0] = candidate_idx
                                                rotated = True
                                                break

                                    if not rotated:
                                        # All keys are RPD-exhausted on this model.
                                        # Signal model escalation by breaking the
                                        # attempt loop without setting success=True.
                                        log.warning(
                                            "Gemini RPD: all keys exhausted on model %s "
                                            "(chunk %d) — escalating model",
                                            model_name, chunk_idx)
                                        break  # → falls into model-escalation logic
                                    continue  # retry with new key

                                else:
                                    # Transient RPM / TPM limit.
                                    # Rotate key first (instant, no sleep needed).
                                    if len(_all_keys) > 1:
                                        next_key_idx = (_key_idx[0] + 1) % len(_all_keys)
                                        if next_key_idx != _key_idx[0]:
                                            log.warning(
                                                "Gemini 429 RPM key #%d (chunk %d, model %s)"
                                                " - rotating to key #%d",
                                                _key_idx[0] + 1, chunk_idx, model_name,
                                                next_key_idx + 1)
                                            _key_idx[0] = next_key_idx
                                            continue

                                    # No other key available — sleep using Google's
                                    # retryDelay if present, else exponential backoff.
                                    if retry_secs is not None:
                                        wait = float(retry_secs) + _random.uniform(0, 2)
                                        log.warning(
                                            "Gemini 429 RPM (chunk %d, attempt %d, model %s)"
                                            " - sleeping %.0fs (retryDelay)",
                                            chunk_idx, attempt + 1, model_name, wait)
                                    else:
                                        wait = min(
                                            MIN_SLEEP * (2 ** attempt) + _random.uniform(0, 2),
                                            60.0,
                                        )
                                        log.warning(
                                            "Gemini 429 RPM (chunk %d, attempt %d, model %s)"
                                            " - sleeping %.0fs (backoff)",
                                            chunk_idx, attempt + 1, model_name, wait)
                                    _time_module.sleep(wait)
                                    continue

                            else:
                                # 503 — server overloaded, not a quota issue.
                                # Exponential backoff with jitter, 60s ceiling.
                                wait = min(
                                    MIN_SLEEP * (2 ** attempt) + _random.uniform(0, 2),
                                    60.0,
                                )
                                log.warning(
                                    "Gemini 503 overloaded (chunk %d, attempt %d, model %s)"
                                    " - sleeping %.0fs",
                                    chunk_idx, attempt + 1, model_name, wait)
                                _time_module.sleep(wait)
                                if attempt >= MAX_RETRIES - 1:
                                    # All retries spent on 503s — escalate to next model.
                                    _503_exhausted = True
                                    break
                                continue

                        raise RuntimeError(
                            "Gemini API error {}: {}".format(e.code, err_body[:300])
                        )

                    except Exception as exc:
                        if attempt < MAX_RETRIES - 1:
                            log.warning("Gemini request failed (chunk %d, attempt %d): %s",
                                        chunk_idx, attempt + 1, exc)
                            elapsed = _time_module.time() - t_start
                            _time_module.sleep(max(MIN_SLEEP, MIN_SLEEP - elapsed))
                            continue
                        # On the final attempt, check whether this is a timeout/network
                        # error.  If so, treat it like 503 exhaustion so the outer loop
                        # can advance to the next model instead of dying entirely.
                        if isinstance(exc, (TimeoutError, OSError)):
                            log.warning(
                                "Gemini request timed out on last attempt "
                                "(chunk %d, model %s) — escalating to next model",
                                chunk_idx, model_name,
                            )
                            _503_exhausted = True
                            break
                        raise

                if success:
                    # Propagate the winning model index back to the outer loop so
                    # the next chunk starts on the same model (e.g. after a 404
                    # caused an advance from flash-lite to flash, the next chunk
                    # should not retry flash-lite again).
                    # NOTE: _chunk_model_idx is defined at ~line 3168, after this
                    # closure, but is guaranteed to be bound before _translate_blocks
                    # is ever *called* (only dispatched from _worker which runs after
                    # all module-level code in translate_srt_with_gemini completes).
                    _chunk_model_idx[0] = active_model_idx[0]
                    break

                active_model_idx[0] += 1
                if active_model_idx[0] >= len(model_chain):
                    if _503_exhausted:
                        raise RuntimeError(
                            "All translation models are overloaded (503). "
                            "Gemini's servers are under heavy load. "
                            "Wait a few minutes and try again."
                        )
                    raise RuntimeError(
                        "All translation models returned 404. "
                        "Please update model names in Settings - Models."
                    )
                log.info("Falling back to model: %s", model_chain[active_model_idx[0]])

            if result_text is None:
                log.error(
                    "gemini chunk %d: all keys RPD-exhausted on model %s "
                    "and no further models available — raising hard error",
                    chunk_idx,
                    model_chain[min(active_model_idx[0], len(model_chain) - 1)],
                )
                raise RuntimeError(
                    "Daily request limit reached for '{}'. "
                    "Quota resets at midnight Pacific Time. "
                    "Try again tomorrow, or update your model in Settings - Models.".format(
                        model_chain[min(active_model_idx[0], len(model_chain) - 1)]
                    )
                )

            parsed = _parse_gemini_response(result_text)

            # Layer 8: detect wrong-language response — Gemini 2.5 flash-lite has a
            # documented bug where it returns the *source* text verbatim (untranslated)
            # with finishReason=STOP and a full block count, so Layer 7 never fires.
            _script_range = _SCRIPT_RANGES.get(target_lang_code)
            if _script_range and parsed and len(parsed) >= 5:
                _sample_text = " ".join(
                    " ".join(lines) for lines in list(parsed.values())[:50]
                )
                _total_chars = len(_sample_text.replace(" ", ""))
                if _total_chars > 0:
                    _lo, _hi = _script_range
                    _target_chars = sum(1 for c in _sample_text if _lo <= ord(c) <= _hi)
                    _target_ratio = _target_chars / _total_chars
                    _thresh = _SCRIPT_WRONG_LANG_THRESHOLD.get(
                        target_lang_code, _SCRIPT_WRONG_LANG_THRESHOLD_DEFAULT
                    )
                    if _target_ratio < _thresh:
                        has_next = active_model_idx[0] + 1 < len(model_chain)
                        if has_next:
                            next_idx = active_model_idx[0] + 1
                            log.warning(
                                "Gemini chunk %d response appears untranslated "
                                "(target-script ratio=%.1f%% < %.0f%% for lang=%r, model=%s) "
                                "— escalating to next model: %s",
                                chunk_idx, _target_ratio * 100, _thresh * 100,
                                target_lang_code, model_name, model_chain[next_idx],
                            )
                            result = _translate_blocks(
                                body_blocks, context_blocks, chunk_idx, chunk_total,
                                is_retry_half=is_retry_half,
                                is_retry_prohibited=is_retry_prohibited,
                                split_depth=split_depth,
                                _model_idx=next_idx,
                                _trunc_retries_used=0,
                            )
                            _chunk_model_idx[0] = next_idx
                            return result
                        else:
                            log.warning(
                                "Gemini chunk %d response appears untranslated "
                                "(target-script ratio=%.1f%% < %.0f%% for lang=%r, model=%s) "
                                "— no fallback model available; accepting output as-is.",
                                chunk_idx, _target_ratio * 100, _thresh * 100,
                                target_lang_code, model_name,
                            )
                            if warn_cb:
                                warn_cb(
                                    "Translation warning: chunk {} may be untranslated "
                                    "(only {:.0f}% target-script characters detected). "
                                    "Try adding a stronger model as fallback.".format(
                                        chunk_idx, _target_ratio * 100)
                                )

            # Layer 7: detect catastrophic truncation — Gemini returned text and
            # claimed STOP but translated fewer than 90% of the blocks it was given.
            # This is a documented Gemini 2.5 bug where finishReason is STOP but
            # output is silently cut short.  Truncation is a transient server-side
            # fluke unrelated to chunk size, so splitting in half is the wrong fix
            # (it cascades into more API calls, more PROHIBITED_CONTENT hits, and
            # more 503s).  Instead we retry the same chunk up to _GEMINI_TRUNC_RETRIES
            # times with a short sleep.  If all retries fail we accept the partial
            # result; the outer reattach loop keeps original text for missing blocks.
            # Guard: only fires when chunk is > 4 blocks (smaller chunks may
            # legitimately have a few untranslatable blocks) and finishReason is not
            # MAX_TOKENS or PROHIBITED_CONTENT (both already handled above).
            if (len(body_blocks) > 4
                    and len(parsed) < int(len(body_blocks) * 0.90)
                    and finish_reason not in ("MAX_TOKENS", "PROHIBITED_CONTENT")):
                if _trunc_retries_used < _GEMINI_TRUNC_RETRIES:
                    log.warning(
                        "Gemini chunk %d returned only %d/%d blocks with finishReason=%r "
                        "(model %s) — catastrophic truncation, retrying same chunk "
                        "(%d/%d trunc retries)",
                        chunk_idx, len(parsed), len(body_blocks), finish_reason,
                        model_name, _trunc_retries_used + 1, _GEMINI_TRUNC_RETRIES,
                    )
                    _time_module.sleep(MIN_SLEEP)
                    # Recurse with incremented _trunc_retries_used so this call
                    # owns its own retry budget independently of any sibling calls.
                    return _translate_blocks(
                        body_blocks, context_blocks, chunk_idx, chunk_total,
                        is_retry_half=is_retry_half,
                        is_retry_prohibited=is_retry_prohibited,
                        split_depth=split_depth,
                        _model_idx=active_model_idx[0],
                        _trunc_retries_used=_trunc_retries_used + 1,
                    )
                # All truncation retries exhausted on this model.
                # Escalate to the next model in the chain — persistent truncation
                # means this model cannot handle this chunk, not a transient fluke.
                next_idx = active_model_idx[0] + 1
                if next_idx < len(model_chain):
                    log.warning(
                        "Gemini chunk %d truncation persists after %d retries on model %s"
                        " — escalating to next model: %s",
                        chunk_idx, _GEMINI_TRUNC_RETRIES, model_name,
                        model_chain[next_idx],
                    )
                    result = _translate_blocks(
                        body_blocks, context_blocks, chunk_idx, chunk_total,
                        is_retry_half=is_retry_half,
                        is_retry_prohibited=is_retry_prohibited,
                        split_depth=split_depth,
                        _model_idx=next_idx,
                        _trunc_retries_used=0,
                    )
                    _chunk_model_idx[0] = next_idx
                    return result
                # Entire model chain exhausted — accept partial result as last resort.
                # Missing blocks fall back to original text in the reattach pass.
                log.warning(
                    "Gemini chunk %d truncation persists across all models after %d retries"
                    " — accepting partial result (%d/%d blocks)",
                    chunk_idx, _GEMINI_TRUNC_RETRIES, len(parsed), len(body_blocks),
                )
                return parsed

            # Layer 4: if Gemini returned text but 0 blocks parsed, it likely omitted
            # sequence numbers (a known failure mode). Retry with an augmented prompt
            # that shows the required format explicitly. Only retry for total failures
            # (0 blocks) — partial drops are handled by the dropped-block fallback below.
            if len(parsed) == 0 and content_attempt < _GEMINI_CONTENT_RETRIES:
                log.warning(
                    "Gemini chunk %d returned 0 parseable blocks "
                    "(finishReason=%r, content_attempt=%d) — retrying with format reminder",
                    chunk_idx, finish_reason, content_attempt + 1,
                )
                result_text = None  # force fresh API call on next iteration
                continue

            if len(parsed) == 0 and content_attempt == _GEMINI_CONTENT_RETRIES:
                raise RuntimeError(
                    "Gemini returned 0 parseable blocks for chunk {} after {} retries. "
                    "The model may be ignoring sequence number requirements. "
                    "Try again or switch to a different model in Settings - Models.".format(
                        chunk_idx, _GEMINI_CONTENT_RETRIES
                    )
                )

            return parsed

        return {}  # unreachable but satisfies linters

    # ── Shared RPD-exhaustion registry ───────────────────────────────────────
    # Tracks (api_key_string, model_name) pairs whose daily quota is gone.
    # Written by whichever thread first hits an RPD 429 on that combination;
    # read by all threads before attempting a request so we skip known-dead
    # pairs without wasting an API call.  Protected by a lock because set.add
    # is not atomic across threads in all Python implementations.
    _rpd_exhausted: set = set()
    _rpd_lock = threading.Lock()

    # Wrap set operations so the inner closure can use them without capturing
    # the lock by name (closures capture the variable, not the value).
    def _rpd_add(key_str, model_str):
        with _rpd_lock:
            _rpd_exhausted.add((key_str, model_str))

    def _rpd_check(key_str, model_str):
        with _rpd_lock:
            return (key_str, model_str) in _rpd_exhausted

    # _chunk_model_idx tracks which model index won the last chunk so the next
    # chunk skips straight to the working model.  With parallel workers each
    # thread must have its own independent cursor — we use threading.local()
    # so the _translate_blocks closure sees the right value per thread.
    # The [0] cell trick still works because each thread gets its own .val list.
    _tl = threading.local()

    def _get_chunk_model_idx():
        if not hasattr(_tl, "chunk_model_idx"):
            _tl.chunk_model_idx = [0]
        return _tl.chunk_model_idx

    # Single generic proxy class — used for both _chunk_model_idx and _key_idx.
    # Takes a *getter* callable that returns the current thread's [int] cell so
    # both proxies share the same __getitem__/__setitem__ logic.
    class _ThreadLocalCell:
        """Proxy that delegates [0] access to a thread-local [int] cell.

        Parameters
        ----------
        getter : callable
            Zero-argument callable that returns the current thread's [int] list.
        """
        def __init__(self, getter):
            self._getter = getter
        def __getitem__(self, _):
            return self._getter()[0]
        def __setitem__(self, _, val):
            self._getter()[0] = val

    _chunk_model_idx = _ThreadLocalCell(_get_chunk_model_idx)

    # ── Progress counter shared across worker threads ─────────────────────────
    _chunks_done   = [0]
    _progress_lock = threading.Lock()

    def _report_progress(chunk_idx):
        """Increment the shared counter and call progress_cb if provided."""
        with _progress_lock:
            _chunks_done[0] += 1
            done = _chunks_done[0]
        if progress_cb:
            try:
                progress_cb(chunk_idx, total)
            except Exception:
                pass

    # ── Per-thread _key_idx proxy ─────────────────────────────────────────────
    # _key_idx is referenced inside _translate_blocks as a mutable [int] cell.
    # With parallel workers each thread needs its own key cursor so they don't
    # overwrite each other.  Same _ThreadLocalCell proxy; different getter.
    _key_tl = threading.local()

    def _get_key_idx():
        if not hasattr(_key_tl, "val"):
            _key_tl.val = [0]
        return _key_tl.val

    # Replace the original shared _key_idx cell with the thread-local proxy.
    _key_idx = _ThreadLocalCell(_get_key_idx)

    # ── Worker function — one per key, runs its assigned chunk slice ──────────
    def _worker(key_index: int, assigned_chunks: list):
        """Translate a slice of chunks using a single pinned API key.

        key_index        – index into _all_keys; this thread owns that key.
        assigned_chunks  – list of (chunk_idx, context_blocks, body_blocks)
                           tuples assigned to this worker.

        Each thread has its own model-chain cursor (_chunk_model_idx is
        thread-local) and its own key cursor (_key_idx is thread-local).
        Results are written into translated_text under _translated_text_lock,
        which guards concurrent .update() calls from parallel workers.
        """
        # Seed this thread's key cursor to its assigned key.
        _key_idx[0] = key_index

        log.debug(
            "gemini worker key#%d started: %d chunk(s) assigned %s",
            key_index + 1,
            len(assigned_chunks),
            [c[0] for c in assigned_chunks],
        )

        for chunk_idx, context_blocks, body_blocks in assigned_chunks:
            if stop_event is not None and stop_event.is_set():
                raise TranslationCancelledError("stopped by user")

            log.debug(
                "gemini worker key#%d -> chunk %d/%d start  model=%s  blocks=%d",
                key_index + 1, chunk_idx + 1, total,
                model_chain[_chunk_model_idx[0]],
                len(body_blocks),
            )
            t_chunk = _time_module.time()

            result = _translate_blocks(
                body_blocks, context_blocks, chunk_idx, total,
                _model_idx=_chunk_model_idx[0],
            )
            with _translated_text_lock:
                translated_text.update(result)

            elapsed_chunk = _time_module.time() - t_chunk
            log.debug(
                "gemini worker key#%d -> chunk %d/%d done  "
                "blocks_returned=%d  elapsed=%.1fs  model=%s",
                key_index + 1, chunk_idx + 1, total,
                len(result),
                elapsed_chunk,
                # NOTE: _chunk_model_idx[0] is updated to the winning model index
                # inside _translate_blocks.  If the chunk caused a model escalation
                # (e.g. flash-lite → flash due to a 404), this shows the new model,
                # not the one that was tried first — cosmetically correct.
                model_chain[_chunk_model_idx[0]],
            )

            _report_progress(chunk_idx)

    # ── Distribute chunks across workers ──────────────────────────────────────
    # With N keys, worker i gets chunks [i, i+N, i+2N, …].
    # This spreads quota evenly from the start rather than concentrating all
    # early chunks on key 1.
    n_workers = max(1, len(_all_keys))

    worker_assignments: list = [[] for _ in range(n_workers)]
    for idx, (context_blocks, body_blocks) in enumerate(chunks):
        worker_idx = idx % n_workers
        worker_assignments[worker_idx].append((idx, context_blocks, body_blocks))

    log.info(
        "gemini dispatch: %d chunk(s), %d worker(s), model_chain=%s",
        total, n_workers, model_chain,
    )
    for ki in range(n_workers):
        log.debug(
            "  worker key#%d assigned chunks: %s",
            ki + 1, [c[0] for c in worker_assignments[ki]],
        )

    worker_errors = []  # collect per-worker exceptions in parallel mode
    if n_workers == 1:
        # Single key — run inline without spawning a thread (avoids overhead
        # and keeps behaviour identical to the old sequential loop).
        log.debug("gemini dispatch: single-worker mode (1 key), running inline")
        _worker(0, worker_assignments[0])
    else:
        def _safe_worker(key_index, assigned):
            try:
                _worker(key_index, assigned)
            except TranslationCancelledError:
                raise
            except Exception:
                raise  # surfaces via f.exception() in as_completed loop below

        # Stagger thread starts so all workers do not fire into the same
        # 60-second RPM window simultaneously.
        stagger_secs = MIN_SLEEP / n_workers   # e.g. 4.5s / 3 = 1.5s per thread
        log.debug(
            "gemini dispatch: parallel mode  workers=%d  stagger=%.1fs",
            n_workers, stagger_secs,
        )

        with _cf.ThreadPoolExecutor(max_workers=n_workers) as executor:
            futures = []
            for ki in range(n_workers):
                if worker_assignments[ki]:
                    if ki > 0:
                        log.debug(
                            "gemini dispatch: sleeping %.1fs before starting worker key#%d",
                            stagger_secs, ki + 1,
                        )
                        _time_module.sleep(stagger_secs)
                    log.debug("gemini dispatch: submitting worker key#%d", ki + 1)
                    futures.append(
                        executor.submit(_safe_worker, ki, worker_assignments[ki])
                    )
            # Wait for ALL workers to finish before checking errors.
            # Do NOT raise on the first exception — let surviving workers finish
            # and contribute their translated blocks.  Only raise if something
            # catastrophic happened (cancellation or all workers failed and nothing
            # was translated at all — caught below after the reattach pass).
            for f in _cf.as_completed(futures):
                exc = f.exception()
                if exc is not None and isinstance(exc, TranslationCancelledError):
                    raise exc
                if exc is not None:
                    log.warning(
                        "gemini dispatch: a worker failed (%s) — "
                        "other workers will continue; partial results will be used",
                        exc,
                    )
                    worker_errors.append(exc)

        log.debug("gemini dispatch: all workers finished")

    # ── Reattach source timestamps in original file order ─────────────────────
    # Walk src_order (guaranteed correct sequence) and build final SRT blocks.
    # For any seq Gemini dropped or corrupted, fall back to original English text.
    translated_blocks = []
    dropped = 0
    for seq in src_order:
        ts, orig_txt = src_meta[seq]
        txt = translated_text.get(seq)
        if not txt or not any(t.strip() for t in txt):
            txt = orig_txt  # Gemini dropped or blanked this block — keep original
            dropped += 1
        translated_blocks.append("\n".join([seq, ts] + txt))
    if dropped:
        log.warning("translate_srt_with_gemini: %d block(s) missing from Gemini response"
                    " — kept original text as fallback", dropped)

    # If parallel workers had errors, check if we still got useful output.
    # If ALL blocks fell back to original (nothing was translated), surface
    # the first worker error so the user gets a clear failure message.
    if n_workers > 1 and worker_errors and dropped == len(src_order):
        raise worker_errors[0]

    # ── Write output file ─────────────────────────────────────────────────────
    # Use the shared helper for the base output path so it stays in sync with
    # the cache-check in _translate_subtitle.  Collision avoidance appends a
    # counter suffix when the base path already exists.
    src = Path(srt_path)
    stem_parts = src.stem.split(".")
    if len(stem_parts) >= 2 and stem_parts[-1] in CODE_TO_LANG:
        src_lang_tag = stem_parts[-1]
        base_stem = ".".join(stem_parts[:-1])
    else:
        src_lang_tag = ""
        base_stem = src.stem

    out_path = _translation_output_path(srt_path, target_lang_code)
    _c = 1
    while out_path.exists():
        tag = "{}.{}".format(target_lang_code, _c) if not src_lang_tag else \
              "{}.{}.{}".format(src_lang_tag, target_lang_code, _c)
        out_path = src.parent / "{}.{}.srt".format(base_stem, tag)
        _c += 1

    out_path.write_text("\n\n".join(translated_blocks) + "\n", encoding="utf-8")
    log.info("translate_srt_with_gemini: wrote %s  (translated=%d/%d blocks)",
             out_path, len(src_order) - dropped, len(src_order))
    return str(out_path), dropped, len(src_order)


def download_with_subliminal(sub, video_path="", dest=None):
    if not SUBLIMINAL_OK: return None
    sub_obj = sub._sub_obj
    if not sub_obj or not hasattr(sub_obj, "provider_name"):
        # Restored from session cache — _sub_obj defaults to "" (not None) because
        # Sub.__init__ uses "" as the default for all slots except target_episode.
        # The original "is None" check never fired, bypassing the re-fetch path entirely.
        # Look up the direct download URL we stored in the cache index on first download.
        idx = _load_cache_index()
        direct_url = idx.get("direct_url:" + sub.sub_id, "")
        if direct_url:
            log.info("subliminal download (cache restore via direct URL): %r", sub.release)
            out = Path(dest) if dest else TEMP_DIR / "subliminal_direct_{}.srt".format(sub.sub_id)
            if download_binary(direct_url, out) and out.stat().st_size > 100:
                return str(out)
        
        log.info("subliminal download: _sub_obj missing (cached). Re-fetching...")

        # Fast path: if we stored the file_id at search time, use the OpenSubtitles
        # /download endpoint directly — no search needed at all.
        _fid = getattr(sub, "file_id", "") or ""
        if _fid and sub.provider in ("opensubtitlescom", "opensubtitles",
                                     ):
            try:
                _oscom_key = _get_oscom_key() or ""
                _jwt       = _get_oscom_jwt()
                _hdr = {
                    "Content-Type": "application/json",
                    "Api-Key":      _oscom_key,
                    "User-Agent":   _UA_CHROME,
                }
                if _jwt:
                    _hdr["Authorization"] = "Bearer " + _jwt
                _payload = json.dumps({"file_id": int(_fid)}).encode()
                _req = urllib.request.Request(
                    "https://api.opensubtitles.com/api/v1/download",
                    data=_payload, headers=_hdr, method="POST")
                with urllib.request.urlopen(_req, timeout=20, context=_SSL_CTX) as _r:
                    _link = json.loads(_r.read()).get("link", "")
                if _link:
                    log.info("subliminal: direct file_id download for %r  fid=%s", sub.release, _fid)
                    out = Path(dest) if dest else TEMP_DIR / "subliminal_direct_{}.srt".format(sub.sub_id)
                    if download_binary(_link, out) and out.stat().st_size > 100:
                        with _cache_index_lock:
                            idx = _load_cache_index(autosave=False)
                            idx["direct_url:" + sub.sub_id] = _link
                            _save_cache_index(idx)
                        return str(out)
            except Exception as e:
                log.warning("subliminal: file_id direct download failed (%s) — falling back to search", e)

        pname = sub.provider.split("/")[-1].strip()
        fresh_subs = search_with_subliminal(sub.release, sub.language, video_path, providers=[pname])
        for fs in fresh_subs:
            if fs.sub_id == sub.sub_id:
                sub._sub_obj = fs._sub_obj
                sub_obj = sub._sub_obj
                break

        if not sub_obj or not hasattr(sub_obj, "provider_name"):
            # Provider pool may not be initialised yet — warm it up with a broad
            # title search, then retry the specific release once more.
            log.info("subliminal: re-fetch returned 0 — warming provider pool and retrying...")
            _broad_q = re.sub(r"[\.\-_]", " ", sub.release)[:60].strip()
            try:
                search_with_subliminal(_broad_q, sub.language, video_path, providers=[pname])
            except Exception:
                pass
            fresh_subs = search_with_subliminal(sub.release, sub.language, video_path, providers=[pname])
            for fs in fresh_subs:
                if fs.sub_id == sub.sub_id:
                    sub._sub_obj = fs._sub_obj
                    sub_obj = sub._sub_obj
                    break

        if not sub_obj or not hasattr(sub_obj, "provider_name"):
            log.error("subliminal: could not re-fetch _sub_obj for %r", sub.release)
            return None
    log.info("subliminal download: %r from %s", sub.release, sub.provider)

    video_obj = None
    if video_path and Path(video_path).is_file():
        try:
            video_obj = Video.fromname(video_path)
        except Exception as _ve:
            log.debug("subliminal download: Video.fromname(%r) failed: %s", video_path, _ve)
    if video_obj is None:
        try:
            video_obj = Video.fromname("{}.mkv".format(re.sub(r"\s+", ".", sub.release)))
        except Exception as e:
            log.error("subliminal download: cannot build Video: %s", e); return None

    try:
        from subliminal.subtitle import Subtitle as _SubtitleBase
    except ImportError:
        _SubtitleBase = object
    if not isinstance(sub_obj, _SubtitleBase):
        log.error("subliminal download error: sub_obj is not a Subtitle instance (got %r) — skipping", type(sub_obj))
        return None

    try:
        pname = getattr(sub_obj,"provider_name", sub.provider.split("/")[-1].strip())
        with ProviderPool(providers=[pname]) as pool:
            pool.download_subtitle(sub_obj)
    except Exception as e:
        log.error("subliminal download error: %s\n%s", e, traceback.format_exc()); return None

    if not sub_obj.content:
        log.warning("subliminal: no content after download for %r — trying direct fallback", sub.release)
        direct_url = (getattr(sub_obj,"download_link","") or getattr(sub_obj,"url","") or
                      getattr(sub_obj,"page_link",""))
        file_id = getattr(sub_obj,"file_id",None) or getattr(sub_obj,"id",None)
        if file_id:
            try:
                payload = json.dumps({"file_id": int(file_id)}).encode()
                req = urllib.request.Request(
                    "https://api.opensubtitles.com/api/v1/download", data=payload,
                    headers={"Content-Type":"application/json","Accept":"application/json",
                             "User-Agent":_UA_CHROME,"Api-Key":_get_oscom_key()},
                    method="POST")
                with urllib.request.urlopen(req, timeout=15, context=_SSL_CTX) as resp:
                    direct_url = json.loads(resp.read()).get("link","")
            except Exception as dl_e:
                log.warning("  opensubtitlescom download API failed: %s", dl_e)
        if direct_url and _URL_SCHEME_RE.match(direct_url):
            out = Path(dest) if dest else TEMP_DIR / "subliminal_direct_{}.srt".format(hashlib.md5(str(file_id or direct_url).encode("utf-8")).hexdigest())
            if download_binary(direct_url, out) and out.stat().st_size > 100:
                with _cache_index_lock:
                    idx = _load_cache_index(autosave=False)
                    idx["direct_url:" + sub.sub_id] = direct_url
                    _save_cache_index(idx)
                return str(out)
        log.error("subliminal: no content and no fallback URL for %r", sub.release); return None

    fmt_attr = getattr(sub_obj,"format",None)
    ext = ".{}".format(str(fmt_attr).lower().lstrip(".")) if fmt_attr else ".srt"
    out = Path(dest) if dest else TEMP_DIR / "{}{}".format(sub.sub_id, ext)
    try:
        out.write_bytes(sub_obj.content)
        return str(out)
    except Exception as e:
        log.error("subliminal: could not write file: %s", e); return None

# ─────────────────────────────────────────────────────────────────────────────
# OPENSUBTITLES.COM DIRECT ENGINE  (REST API v1 — no subliminal dependency)
# ─────────────────────────────────────────────────────────────────────────────

def _compute_moviehash(path: str) -> str:
    """Compute the OpenSubtitles movie hash for a local video file.

    Algorithm: filesize + sum of first 64 KB + sum of last 64 KB, where each
    sum accumulates 64-bit little-endian signed integers mod 2^64.
    Returns a 16-character lowercase hex string, or "" on any error or if the
    file is smaller than 128 KB (hash would be unreliable for tiny files).

    Pure stdlib — no third-party dependencies.
    """
    try:
        fsize = Path(path).stat().st_size
        # The OS.com hash reads the first 64 KB and the last 64 KB (chunk = 65536).
        # Files smaller than 2×chunk (131072 bytes) would have the two windows overlap,
        # producing a corrupt hash.  Skip hashing entirely for such files.
        if fsize < 131072:
            return ""
        chunk  = 65536       # 64 KB
        _hash  = fsize & 0xFFFFFFFFFFFFFFFF
        with open(path, "rb") as _f:
            # First 64 KB
            for _ in range(chunk // 8):
                word = _f.read(8)
                if len(word) < 8:
                    break
                # "<Q" (unsigned) is semantically correct per the OpenSubtitles hash spec.
                # "<q" (signed) produces identical output due to the 0xFFFF…FFFF mask,
                # but unsigned is the correct and more readable intent.
                _hash = (_hash + _struct.unpack("<Q", word)[0]) & 0xFFFFFFFFFFFFFFFF
            # Last 64 KB
            _f.seek(max(0, fsize - chunk))
            for _ in range(chunk // 8):
                word = _f.read(8)
                if len(word) < 8:
                    break
                # "<Q" (unsigned) is semantically correct per the OpenSubtitles hash spec.
                # "<q" (signed) produces identical output due to the 0xFFFF…FFFF mask,
                # but unsigned is the correct and more readable intent.
                _hash = (_hash + _struct.unpack("<Q", word)[0]) & 0xFFFFFFFFFFFFFFFF
        return "{:016x}".format(_hash)
    except Exception as _e:
        log.debug("_compute_moviehash(%r): %s", path, _e)
        return ""


def search_with_opensubtitlescom(query: str, lang_code, video_path: str = "",
                                 release_hint: str = "") -> list:
    """Search OpenSubtitles.com REST API v1 directly — no subliminal required.

    lang_code may be a single ISO-639-1 string OR a list of them.
    release_hint is the detected release name of the file being played
    (e.g. from the Content-Disposition header). When provided, results whose
    release field matches it closely get a scoring bonus — a subtitle uploaded
    for the exact same release as your file is very likely to have correct sync.
    Returns a list of Sub objects with provider="opensubtitlescom_direct".

    Search strategy (layered for maximum result quality):
      1. If video_path is a local file, compute moviehash and send alongside
         the filename as query — this surfaces perfectly-synced results first.
      2. Always also send a plain title query with season/episode numbers so
         results exist even when no hash-matched subtitles are available.
      3. Query params are sorted alphabetically before encoding to avoid the
         OS.com Varnish layer returning 301 redirects that can strip params.

    Scoring (normalised to [0.0, 1.0]):
      Base 0.70 for all results.
      +0.10 if moviehash_match is True (perfect sync).
      +0.08 if from_trusted uploader.
      +0.05 if not ai_translated and not machine_translated.
      Remainder from download_count (log-scaled, capped at +0.07).
    """
    api_key = _get_oscom_key()
    if not api_key:
        return []

    # Normalise lang_code to list of ISO-639-1 strings
    if isinstance(lang_code, str):
        lang_codes = [lang_code]
    else:
        lang_codes = list(lang_code)

    log.info("OS.com direct search  query=%r  langs=%s", query, lang_codes)

    # --- Build common headers -------------------------------------------
    jwt    = _get_oscom_jwt()   # may be "" if no credentials configured
    host   = _oscom_base_url    # may be vip-api.opensubtitles.com for VIP
    base   = "https://{}/api/v1/subtitles".format(host)
    hdrs   = {
        "Accept":     "application/json",
        "Api-Key":    api_key,
        "User-Agent": _UA_CHROME,
    }
    if jwt:
        hdrs["Authorization"] = "Bearer " + jwt

    # --- Parse season/episode from query ---------------------------------
    season, episode = parse_season_episode(query)
    # Strip release tags from the title, keeping only the show/movie name
    _title_raw = re.sub(r"[\s._-]*[Ss]\d{1,2}(?:[Ee][Pp]?\d{1,2}.*)?$", "", query).strip(" .-_")
    _title_raw = re.sub(r"[\s._-]*\d{1,2}[xX]\d{1,2}.*$", "", _title_raw).strip(" .-_")
    # Remove year from title if present (it's a separate API param)
    year_val = ""
    _ym = re.search(r"\b(19|20)\d{2}\b", _title_raw)
    if _ym:
        year_val = _ym.group(0)
        _title_raw = _title_raw[:_ym.start()].strip(" .-_()")

    content_type = "episode" if season is not None else "movie"

    # --- Compute moviehash if we have a local file -----------------------
    movie_hash = ""
    if video_path and Path(video_path).is_file():
        movie_hash = _compute_moviehash(video_path)
        if movie_hash:
            log.debug("OS.com direct: moviehash=%s", movie_hash)

    # --- Languages param: comma-separated, sorted alphabetically ---------
    # The API best-practice doc says to sort params AND sort language codes
    # alphabetically to optimise caching.
    langs_param = ",".join(sorted(lang_codes))

    # --- Helper: execute one GET and return parsed JSON ------------------
    def _do_search(params: dict) -> list:
        """Sort params alphabetically (OS.com caching requirement), fire GET."""
        sorted_params = sorted(params.items())
        url = base + "?" + urllib.parse.urlencode(sorted_params)
        log.debug("OS.com direct GET: %s",
                  re.sub(r"(api_key=)[^&]+", r"\1<redacted>", url))
        try:
            req = urllib.request.Request(url, headers=hdrs)
            with urllib.request.urlopen(req, timeout=20, context=_SSL_CTX) as r:
                return json.loads(r.read().decode("utf-8")).get("data", [])
        except urllib.error.HTTPError as _he:
            log.warning("OS.com direct search HTTP %s: %s", _he.code, _he.reason)
            return []
        except Exception as _e:
            log.warning("OS.com direct search error: %s", _e)
            return []

    # --- Fire searches ---------------------------------------------------
    raw_items: list = []
    seen_ids:  set  = set()

    def _merge(items):
        for it in items:
            _iid = it.get("id", "")
            if _iid and _iid not in seen_ids:
                seen_ids.add(_iid)
                raw_items.append(it)

    # Pass 1: hash search (local file only) — most precise
    if movie_hash:
        p1: dict = {"languages": langs_param, "moviehash": movie_hash}
        # Include filename as query alongside hash per API recommendation
        if _title_raw:
            p1["query"] = _title_raw.lower()
        _merge(_do_search(p1))

    # Pass 2: title + season/episode query — always run so we always have results
    p2: dict = {"languages": langs_param, "type": content_type}
    if _title_raw:
        p2["query"] = _title_raw.lower()
    if year_val:
        p2["year"] = year_val
    if season is not None:
        p2["season_number"] = str(season)
    if episode is not None:
        p2["episode_number"] = str(episode)
    _merge(_do_search(p2))

    log.info("OS.com direct: %d raw item(s) after dedup", len(raw_items))

    # --- Convert to Sub objects -----------------------------------------
    results = []
    for item in raw_items:
        attrs = item.get("attributes", {})
        files = attrs.get("files", [])
        if not files:
            continue
        file_id   = files[0].get("file_id", "")
        file_name = files[0].get("file_name", "") or ""
        if not file_id:
            continue

        lang_raw  = attrs.get("language", "") or ""
        # OS.com returns ISO-639-1 or ISO-639-2; normalise to the ISO-639-1 we
        # requested.  If the returned code matches one we asked for, use it;
        # otherwise fall back to the first requested language.
        result_lang = lang_raw if lang_raw in lang_codes else lang_codes[0]

        release       = attrs.get("release", "") or file_name or ""
        dl_count      = int(attrs.get("download_count", 0) or 0)
        new_dl_count  = int(attrs.get("new_download_count", 0) or 0)
        from_trusted  = bool(attrs.get("from_trusted", False))
        hash_match    = bool(attrs.get("moviehash_match", False))
        ai_translated = bool(attrs.get("ai_translated", False))
        mach_trans    = bool(attrs.get("machine_translated", False))
        votes         = int(attrs.get("votes", 0) or 0)
        ratings       = float(attrs.get("ratings", 0.0) or 0.0)
        uploader_rank = (attrs.get("uploader", {}) or {}).get("rank", "") or ""

        # ── Scoring ──────────────────────────────────────────────────────────
        # Built from verified signal meanings per OS API docs and forum staff:
        #
        # HARD DISQUALIFIERS (applied first):
        #   ai_translated or machine_translated → cap at 0.45.
        #   These are auto-generated and frequently poor quality.
        #
        # TIER 1 — Sync certainty (most important signal):
        #   hash_match=True means the subtitle was matched to this exact file's
        #   byte signature.  Sync is guaranteed.  Start at 0.93.
        #   hash_match=False → start at 0.72.  Everything else is a modifier.
        #
        # TIER 2 — Uploader trust (verified by OS forum staff):
        #   Only "Trusted Member", "Administrator", "Moderator", "Translator",
        #   and "Application Developers" actually signal quality.
        #   Silver/Gold/Platinum are upload-count badges — they mean nothing.
        #   from_trusted=True is the REST API's pre-computed version of this.
        #
        # TIER 3 — Community rating:
        #   ratings (0–10) is meaningful only when votes > 0.
        #   Ignored entirely when votes == 0 to avoid noise.
        #
        # TIER 4 — Popularity (tiebreaker only):
        #   download_count is a weak proxy for quality — a subtitle can have
        #   100k downloads and still be wrong for your file.  Dampened heavily.
        #   new_download_count (recent momentum) is a mild recency signal.

        uploader_trusted = from_trusted or (uploader_rank.lower() in _TRUSTED_RANKS)

        # Pre-normalise release_hint once per result for comparison.
        # Strip extension, lower-case, collapse all separators to spaces.
        _hint_norm = _norm_release_name(release_hint) if release_hint else ""

        if ai_translated or mach_trans:
            # Auto-translated — hard cap, always below human subtitles
            score = _SCORE_AI_TRANSLATED
        elif hash_match:
            # Exact file match — sync is confirmed, start high
            score = _SCORE_HASH_BASE
            if uploader_trusted:
                score = min(score + _SCORE_HASH_TRUSTED_BONUS, _SCORE_HASH_MAX)
            if votes > 0 and ratings >= 8.0:
                score = min(score + _SCORE_HASH_VOTE_BONUS, _SCORE_HASH_MAX)
        else:
            # No hash match — title/episode query result, sync not guaranteed
            score = _SCORE_QUERY_BASE
            if uploader_trusted:
                score = min(score + _SCORE_TRUSTED_BONUS, _SCORE_QUERY_CAP)
            if votes > 0:
                # ratings 0–10 → bonus 0–_SCORE_RATING_WEIGHT
                score = min(score + (ratings / 10.0) * _SCORE_RATING_WEIGHT, _SCORE_QUERY_CAP)
            # Popularity tiebreaker: log-dampened, capped at +_SCORE_POP_WEIGHT
            if dl_count > 0:
                import math as _math
                score = min(score + _SCORE_POP_WEIGHT * (_math.log10(dl_count + 1) / 6.0), _SCORE_QUERY_CAP)
            # Recent momentum: small bonus for newly popular subs
            if new_dl_count > 50:
                score = min(score + _SCORE_MOMENTUM_BONUS, _SCORE_QUERY_CAP)

        # TIER 5 — Release name match (applied after all other tiers, any path):
        #   If the subtitle's release name matches the actual file's release name
        #   (from Content-Disposition / filename detection), the subtitle was
        #   almost certainly made for this exact encode — strong sync signal.
        #   Two levels:
        #     exact  → full normalised string match          → +_SCORE_RELEASE_EXACT (capped _SCORE_RELEASE_EXACT_CAP)
        #     partial → hint is a substring of release or vice versa → +_SCORE_RELEASE_PARTIAL (capped _SCORE_QUERY_CAP)
        #   Intentionally capped below hash_match since we can't guarantee byte-level sync.
        release_match = False
        if _hint_norm and not (ai_translated or mach_trans):
            _rel_norm = _norm_release_name(release)
            if _hint_norm == _rel_norm:
                score = min(score + _SCORE_RELEASE_EXACT, _SCORE_RELEASE_EXACT_CAP)
                release_match = True
            elif _hint_norm in _rel_norm or _rel_norm in _hint_norm:
                score = min(score + _SCORE_RELEASE_PARTIAL, _SCORE_QUERY_CAP)
                release_match = True

        # Stable unique ID: provider + lang + subtitle_id
        subtitle_id = attrs.get("subtitle_id", "") or str(item.get("id", ""))
        _stable     = "oscom_direct_{}_{}_{}" .format(subtitle_id, result_lang, file_id)
        sub_id      = "oscom_" + hashlib.md5(_stable.encode("utf-8")).hexdigest()

        # Infer format from file_name extension
        fmt = ""
        _fn_lower = file_name.lower()
        for _ec in (".srt", ".ass", ".ssa", ".vtt", ".sub"):
            if _fn_lower.endswith(_ec):
                fmt = _ec.lstrip(".")
                break

        # Episode mismatch penalty: if the result carries an explicit episode tag
        # that doesn't match what was searched, apply a −0.25 penalty.
        # Season packs (no episode tag) and hash-matched results are left untouched.
        if episode is not None and not hash_match and _RE_EP_TAG.search(release):
            _ep_pen = False
            for _pat in _RE_SE_PATTERNS:
                _m = re.search(_pat, release)
                if _m:
                    try:
                        _res_sea = int(_m.group(1))
                        _res_ep  = int(_m.group(2))
                        if _res_ep != episode or (season is not None and _res_sea != season):
                            _ep_pen = True
                    except (IndexError, ValueError):
                        pass
                    break
            if _ep_pen:
                score = max(0.0, score - 0.25)
                log.debug("  OS.com ep-mismatch penalty: %r  searched=S%sE%s", release, season, episode)

        results.append(Sub(
            provider  = "opensubtitlescom_direct",
            language  = result_lang,
            release   = release,
            score     = score,
            downloads = dl_count,
            dl_url    = "",          # populated at download time via /download endpoint
            sub_id    = sub_id,
            fmt       = fmt,
            _sub_obj  = None,
            file_id   = str(file_id),
        ))
        log.debug(
            "  OS.com [%s] %r  lang=%s  score=%.3f  "
            "hash_match=%s  release_match=%s  trusted=%s  from_trusted=%s  uploader_rank=%r  "
            "dl=%d  new_dl=%d  votes=%d  ratings=%.1f  "
            "ai_trans=%s  mach_trans=%s",
            subtitle_id, release, result_lang, score,
            hash_match, release_match, uploader_trusted, from_trusted, uploader_rank,
            dl_count, new_dl_count, votes, ratings,
            ai_translated, mach_trans,
        )

    results.sort(key=lambda s: s.score, reverse=True)
    log.info("OS.com direct returned %d result(s)", len(results))
    return results


def download_with_opensubtitlescom(sub: "Sub", video_path: str = "",
                                   dest: str = None) -> "Optional[str]":
    """Download a subtitle via the OpenSubtitles.com /download endpoint.

    Flow:
      1. Check the cache index for a previously-stored direct CDN link
         ("direct_url:" + sub.sub_id) — avoids consuming quota on repeated loads.
      2. POST {"file_id": N} to /api/v1/download to get a signed CDN link.
         Both Api-Key and Authorization: Bearer JWT are sent when available.
      3. Download the file from the CDN link via download_binary().
      4. Store the CDN link in the cache index so step 1 succeeds next time.

    Quota handling:
      The /download endpoint returns HTTP 401 when the daily quota is exhausted,
      with a JSON body like {"message": "You have downloaded your allowed N
      subtitles for 24h..."}.  This is detected by message content inspection
      (not by HTTP code alone) and logged as a warning rather than an error so
      the caller can fall through to subliminal as a fallback.

    Returns the local file path on success, None on any failure.
    """
    api_key = _get_oscom_key()
    if not api_key:
        log.warning("OS.com download: no API key configured")
        return None

    file_id = getattr(sub, "file_id", "") or ""

    # --- Cache hit: reuse previously stored CDN link --------------------
    with _cache_index_lock:
        idx         = _load_cache_index(autosave=False)
        cached_link = idx.get("direct_url:" + sub.sub_id, "")

    if cached_link:
        # Support both old format (bare URL string) and new format (JSON with expiry).
        _resolved_link = ""
        try:
            _entry = json.loads(cached_link)
            if isinstance(_entry, dict):
                _expires = _entry.get("expires", 0)
                if _time_module.time() < _expires:
                    _resolved_link = _entry.get("link", "")
                else:
                    log.debug("OS.com download: cached CDN link expired — fetching fresh link")
            else:
                _resolved_link = str(_entry)  # unexpected dict type fallback
        except (json.JSONDecodeError, TypeError):
            # Old format: bare URL string
            _resolved_link = cached_link
        if _resolved_link:
            log.info("OS.com download (cached link): %r", sub.release)
            out = Path(dest) if dest else TEMP_DIR / "oscom_{}.srt".format(sub.sub_id)
            if download_binary(_resolved_link, out) and out.stat().st_size > 100:
                return str(out)
            log.debug("OS.com download: cached link stale — falling back to /download")

    # --- Need a file_id to call /download --------------------------------
    if not file_id:
        log.warning("OS.com download: no file_id for %r — cannot download", sub.release)
        return None

    # --- POST to /download endpoint --------------------------------------
    host    = _oscom_base_url
    url     = "https://{}/api/v1/download".format(host)
    jwt     = _get_oscom_jwt()
    headers = {
        "Content-Type": "application/json",
        "Accept":       "application/json",
        "Api-Key":      api_key,
        "User-Agent":   _UA_CHROME,
    }
    if jwt:
        headers["Authorization"] = "Bearer " + jwt

    payload = json.dumps({"file_id": int(file_id)}).encode("utf-8")

    try:
        req = urllib.request.Request(url, data=payload, headers=headers, method="POST")
        with urllib.request.urlopen(req, timeout=20, context=_SSL_CTX) as resp:
            resp_data = json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as he:
        # Read body to distinguish quota exhaustion from other auth errors
        err_body = ""
        try:
            err_body = he.read().decode("utf-8", errors="replace")
        except Exception:
            pass
        err_msg = ""
        try:
            err_msg = json.loads(err_body).get("message", "")
        except Exception:
            err_msg = err_body

        # Quota exhausted — the API returns 401 with a distinctive message
        if he.code == 401 and (
            "downloaded" in err_msg.lower() or
            "quota"      in err_msg.lower() or
            "allowed"    in err_msg.lower()
        ):
            log.warning("OS.com download: daily quota reached — %s", err_msg.strip())
            return None   # caller will fall through to subliminal

        log.warning("OS.com download HTTP %s: %s  body=%r", he.code, he.reason, err_msg[:200])
        return None
    except Exception as _e:
        log.warning("OS.com download request failed: %s", _e)
        return None

    cdn_link = resp_data.get("link", "")
    remaining = resp_data.get("remaining", "?")
    log.info("OS.com download: got CDN link for %r  remaining=%s", sub.release, remaining)

    if not cdn_link:
        log.warning("OS.com download: /download returned no link for %r", sub.release)
        return None

    # --- Fetch the actual subtitle file from CDN -------------------------
    # Determine output extension from the file_name in the /download response
    cdn_fname = resp_data.get("file_name", "") or ""
    ext = ".srt"
    _cfl = cdn_fname.lower()
    for _ec in (".srt", ".ass", ".ssa", ".vtt", ".sub"):
        if _cfl.endswith(_ec):
            ext = _ec
            break

    out = Path(dest) if dest else TEMP_DIR / "oscom_{}{}".format(sub.sub_id, ext)
    if not download_binary(cdn_link, out):
        log.warning("OS.com download: download_binary failed for %r", sub.release)
        return None
    if out.stat().st_size <= 100:
        log.warning("OS.com download: downloaded file too small (%d bytes) for %r",
                    out.stat().st_size, sub.release)
        out.unlink(missing_ok=True)
        return None

    # --- Cache the CDN link for future loads without consuming quota -----
    # OS.com CDN links are signed and typically valid for ~24 hours.
    # Store an expiry timestamp so the cache-hit path can skip stale links
    # instead of letting download_binary fail and consuming another quota unit.
    _cdn_ttl = 82800  # 23 hours — slightly under the 24h CDN TTL for safety margin
    with _cache_index_lock:
        idx2 = _load_cache_index(autosave=False)
        idx2["direct_url:" + sub.sub_id] = json.dumps({
            "link":    cdn_link,
            "expires": _time_module.time() + _cdn_ttl,
        })
        _save_cache_index(idx2)

    log.info("OS.com download complete: %s", out.name)
    return str(out)


# ─────────────────────────────────────────────────────────────────────────────
# SUBDL ENGINE
# ─────────────────────────────────────────────────────────────────────────────

# Module-level constant — avoid rebuilding on every search call.
_PROVIDER_DISPLAY = {
    "opensubtitles":          "OpenSub v2",
    "opensubtitlescom":       "OpenSub v3",
    "opensubtitlescom_direct": "OpenSub v3",
    "subdl":                  "SubDL",
}

def _provider_display(provider: str) -> str:
    return _PROVIDER_DISPLAY.get(provider.lower(), provider)

_SUBDL_CODES = {
    "ar":"AR","en":"EN","fr":"FR","es":"ES","de":"DE","it":"IT","pt":"PT","ru":"RU",
    "zh":"ZH","ja":"JA","ko":"KO","tr":"TR","he":"HE","nl":"NL","pl":"PL","sv":"SV",
    "no":"NO","da":"DA","fi":"FI","cs":"CS","hu":"HU","ro":"RO","bg":"BG","el":"EL",
    "hr":"HR","sr":"SR","uk":"UK","th":"TH","id":"ID","vi":"VI","fa":"FA","ms":"MS","ur":"UR",
}
_SUBDL_CODE_REV = {v: k for k, v in _SUBDL_CODES.items()}

def search_with_subdl(query, lang_code, video_path=""):
    """Search SubDL for subtitles.
    lang_code may be a single ISO-639-1 string OR a list of them.
    A single API call is made regardless of how many languages are requested.
    """
    api_key = _get_subdl_key()
    if not api_key: return []

    # Normalise to list
    if isinstance(lang_code, str):
        lang_codes = [lang_code]
    else:
        lang_codes = list(lang_code)

    log.info("SubDL search  query=%r  langs=%s", query, lang_codes)

    # Build comma-separated language param for the API (e.g. "EN,AR")
    lang_params = ",".join(
        _SUBDL_CODES.get(lc, lc.upper()) for lc in lang_codes
    )
    code_rev = _SUBDL_CODE_REV

    season, episode = parse_season_episode(query)

    # Handle season-only searches like "Reacher S03" where there's no episode number.
    # parse_season_episode needs both S and E, so check for a bare season tag manually.
    if season is None:
        _sm = re.search(r"(?<![Ee])[Ss](\d{1,2})(?!\s*[Ee]|\d)", query)
        if _sm:
            season = int(_sm.group(1))

    content_type = "tv" if season is not None else "movie"

    year_val = ""
    ym = re.search(r"\b(19|20)\d{2}\b", query)
    if ym:
        year_val = ym.group(0)
        film_name = query[:ym.start()].strip(" .-_()")
    else:
        film_name = query
    film_name = re.sub(r"[\s._-]*[Ss]\d{1,2}(?:[Ee][Pp]?\d{1,2}.*)?$", "", film_name).strip(" .-_")
    film_name = re.sub(r"[\s._-]*\d{1,2}[xX]\d{1,2}.*$", "", film_name).strip(" .-_")
    # NOTE: "Episode N" written-form (e.g. "Show.Episode.05") is not stripped here —
    # it's a rare edge case (mainly certain CJK/anime titles) and the SubDL API
    # handles partial-match queries reasonably well for those titles.

    params = {"api_key": api_key, "film_name": film_name, "type": content_type, "subs_per_page": "500"}
    if year_val: params["year"] = year_val
    if lang_params: params["languages"] = lang_params
    if season is not None: params["season_number"] = str(season)
    if episode is not None: params["episode_number"] = str(episode)

    url = "https://api.subdl.com/api/v1/subtitles?" + urllib.parse.urlencode(params)
    # Log the URL with the API key redacted to avoid exposing secrets in the log file.
    _safe_url = re.sub(r"(api_key=)[^&]+", r"\1<redacted>", url)
    log.debug("SubDL request URL: %s", _safe_url)
    try:
        req = urllib.request.Request(url, headers={"User-Agent": HTTP_HEADERS["User-Agent"], "Accept": "application/json"})
        with urllib.request.urlopen(req, timeout=20, context=_SSL_CTX) as resp:
            data = json.loads(resp.read().decode("utf-8"))
    except Exception as e:
        log.error("SubDL request failed: %s", e); return []

    if not data.get("status"):
        log.warning("SubDL API status=false: %s", data.get("message","")); return []

    subtitles = data.get("subtitles", [])
    log.info("SubDL raw results: %d", len(subtitles))
    results = []
    for item in subtitles:
        dl_url = item.get("download_link", "")
        if not dl_url:
            up = item.get("url","")
            dl_url = ("https://dl.subdl.com" + up) if up else ""
        if not dl_url: continue
        sub_name = item.get("release_name") or item.get("name") or ""
        slc = item.get("language","").upper()
        rlc = code_rev.get(slc, lang_codes[0])
        sd_id = str(item.get("sd_id") or item.get("id") or "")
        if not sd_id:
            sd_id = hashlib.md5("{}_{}_{}".format(sub_name, rlc, dl_url).encode("utf-8")).hexdigest()
        # For season packs, make the cache key episode-specific so a cached
        # extraction for ep5 is not reused when the same pack appears for ep6.
        if episode is not None and not re.search(
            r"[Ss]\d{1,2}[Ee][Pp]?\d{1,2}|\d{1,2}x\d{2}", sub_name
        ):
            sd_id = "{}_ep{}".format(sd_id, episode)
        downloads = int(item.get("downloads") or 0)
        # SubDL provides no uploader trust, ratings, or hash-match signals —
        # only download count.  A result with zero downloads is genuinely
        # unknown quality, same as OS.com anonymous zero-download results.
        # Base: 0.72 (no signals).  Downloads push toward 0.89 max.
        score_norm = min(0.72 + float(downloads) / 200000.0, 0.89) if downloads else 0.72
        fmt = ""
        _sn_lower = sub_name.lower()
        for ec in (".ass", ".ssa", ".vtt", ".sub", ".srt"):
            if _sn_lower.endswith(ec):
                fmt = ec.lstrip("."); break
        # Episode mismatch penalty: if the result carries an explicit episode tag
        # that doesn't match what was searched, apply a −0.25 penalty.
        # Season packs (no episode tag) are left untouched.
        if episode is not None and _RE_EP_TAG.search(sub_name):
            _ep_pen = False
            for _pat in _RE_SE_PATTERNS:
                _m = re.search(_pat, sub_name)
                if _m:
                    try:
                        _res_sea = int(_m.group(1))
                        _res_ep  = int(_m.group(2))
                        if _res_ep != episode or (season is not None and _res_sea != season):
                            _ep_pen = True
                    except (IndexError, ValueError):
                        pass
                    break
            if _ep_pen:
                score_norm = max(0.0, score_norm - 0.25)
                log.debug("  SubDL ep-mismatch penalty: %r  searched=S%sE%s", sub_name, season, episode)
        results.append(Sub(provider="subdl", language=rlc, release=sub_name,
                           score=score_norm, downloads=downloads, dl_url=dl_url,
                           sub_id="subdl_"+sd_id, fmt=fmt, _sub_obj=None, target_episode=episode))
        log.debug("  SubDL result: %r  lang=%s  dl=%s  score=%.3f", sub_name, slc, downloads, score_norm)
    results.sort(key=lambda s: s.score, reverse=True)
    log.info("SubDL returned %d results", len(results))
    return results

def _archive_dest_for(zip_key: str, ext: str = ".zip", label: str = "") -> Path:
    """Return the Path where the SubDL archive for *zip_key* lives (or should live).
    ext should be '.zip' or '.rar'.
    If label is provided it is prepended to the filename for human readability;
    the MD5 zip_key is always preserved so caching logic is unaffected.
    """
    if label:
        safe_label = re.sub(r'[\\/:*?"<>|]', "_", label).strip(" .")
        if safe_label:
            return TEMP_DIR / "{}_subdl_{}{}".format(safe_label, zip_key, ext)
    return TEMP_DIR / "subdl_{}{}".format(zip_key, ext)


def download_with_subdl(sub, dest=None):
    if not sub.dl_url: return None
    log.info("SubDL download: %r  url=%s", sub.release, sub.dl_url)

    # Use a dl_url-based key for the archive so the same season pack is not
    # re-downloaded for every episode (sub_id is now episode-specific for season packs).
    zip_key  = hashlib.md5(sub.dl_url.encode("utf-8")).hexdigest()
    # Check cache index to see if we already know this is a RAR
    pack_key = "pack:" + zip_key
    _cached_zip_ext = ".zip"
    try:
        _pack_raw = _load_cache_index().get(pack_key, "")
        if _pack_raw:
            _cached_zip_ext = json.loads(_pack_raw).get("zip_ext", ".zip")
    except Exception:
        pass
    zip_dest = _archive_dest_for(zip_key, _cached_zip_ext, label=sub.release)
    if not zip_dest.is_file() or zip_dest.stat().st_size < 10:
        # Download initially as .zip; we'll rename to .rar if needed after detection
        zip_dest = _archive_dest_for(zip_key, ".zip", label=sub.release)
        if not download_binary(sub.dl_url, zip_dest) or zip_dest.stat().st_size < 10:
            return None

    try:
        with zipfile.ZipFile(zip_dest, "r") as zf:
            sub_files = [n for n in zf.namelist()
                         if n.lower().endswith((".srt",".ass",".ssa",".vtt",".sub"))]
            if not sub_files:
                log.error("SubDL zip no subtitle files: %s", zf.namelist())
                return (_ARCHIVE_ONLY, str(zip_dest))

            def _fmtrank(f):
                return {".srt":0,".ass":1,".ssa":2,".vtt":3,".sub":4}.get(Path(f).suffix.lower(), 5)
            srt_files = sorted(sub_files, key=_fmtrank)
            chosen = None

            if len(srt_files) > 1:
                # Parse episode from release name, but only trust it if it looks
                # like a real episode tag (SxxExx / NxNN), not a bare NNN hit.
                _ep_from_release = None
                _sea_from_release = None
                for _pat in [
                    r"[Ss](\d{1,2})[.\-_ ]?[Ee][Pp]?(\d{1,2})(?!\d)",
                    r"(?<!\d)(\d{1,2})[xX](\d{2})(?!\d)",
                ]:
                    _m = re.search(_pat, sub.release)
                    if _m:
                        _sea_from_release = int(_m.group(1))
                        _ep_from_release  = int(_m.group(2))
                        break
                # Trust the explicit episode tag from the release name if found;
                # otherwise fall back to the target_episode stored at search time.
                if _ep_from_release is not None:
                    season, episode = _sea_from_release, _ep_from_release
                elif sub.target_episode is not None:
                    episode = sub.target_episode
                    s_match = re.search(r"\b(?:[Ss]eason\s*|[Ss])(\d{1,2})(?!\d)", sub.release, re.I)
                    season = int(s_match.group(1)) if s_match else None
                else:
                    season, episode = None, None
                log.warning("SubDL zip %d files — season pack. Target ep: %s", len(srt_files), episode)

                if episode is not None:
                    sp = r"\d{1,2}" if season is None else r"0*{}".format(season)
                    ep_str = r"0*{}".format(episode)

                    # ── Score +3: unambiguous episode tag patterns ──────────────
                    # Standard SxxExx / SxxEPxx (with optional separators)
                    ep_re  = re.compile(r"[Ss]{}[.\-_ ]?[Ee][Pp]?{}(?!\d)".format(sp, ep_str), re.I)
                    # NxNN format (1x05, 01x05, 1×05 unicode ×) — season part uses 0* padding
                    nx_re  = re.compile(r"(?<!\d){}[xX\u00d7]{}(?!\d)".format(
                        r"0*{}".format(season) if season is not None else r"\d{1,2}", ep_str), re.I)
                    # Ep01 / EP05 prefix style (e.g. Ep01_Ar_ar, EP05.srt)
                    ep_prefix_re = re.compile(r"(?<![A-Za-z])[Ee][Pp]{}(?!\d)".format(ep_str), re.I)
                    # Multi-episode range end: S01E01-E03 / S01E01E03 — target is end ep
                    multi_ep_re = re.compile(
                        r"[Ss]{sp}[.\-_ ]?[Ee][Pp]?\d{{1,2}}[.\-_ ]?(?:[Ee][Pp]?)?{ep}(?!\d)".format(
                            sp=sp, ep=ep_str), re.I)
                    # Written-out: "Episode 5" or "Episode.05" in filename
                    written_re = re.compile(r"[Ee]pisode[.\s_-]*{}(?!\d)".format(ep_str), re.I)
                    # E.01 / e_01 / E-01 separator variants
                    e_sep_re = re.compile(r"(?<![A-Za-z])[Ee][.\-_]{}(?!\d)".format(ep_str), re.I)
                    # Part/Pt style: Part.1, Pt01, Part_01 (only for low episode numbers ≤ 4)
                    part_re = re.compile(r"[Pp](?:ar)?t[.\-_ ]?{}(?!\d)".format(ep_str), re.I) if episode <= 4 else None

                    # ── Score +2: moderately reliable patterns ──────────────────
                    # Anime bracket style: [01] or #01 at word boundary
                    anime_bracket_re = re.compile(r"[\[\(#]0*{}[\]\)]".format(episode))
                    # Anime dash style: "Series - 05 -" or "Series - 05 [CRC]" or "- 05."
                    anime_dash_re = re.compile(r"(?<![A-Za-z\d])-[.\s]*{}[.\s]*(?:-|\[|\.|$)".format(ep_str))
                    # Underscore-bounded: _01_ or _01. or .01_ (common in anime/fansub packs)
                    us_bound_re = re.compile(r"(?<![A-Za-z\d_]){}(?![A-Za-z\d])".format(ep_str))
                    # Bare SNN (no E prefix, just season+episode concatenated e.g. "308" = S03E08)
                    bare_re = re.compile(r"(?<!\d){}{}(?!\d)".format(
                        season if season is not None else r"[1-9]", ep_str)) if season is not None else None

                    # ── Exclusion: file has a DIFFERENT explicit episode tag ────
                    # If a file contains SxxEyy / NxNN where yy ≠ target episode,
                    # it should be strongly penalised so it is never chosen.
                    # We match any explicit episode tag and check the captured number.
                    _excl_se_re  = re.compile(r"[Ss]\d{1,2}[.\-_ ]?[Ee][Pp]?(\d{1,3})(?!\d)", re.I)
                    _excl_nx_re  = re.compile(r"(?<!\d)\d{1,2}[xX\u00d7](\d{1,3})(?!\d)", re.I)
                    _excl_epx_re = re.compile(r"(?<![A-Za-z])[Ee][Pp](\d{1,3})(?!\d)", re.I)

                    def _has_wrong_ep(stem):
                        """Return True if the stem has an explicit episode tag for a DIFFERENT episode.
                        Multi-episode ranges (S01E01E05) are excluded from penalty — they may cover
                        the target episode even if the first number differs."""
                        for pat in (_excl_se_re, _excl_nx_re, _excl_epx_re):
                            for m in pat.finditer(stem):
                                found_ep = int(m.group(1))
                                if found_ep != episode:
                                    # Skip if immediately followed by another episode tag
                                    # (multi-ep range: S01E01E05 / S01E01-E05)
                                    tail = stem[m.end():]
                                    if re.match(r"[.\-_ ]?[Ee][Pp]?\d", tail):
                                        continue
                                    return True
                        return False

                    def _ms(fname):
                        stem = Path(fname).stem
                        # Hard exclusion: explicit episode tag for a different episode
                        if _has_wrong_ep(stem):
                            return -10
                        # Score 3: unambiguous episode tag matches target
                        if (ep_re.search(stem) or nx_re.search(stem)
                                or ep_prefix_re.search(stem) or multi_ep_re.search(stem)
                                or written_re.search(stem) or e_sep_re.search(stem)
                                or (part_re and part_re.search(stem))):
                            return 3
                        # Score 2: moderately reliable match
                        if anime_bracket_re.search(stem) or anime_dash_re.search(stem):
                            return 2
                        if bare_re and bare_re.search(stem):
                            return 2
                        # Score 1: last-resort heuristic — isolated digit match (e.g. bare "5" in stem).
                        # Not reliable on its own; used only when no stronger pattern matched.
                        # srt_files[0] is the fallback when best_score stays 0 regardless.
                        if us_bound_re.search(stem):
                            return 1
                        return 0

                    best = max(srt_files, key=lambda f: _ms(f)*10 + (1 if f.lower().endswith(".srt") else 0))
                    best_score = _ms(best)
                    if best_score >= 2:
                        chosen = best
                        log.info("Season pack: selected %r for episode %d (score=%d)", chosen, episode, best_score)
                    elif best_score == 1:
                        chosen = best
                        log.warning("Season pack: weak match %r for episode %d (score=1)", chosen, episode)
                    else:
                        log.warning("Season pack: no confident match for ep %d — falling back to first", episode)

            if chosen is None:
                chosen = srt_files[0]
                if len(srt_files) > 1:
                    log.warning("Season pack fallback: using %r", chosen)

            ext = Path(chosen).suffix or ".srt"
            if dest:
                out = Path(dest)
            else:
                # Use the actual filename from inside the zip (stem only, sanitized)
                chosen_stem = Path(chosen).stem
                # Sanitize: remove characters invalid on Windows/Linux filesystems
                safe_stem = re.sub(r'[\\/:*?"<>|]', "_", chosen_stem).strip(" .")
                if not safe_stem:
                    safe_stem = "{}_extracted".format(sub.sub_id)
                # Avoid collisions: if a file with the same name already exists in TEMP_DIR, append a counter
                out = TEMP_DIR / "{}{}".format(safe_stem, ext)
                _counter = 1
                while out.exists():
                    out = TEMP_DIR / "{}_{}{}".format(safe_stem, _counter, ext)
                    _counter += 1
            _member_info = zf.getinfo(chosen)
            if _member_info.file_size > 50 * 1024 * 1024:  # 50 MB hard limit — no subtitle is this large
                log.error(
                    "SubDL zip: member %r uncompressed size %d bytes exceeds 50 MB limit — aborting",
                    chosen, _member_info.file_size,
                )
                return None
            data = zf.read(chosen)
            out.write_bytes(data)
            log.info("SubDL extracted %d bytes → %s", len(data), out.name)

        # If the zip had only one subtitle, it's not a season pack — delete it.
        if len(srt_files) == 1:
            try:
                zip_dest.unlink(missing_ok=True)
                log.info("Single-file zip deleted after extraction: %s", zip_dest.name)
            except Exception as _e:
                log.warning("Could not delete single-file zip %s: %s", zip_dest.name, _e)

        return str(out)

    except zipfile.BadZipFile:
        # Check if it's a RAR archive (magic: Rar!\x1a\x07)
        try:
            with open(zip_dest, "rb") as _f:
                _magic = _f.read(6)
        except Exception:
            _magic = b""
        if _magic[:4] == b"Rar!":
            # Rename the downloaded file from .zip to .rar so it's stored correctly
            rar_dest = _archive_dest_for(zip_key, ".rar", label=sub.release)
            try:
                if rar_dest.exists():
                    # Only reuse the cached .rar if it is intact (≥ 10 bytes).
                    # A zero-byte or truncated file (e.g. from a prior interrupted
                    # download) would cause every future attempt to fail silently
                    # because the fresh download is discarded in its favour.
                    try:
                        _rar_cached_size = rar_dest.stat().st_size
                    except Exception:
                        _rar_cached_size = 0
                    if _rar_cached_size >= 10:
                        zip_dest.unlink(missing_ok=True)  # remove redundant .zip download
                        zip_dest = rar_dest
                        log.info("Re-using existing .rar archive: %s", zip_dest.name)
                    else:
                        # Corrupt cached .rar — overwrite it with the fresh download
                        # so the user is not permanently stuck.
                        try:
                            zip_dest.rename(rar_dest)
                        except OSError:
                            shutil.copy2(zip_dest, rar_dest)
                            zip_dest.unlink(missing_ok=True)
                        zip_dest = rar_dest
                        log.warning("Replaced corrupt cached .rar (%d bytes) with fresh "
                                    "download: %s", _rar_cached_size, zip_dest.name)
                else:
                    zip_dest.rename(rar_dest)
                    zip_dest = rar_dest
                    log.info("Renamed downloaded archive to .rar: %s", zip_dest.name)
            except Exception as _ren_e:
                log.warning("Could not rename to .rar: %s", _ren_e)
                # zip_dest stays as-is; extraction will still be attempted

            _rar_exe, _rar_kind = _find_rar_tool()

            def _pick_best_rar_sub(_extracted, _sub=sub):
                """Given a list of extracted subtitle Paths, return the best one."""
                _fmt_rank = {'.srt':0,'.ass':1,'.ssa':2,'.vtt':3,'.sub':4}
                _rar_episode = _sub.target_episode
                if _rar_episode is not None:
                    _sm2 = re.search(r"\b(?:[Ss]eason\s*|[Ss])(\d{1,2})(?!\d)", _sub.release, re.I)
                    _rar_season  = int(_sm2.group(1)) if _sm2 else None
                    _sp2 = r"\d{1,2}" if _rar_season is None else r"0*{}".format(_rar_season)
                    _rar_ep_re      = re.compile(r"[Ss]{}[.\-_ ]?[Ee][Pp]?0*{}(?!\d)".format(_sp2, _rar_episode), re.I)
                    _rar_nx_re      = re.compile(r"(?<!\d){}[xX]0*{}(?!\d)".format(
                                          r"0*{}".format(_rar_season) if _rar_season is not None else r"\d{1,2}", _rar_episode), re.I)
                    _rar_bare_re    = re.compile(r"(?<!\d){}0*{}(?!\d)".format(_rar_season, _rar_episode)) if _rar_season is not None else None
                    _rar_prefix_re  = re.compile(r"(?<![A-Za-z])[Ee][Pp]0*{}(?!\d)".format(_rar_episode), re.I)
                    _rar_anime_re   = re.compile(r"(?<![A-Za-z\d])-[.\s]*0*{}[.\s]*(?:-|\[|$)".format(_rar_episode))
                    _rar_multi_re   = re.compile(r"[Ss]{sp}[.\-_ ]?[Ee][Pp]?\d{{1,2}}[.\-_ ]?[Ee]?0*{ep}(?!\d)".format(sp=_sp2, ep=_rar_episode), re.I)
                    _rar_written_re = re.compile(r"[Ee]pisode[.\s_-]*0*{}(?!\d)".format(_rar_episode), re.I)

                    def _rar_ms(p):
                        s = p.stem
                        if (_rar_ep_re.search(s) or _rar_nx_re.search(s)
                                or _rar_prefix_re.search(s) or _rar_multi_re.search(s)
                                or _rar_written_re.search(s)):
                            return 3
                        if _rar_anime_re.search(s): return 2
                        if _rar_bare_re and _rar_bare_re.search(s): return 2
                        if re.search(r"(?<!\d)0*{}(?!\d)".format(_rar_episode), s): return 1
                        return 0

                    _best = max(_extracted, key=lambda f: _rar_ms(f)*10 + _fmt_rank.get(f.suffix.lower(), 5) * -1)
                    if _rar_ms(_best) < 2:
                        log.warning("RAR season pack: no confident ep match for ep %s — using first", _rar_episode)
                        _best = sorted(_extracted, key=lambda f: _fmt_rank.get(f.suffix.lower(), 5))[0]
                    else:
                        log.info("RAR season pack: selected %r for episode %s (score %d)", _best.name, _rar_episode, _rar_ms(_best))
                else:
                    _best = sorted(_extracted, key=lambda f: _fmt_rank.get(f.suffix.lower(), 5))[0]
                return _best

            def _finalise_rar(_extracted, _zip_dest=zip_dest):
                """Copy best subtitle out of temp dir, clean up single-file RARs, return path."""
                _best = _pick_best_rar_sub(_extracted)
                out_rar = TEMP_DIR / "{}_direct{}".format(sub.sub_id, _best.suffix)
                shutil.copy2(_best, out_rar)
                log.info("RAR extracted %r → %s", _best.name, out_rar.name)
                if len(_extracted) == 1:
                    try:
                        _zip_dest.unlink(missing_ok=True)
                        log.info("Single-file RAR deleted after extraction: %s", _zip_dest.name)
                    except Exception as _e:
                        log.warning("Could not delete single-file RAR %s: %s", _zip_dest.name, _e)
                return str(out_rar)

            if _rar_exe:
                with tempfile.TemporaryDirectory() as _td:
                    try:
                        if _rar_kind == "7zip":
                            _cmd = [_rar_exe, "e", str(zip_dest), "-o" + _td, "-y"]
                        elif _rar_kind == "bsdtar":
                            _cmd = [_rar_exe, "-x", "-f", str(zip_dest), "-C", _td]
                        else:  # winrar: UnRAR.exe / Rar.exe
                            _cmd = [_rar_exe, "e", "-y", str(zip_dest), _td]
                        subprocess.run(_cmd, capture_output=True, timeout=15, check=True)
                        _extracted = [Path(_td) / f for f in os.listdir(_td)
                                      if Path(f).suffix.lower() in _SUB_EXTENSIONS]
                        if _extracted:
                            return _finalise_rar(_extracted)
                    except Exception as _rar_e:
                        log.warning("RAR extraction via %s failed: %s", _rar_kind, _rar_e)

            log.error("RAR extraction failed — install WinRAR or 7-Zip to handle .rar files: %s", zip_dest.name)
            return None
        # Not a RAR — genuine bad zip, nothing we can do
        log.error("SubDL: not a valid zip or rar file: %s", zip_dest.name)
        return None
    except Exception as e:
        log.error("SubDL zip extraction error: %s\n%s", e, traceback.format_exc()); return None

# ─────────────────────────────────────────────────────────────────────────────
# MPV INTEGRATION
# ─────────────────────────────────────────────────────────────────────────────

# Pre-compute Unix domain socket default paths at import time.
# XDG_RUNTIME_DIR doesn't change during a session, so computing this once is safe
# and avoids 6 str.format() calls + a list concatenation on every _ipc_command call.
_xdg_runtime_dir = os.environ.get("XDG_RUNTIME_DIR", "")
_UNIX_IPC_DEFAULTS: list = [
    "/tmp/mpv-socket", "/tmp/mpvsocket", "/tmp/mpv-ipc",
    "/run/user/{}/mpv-socket".format(os.getuid() if hasattr(os, "getuid") else 0),
]
if _xdg_runtime_dir:
    _UNIX_IPC_DEFAULTS = [
        "{}/mpv-socket".format(_xdg_runtime_dir),
        "{}/mpvsocket".format(_xdg_runtime_dir),
    ] + _UNIX_IPC_DEFAULTS

def _parse_ipc_response(data: bytes):
    """Parse an mpv IPC response buffer that may contain leading event lines.

    mpv sends unsolicited event objects ({"event": "..."}) on the same pipe/socket
    before delivering the actual command response.  Iterating newline-delimited
    JSON objects and returning the first non-event dict prevents json.loads from
    silently parsing a stale event line instead of the real response (skip
    unsolicited mpv event objects).
    """
    for raw_line in data.split(b"\n"):
        raw_line = raw_line.strip()
        if not raw_line:
            continue
        try:
            obj = json.loads(raw_line.decode("utf-8"))
            if isinstance(obj, dict) and "event" not in obj:
                return obj
        except Exception:
            continue
    return None


def _ipc_command(command, pipes=None):
    """Send a JSON IPC command to mpv and return the parsed response dict, or None.

    Works on both Windows (win32file named pipes) and Unix (socket domain files).
    Tries each pipe/socket path in turn and returns on the first successful response.

    Args:
        command: list, e.g. ["get_property", "path"] or ["sub-add", "/tmp/x.srt", "select"]
        pipes:   optional list of pipe/socket paths to try; defaults to MPV_IPC_PIPES
    """
    targets = pipes if pipes is not None else MPV_IPC_PIPES
    payload = (json.dumps({"command": command}) + "\n").encode("utf-8")

    if sys.platform == "win32":
        try:
            import win32file
        except ImportError:
            log.debug("_ipc_command: win32file not available (install pywin32)")
            return None
        for pipe in targets:
            h = None
            try:
                try:
                    h = win32file.CreateFile(pipe,
                                             win32file.GENERIC_READ | win32file.GENERIC_WRITE,
                                             0, None, win32file.OPEN_EXISTING, 0, None)
                    win32file.WriteFile(h, payload)
                    # mpv terminates every IPC response with '\n'.  Loop on ReadFile
                    # (4 KB chunks) until we see a newline, mirroring the UNIX socket
                    # path below.  A single 64 KB read silently truncates large responses
                    # (e.g. playlist property) and causes json.loads to raise (VUL-09).
                    # Hard cap at 256 KB: no legitimate mpv IPC response is that large,
                    # and a malformed/infinite response would otherwise loop forever.
                    _MAX_IPC_BYTES = 256 * 1024
                    chunks = []
                    _total = 0
                    while True:
                        _, chunk = win32file.ReadFile(h, 4096)
                        if not chunk:
                            break
                        chunks.append(chunk)
                        _total += len(chunk)
                        if b"\n" in chunk or _total >= _MAX_IPC_BYTES:
                            break
                    data = b"".join(chunks)
                finally:
                    if h is not None:
                        try: win32file.CloseHandle(h)
                        except Exception: pass
                return _parse_ipc_response(data)
            except Exception as e:
                log.debug("_ipc_command via %s: %s", pipe, e)
        return None
    else:
        # Unix domain socket (Linux / macOS)
        # Defensive guard: AF_UNIX is guaranteed on Linux/macOS but may be absent if
        # this branch is ever reached on a custom Python build or via a non-default
        # pipes= argument that bypasses the sys.platform check above.
        if not hasattr(_socket, "AF_UNIX"):
            log.warning("_ipc_command: AF_UNIX not available on this platform")
            return None
        # Default socket paths are pre-computed at module level in _UNIX_IPC_DEFAULTS
        # to avoid rebuilding the list on every call.
        unix_targets = targets if targets is not MPV_IPC_PIPES else _UNIX_IPC_DEFAULTS
        for sock_path in unix_targets:
            try:
                with _socket.socket(_socket.AF_UNIX, _socket.SOCK_STREAM) as s:
                    s.settimeout(2)
                    s.connect(sock_path)
                    s.sendall(payload)
                    # mpv terminates every IPC response with '\n'.  A single recv()
                    # may return a partial response if the OS splits the packet, so
                    # we accumulate chunks until we see a newline or the connection
                    # closes.  4 KB per chunk is enough for any realistic mpv reply.
                    chunks = []
                    while True:
                        chunk = s.recv(4096)
                        if not chunk:
                            break
                        chunks.append(chunk)
                        if b"\n" in chunk:
                            break
                    data = b"".join(chunks)
                return _parse_ipc_response(data)
            except Exception as e:
                log.debug("_ipc_command via %s: %s", sock_path, e)
        return None


def load_subtitle_into_mpv(path, title=None):
    # sub-add accepts: url [flag [title [lang]]]
    # Passing the human-readable title makes mpv's own track picker show the
    # same name as the SubFinder results list (Issue #1).
    cmd = ["sub-add", path, "select"]
    if title:
        cmd.append(title)
    resp = _ipc_command(cmd)
    if resp is not None:
        log.info("mpv IPC: sub-add succeeded")
        return True
    try:
        # Write a timestamp prefix so the JS poller can detect and ignore
        # stale trigger files left over from a previous mpv session.
        # The '|' delimiter is safe here because subtitle paths generated by
        # SubFinder are always in TEMP_DIR or alongside the video file — neither
        # of which ever contains a '|' character.
        ts = str(int(_time_module.time() * 1000))  # milliseconds
        content = "{}|{}".format(ts, path)
        # Atomic write: write to temp file then rename to prevent JS reading a
        # partial trigger file if the process is interrupted mid-write.
        _tmp = TRIGGER_FILE.with_suffix(".txt.tmp")
        _tmp.write_text(content, encoding="utf-8")
        _tmp.replace(TRIGGER_FILE)
        log.info("wrote subtitle trigger file: %s", TRIGGER_FILE)
        return True
    except Exception as e:
        log.error("trigger file write failed: %s", e)
    return False

def load_subtitle_into_mpv_secondary(path):
    # Step 1: snapshot existing subtitle track IDs
    tl_before = _ipc_command(["get_property", "track-list"])
    before_ids = set()
    if tl_before is not None:
        for t in (tl_before.get("data") or []):
            if t.get("type") == "sub":
                before_ids.add(t["id"])

    # Step 2: add the track without selecting it as primary
    resp = _ipc_command(["sub-add", path, "auto"])
    if resp is None:
        # IPC not available — fall back to trigger file
        try:
            ts = str(int(_time_module.time() * 1000))
            content = "{}|secondary|{}".format(ts, path)
            _tmp = TRIGGER_FILE.with_suffix(".txt.tmp")
            _tmp.write_text(content, encoding="utf-8")
            _tmp.replace(TRIGGER_FILE)
            log.info("wrote secondary subtitle trigger file: %s", TRIGGER_FILE)
            return True
        except Exception as e:
            log.error("trigger file write failed: %s", e)
        return False

    log.info("mpv IPC: sub-add (secondary) succeeded")

    # Step 3: find the new track ID — retry up to 5 times (mpv may still be
    # processing the sub-add when the very next IPC call arrives).
    new_id = None
    for attempt in range(5):
        if attempt > 0:
            _time_module.sleep(0.1)
        tl_after = _ipc_command(["get_property", "track-list"])
        if tl_after is not None:
            for t in (tl_after.get("data") or []):
                _tid = t.get("id")
                if t.get("type") == "sub" and _tid is not None and _tid not in before_ids:
                    new_id = _tid
                    break
        if new_id is not None:
            break

    if new_id is not None:
        set_resp = _ipc_command(["set_property", "secondary-sid", new_id])
        log.info("mpv IPC: secondary-sid set to %s (resp=%s)", new_id, set_resp)
    else:
        log.warning("mpv IPC: could not determine new sub track ID for secondary-sid")

    return True

def get_mpv_title():
    for prop in ("media-title", "metadata/title"):
        resp = _ipc_command(["get_property", prop])
        if resp is None:
            continue
        val = resp.get("data", "")
        # Reject titles that are raw URLs or JWT tokens — some streaming apps
        # set the media title to the full CDN URL instead of the filename.
        if (val and val != "?"
                and not _URL_SCHEME_RE.match(str(val))
                and "token=" not in str(val)
                and len(str(val)) <= 300):
            return str(val)
        # Only sleep between iterations, not after the last one — avoids a
        # needless 50 ms block on the main thread when both props are exhausted.
        if prop != "metadata/title":
            _time_module.sleep(0.05)
    return ""
def get_filename_from_headers(url):
    try:
        req = urllib.request.Request(url, method="HEAD", headers=HTTP_HEADERS)
        with urllib.request.urlopen(req, timeout=5, context=_SSL_CTX) as r:
            cd = r.headers.get("Content-Disposition","")
            if cd:
                # Handles both plain filename= and RFC 5987 filename*=UTF-8''... forms.
                # Note: non-UTF-8 RFC 5987 charsets (e.g. ISO-8859-1'') are not decoded
                # correctly — unquote() assumes UTF-8. This is acceptable for subtitle
                # servers which overwhelmingly use UTF-8 or plain ASCII filenames.
                m = re.search(r'filename\*?=["\']?(?:UTF-8\'\')?([^"\';\s]+)', cd, re.I)
                if m:
                    return urllib.parse.unquote(m.group(1).strip('"\''))
    except Exception:
        pass
    return ""

def get_playing_video():
    def _is_local_file(p: str) -> bool:
        """Safe is_file() guard — Path(url).is_file() raises OSError on Windows for rtsp:// etc."""
        try:
            return Path(p).is_file()
        except OSError:
            return False

    for arg in sys.argv[1:]:
        if arg not in ("--test",) and (_URL_SCHEME_RE.match(arg) or _is_local_file(arg)):
            log.info("video from CLI arg: %s", arg); return arg
    resp = _ipc_command(["get_property", "path"])
    if resp is not None:
        path = resp.get("data", "")
        if path and (_URL_SCHEME_RE.match(path) or _is_local_file(path)):
            log.info("mpv IPC get_property path: %s", path)
            return path
    wl = SCRIPT_DIR.parent.parent / "watch_later"
    if wl.is_dir():
        try:
            for f in sorted(wl.iterdir(), key=lambda p: p.stat().st_mtime, reverse=True)[:5]:
                # Guard: skip absurdly large files (e.g. corrupted entries) to
                # prevent reading megabytes of garbage into memory.
                try:
                    if f.stat().st_size > 64 * 1024:   # 64 KB is far more than any watch_later entry
                        log.debug("watch_later: skipping oversized file %s", f.name)
                        continue
                except OSError:
                    continue
                content = f.read_text(encoding="utf-8", errors="ignore")
                m = re.search(r"^# ([^\n]+)", content, re.M)
                if m:
                    c = m.group(1).strip()
                    if _URL_SCHEME_RE.match(c):
                        log.info("video from watch_later (URL): %s", c)
                        return c
                    if Path(c).is_file():
                        log.info("video from watch_later (file): %s", c)
                        return c
                    log.debug("watch_later entry no longer exists, skipping: %s", c)
        except Exception: pass
    return ""
# ─────────────────────────────────────────────────────────────────────────────
# SEASON PACK CACHE LOOKUP
# ─────────────────────────────────────────────────────────────────────────────

def find_cached_season_packs(video_path: str) -> list:
    """
    Look at the cache index for season packs already downloaded and check whether
    any of them cover the season/episode of *video_path*.  Returns a list of Sub
    objects (one per matching pack) with target_episode set to the current episode,
    ready to be dropped straight into the results list without any API call.
    """
    if not video_path:
        return []

    # Figure out what season/episode the current video is
    # For URLs, extract the filename from the &filename= parameter if present,
    # otherwise fall back to the last path segment.
    if _URL_SCHEME_RE.match(video_path):
        _fn = re.search(r"[?&]filename=([^&]+)", video_path)
        if _fn:
            name = Path(urllib.parse.unquote(_fn.group(1))).stem
        else:
            name = Path(video_path.split("?")[0].rstrip("/").split("/")[-1]).stem
    else:
        name = Path(video_path).stem

    season, episode = parse_season_episode(name)
    if season is None or episode is None:
        log.debug("season pack cache: could not parse S/E from %r", name)
        return []

    _m = re.search(r"[Ss]\d{1,2}[Ee][Pp]?\d{1,2}|\d{1,2}[xX]\d{2}", name)
    # If _m is None, the season/episode was found via the bare-NNN fallback
    # (e.g. "105" → S01E05).  We still build current_show from the full name
    # minus trailing digits so show-name filtering isn't silently skipped.
    if _m:
        current_show = re.sub(r"[._\-]+", " ", name[:_m.start()]).strip().lower()
    else:
        # Strip trailing digit cluster (the bare episode number) and normalise.
        current_show = re.sub(r"\s*\d+\s*$", "", re.sub(r"[._\-]+", " ", name)).strip().lower()
    # Strip trailing year tokens like "(2013)" or "2013" that appear in video
    # filenames but never in subtitle release names, so they don't break the
    # show-name comparison against cached season pack release strings.
    current_show = re.sub(r"\s*\(?\d{4}\)?\s*$", "", current_show).strip()

    with _cache_index_lock:
        idx = _load_cache_index(autosave=False)  # read-only lookup; no save needed
    results = []

    for key, raw_val in idx.items():
        if not key.startswith("pack:"):
            continue
        try:
            meta = json.loads(raw_val)
        except Exception:
            continue

        zip_key   = meta.get("zip_key", "")
        zip_ext   = meta.get("zip_ext", ".zip")
        dl_url    = meta.get("dl_url", "")
        release   = meta.get("release", "")
        language  = meta.get("language", "")
        fmt       = meta.get("fmt", "srt")
        downloads = int(meta.get("downloads", 0))

        if not zip_key or not dl_url:
            continue

        # The archive must still be on disk — if it's gone, re-download it silently.
        zip_dest = _archive_dest_for(zip_key, zip_ext, label=release)
        if not zip_dest.is_file() or zip_dest.stat().st_size < 10:
            log.info("season pack cache: archive missing for %r, re-downloading", release)
            # Re-download to the correct extension path
            api_key = _get_subdl_key()
            dl_url_with_key = dl_url
            if api_key and "subdl.com" in dl_url and "api_key" not in dl_url:
                sep = "&" if "?" in dl_url else "?"
                dl_url_with_key = "{}{}api_key={}".format(dl_url, sep, api_key)
            if not download_binary(dl_url_with_key, zip_dest) or zip_dest.stat().st_size < 10:
                log.warning("season pack cache: re-download failed for %r, skipping", release)
                continue
            log.info("season pack cache: re-download successful for %r", release)

        # The pack's release name must reference the same season.
        # Prefer an explicit bare-S tag (e.g. "S03" in "Luther.S03.HDTV.x264-FoV")
        # over parse_season_episode, which can be fooled by codec strings like x264
        # into returning a wrong season via the bare-NNN fallback (264 → S02E64).
        _sm_bare = re.search(r"[Ss](\d{1,2})(?![Ee\d])", release)
        if _sm_bare:
            pack_season = int(_sm_bare.group(1))
        else:
            pack_season, _ = parse_season_episode(release)
        if pack_season is None:
            # Cannot determine which season this pack belongs to — skip it rather
            # than letting it surface for any season.  This prevents packs with
            # ambiguous or missing season markers from matching unrelated episodes.
            log.debug("season pack cache: could not determine season for %r, skipping", release)
            continue
        if pack_season != season:
            log.debug("season pack cache: %r is season %s, current is %s — skip",
                      release, pack_season, season)
            continue

        if current_show:
            _pm = re.search(r"[Ss]\d{1,2}[Ee][Pp]?\d{1,2}|\d{1,2}[xX]\d{2}", release)
            # Normalize dots/dashes to spaces in both cases so 'the rookie' matches
            # 'The.Rookie.S06.Complete' (release names without a specific episode tag).
            pack_show = re.sub(r"[._\-]+", " ", release[:_pm.start()]).strip().lower() if _pm \
                        else re.sub(r"[._\-]+", " ", release).strip().lower()
            if current_show not in pack_show and pack_show not in current_show:
                log.debug("season pack cache: show name mismatch — %r vs %r, skip",
                          current_show, pack_show)
                continue

        # Reconstruct the exact sub_id that search_with_subdl would produce.
        # If base_sub_id was stored in pack metadata, use it directly (it already
        # has the "subdl_" prefix and the correct sd_id hash from the API).
        # Fall back to url-MD5 for old cache entries that predate this field.
        _base_sub_id = meta.get("base_sub_id", "")
        if _base_sub_id:
            ep_sub_id = "{}_ep{}".format(_base_sub_id, episode)
        else:
            base_id = hashlib.md5(dl_url.encode("utf-8")).hexdigest()
            ep_sub_id = "subdl_{}_ep{}".format(base_id, episode)

        score_norm = min(0.72 + float(downloads) / 200000.0, 0.89) if downloads else 0.72

        sub = Sub(
            provider="subdl",
            language=language,
            release=release,
            score=score_norm,
            downloads=downloads,
            dl_url=dl_url,
            sub_id=ep_sub_id,
            fmt=fmt,
            _sub_obj=None,
            target_episode=episode,
        )
        results.append(sub)
        log.info("season pack cache hit: %r covers S%02dE%02d", release, season, episode)

    return results


# ─────────────────────────────────────────────────────────────────────────────
# GUI DEFAULTS
# ─────────────────────────────────────────────────────────────────────────────

DEFAULT_W, DEFAULT_H = 754, 686

# ─────────────────────────────────────────────────────────────────────────────
# GUI
# ─────────────────────────────────────────────────────────────────────────────


# ─────────────────────────────────────────────────────────────────────────────
# TOOLTIP
# ─────────────────────────────────────────────────────────────────────────────

class _Tooltip:
    """Lightweight hover tooltip for any tkinter widget."""
    _DELAY = 600   # ms before tooltip appears
    _PAD   = 6     # padding inside the tooltip box

    def __init__(self, widget, text: str):
        self._widget  = widget
        self._text    = text
        self._id      = None   # after() handle
        self._win     = None   # Toplevel window
        widget.bind("<Enter>",  self._on_enter, add="+")
        widget.bind("<Leave>",  self._on_leave, add="+")
        widget.bind("<ButtonPress>", self._on_leave, add="+")

    def _on_enter(self, _event=None):
        self._cancel()
        self._id = self._widget.after(self._DELAY, self._show)

    def _on_leave(self, _event=None):
        self._cancel()
        self._hide()

    def _cancel(self):
        if self._id:
            self._widget.after_cancel(self._id)
            self._id = None

    def _show(self):
        if self._win:
            return
        x = self._widget.winfo_rootx() + self._widget.winfo_width() // 2
        y = self._widget.winfo_rooty() + self._widget.winfo_height() + 4
        self._win = win = tk.Toplevel(self._widget)
        win.overrideredirect(True)
        win.attributes("-topmost", True)
        bg  = C.get("card",    "#101828")
        fg  = C.get("text",    "#ccd6f6")
        bdr = C.get("accent",  "#4d9de0")
        outer = tk.Frame(win, bg=bdr, bd=1)
        outer.pack(fill="both", expand=True)
        tk.Label(outer, text=self._text, bg=bg, fg=fg,
                 font=(_FONT_UI, 9), padx=self._PAD, pady=self._PAD // 2,
                 relief="flat").pack()
        win.update_idletasks()
        tw = win.winfo_reqwidth()
        th = win.winfo_reqheight()
        # Keep tooltip on screen.  wm_maxsize() covers multi-monitor setups but
        # returns (0, 0) on many Linux WMs.  Fall back to winfo_vrootwidth/height
        # (virtual root = full multi-monitor span) before the primary-monitor-only
        # winfo_screenwidth/height — mirrors the same fallback used in _open_settings.
        _max_w, _max_h = win.wm_maxsize()
        if _max_w > 0:
            sx, sy = _max_w, _max_h
        else:
            try:
                sx = self._widget.winfo_vrootwidth()
                sy = self._widget.winfo_vrootheight()
            except Exception:
                sx = self._widget.winfo_screenwidth()
                sy = self._widget.winfo_screenheight()
        if x + tw > sx:
            x = sx - tw - 4
        # Keep tooltip on screen vertically: if it would go below the screen,
        # flip it above the widget instead.
        if y + th > sy:
            y = self._widget.winfo_rooty() - th - 4
        win.geometry("+{}+{}".format(x, y))

    def _hide(self):
        if self._win:
            self._win.destroy()
            self._win = None

class App(tk.Tk):

    # Single source of truth for column definitions.
    # Tuple: (col_id, settings_key, heading_text, default_width, anchor)
    # _build_ui and all column-order/visibility logic must read from this list —
    # never maintain a parallel inline list.
    COLUMNS = [
        ("score",    "col_score",    "Score",           62,  "center"),
        ("release",  "col_release",  "Release / Title", 350, "w"),
        ("language", "col_language", "Language",         90, "center"),
        ("provider", "col_provider", "Provider",        150, "center"),
        ("fmt",      "col_fmt",      "Fmt",              48, "center"),
    ]

    def __init__(self, video_path=""):
        super().__init__()
        self.video_path = video_path
        self.results: List[Sub] = []
        self.secondary_results: List[Sub] = []
        self._secondary_expanded = False
        self._search_job = None      # search thread (set by _start_search)
        self._translate_job = None   # translation thread (set by _translate_subtitle)
        self._stop_event = threading.Event()
        self._sync_procs: "set" = set()  # killable sync subprocesses (ffmpeg + sync tool)
        self._last_dl_path: dict = {}
        self._last_dl_path_lock = threading.Lock()  # guards compound read-modify-write on _last_dl_path
        self._mpv_primary_sub_id: str = ""   # sub_id of currently active primary subtitle
        self._mpv_secondary_sub_id: str = ""  # sub_id of currently active secondary subtitle
        self._mpv_primary_sids: dict = {}     # sub_id -> mpv sid for primary slot
        self._mpv_secondary_sids: dict = {}   # sub_id -> mpv sid for secondary slot
        self.detail_visible = False
        self._col_sort_state: dict = {}   # col_id → "desc"|"asc"|"none"
        self._active_sort_col:  str  = ""    # which col currently has an arrow shown
        self._sort_direction: str  = "desc"  # direction for the Sort-by dropdown
        # Single-instance window refs
        self._settings_win = None
        self._log_win = None
        self._help_win = None
        self._active_sort_key_fn = None      # last key_fn used by _populate_tree; None = use _sort_key
        self._pre_detail_h = 0
        self._pre_warn_h   = 0   # written by banner expand/collapse but never read back;
                                 # both paths use winfo_height() at the point of use
        # Set to True whenever download state or mpv sid changes — tells the fast
        # sort path that it must re-push tags before reordering.  Cleared after
        # each tag refresh so pure re-sorts skip the N tree.item() calls entirely.
        self._tree_tags_dirty   = False
        self._last_selected_iid = ""   # flash guard: skip btn_load.config when selection unchanged

        self._settings = {
            "auto_search": False, "close_on_dbl_click": False,
            "last_language": "English", "last_languages": ["English"], "row_height": 40, "font_size": 9,
            "oscom_api_key": "", "oscom_username": "", "oscom_password": "",
            "subdl_api_key": "", "gemini_api_key": "",
            "gemini_api_keys": [],
            "gemini_chunk_size": _GEMINI_CHUNK_SIZE,
            "gemini_key_warning_dismissed": False,
            "gemini_models": ["gemini-2.5-flash-lite", "gemini-2.5-flash", "gemini-2.5-pro"],
            # Providers default to False — user must set API keys and enable them in Settings.
            # This is intentional; enabling them without a key would only produce errors.
            # Note: provider_gemini_translate was removed; the Gemini key is the only gate.
            "provider_subliminal": False, "provider_subdl": False,
            "col_score": True, "col_release": True, "col_language": True,
            "col_provider": True, "col_fmt": True,
            "col_order": ["score","release","provider","language","fmt"],
            "col_widths": {"score":70,"release":384,"language":87,"provider":92,"fmt":73}, "theme": "Default",
            "free_resize": True, "save_position": True, "win_geometry": "",
            "log_win_geometry": "", "settings_win_geometry": "", "help_win_geometry": "",
            "oscom_popup_geometry": "", "gemini_popup_geometry": "",
            "subliminal_warn_dismissed": False,
            "ffsubsync_warn_dismissed": False,
            "pysubs2_warn_dismissed": False,
            "ffmpeg_warn_dismissed": False,
            "pywin32_warn_dismissed": False,
            "sort_var": "Score",
            "sort_col_state": {},
            "sort_active_col": "",
            "sort_direction": "desc",
        }
        self._settings_file = CONFIG_DIR / "subfinder_settings.json"
        self._load_settings()
        self._multi_lang_search = False   # set True when >1 language is searched
        # Column drag-reorder state
        self._col_drag_source: Optional[str] = None   # col id being dragged
        self._col_drag_active: bool = False            # True once drag threshold crossed
        self._col_drag_after: Optional[str] = None    # after() handle for drag timeout
        self._col_drag_press_x: int = 0               # x coord of initial press

        global C
        C = dict(THEMES.get(self._settings.get("theme","Default"), THEMES["Default"]))

        self._init_window()
        self._init_styles()
        self._build_ui()
        self.after(50, self._apply_settings_to_ui)
        self.after(120, self._on_start)

    # ── settings ──────────────────────────────────────────────────────────────

    def _load_settings(self):
        try:
            data = json.loads(self._settings_file.read_text(encoding="utf-8"))
            for k, v in data.items():
                if k not in self._settings:
                    log.debug(
                        "settings: unknown key %r (value %r) — "
                        "preserved in _extra for forward-compat (may be from a newer version)",
                        k, v,
                    )
                    # Accumulate unknown keys so they survive a downgrade-then-upgrade cycle.
                    self._settings.setdefault("_extra", {})[k] = v
                    continue
                default = self._settings[k]
                # Accept the value only when its type matches the built-in default.
                # This prevents a hand-edited "row_height": "40" (string) from
                # reaching Tkinter as a string and raising a Tcl error.
                # Special case: bool is a subclass of int in Python, so we must
                # check bool explicitly before int to avoid treating True/False as 1/0.
                if isinstance(default, bool):
                    if isinstance(v, bool):
                        self._settings[k] = v
                elif isinstance(default, int):
                    if isinstance(v, int) and not isinstance(v, bool):
                        self._settings[k] = v
                    elif isinstance(v, float) and v == int(v):
                        # json.loads("40.0") returns float — accept lossless floats for int fields
                        self._settings[k] = int(v)
                else:
                    # For list, dict, str, float: require exact type match.
                    # Uses 'is' (identity) rather than '==' to avoid triggering
                    # __eq__ on custom types and to make the intent explicit.
                    if type(v) is type(default):
                        self._settings[k] = v
        except Exception:
            pass

    def _save_settings(self):
        # Debounce: collapse rapid successive saves (e.g. checkbox toggles, spinbox changes)
        # into a single write 300ms after the last call.  This eliminates synchronous
        # JSON writes on the UI thread during interactive settings changes.
        if hasattr(self, "_save_settings_after_id") and self._save_settings_after_id:
            try:
                self.after_cancel(self._save_settings_after_id)
            except Exception:
                pass
        self._save_settings_after_id = self.after(300, self._flush_settings)

    def _flush_settings(self):
        """Actually write settings to disk. Called by the debounce timer."""
        self._save_settings_after_id = None
        # Persist current sort state before writing
        self._settings["sort_var"]        = self.sort_var.get() if hasattr(self, "sort_var") else "Score"
        self._settings["sort_col_state"]  = getattr(self, "_col_sort_state", {})
        self._settings["sort_active_col"] = getattr(self, "_active_sort_col", "")
        self._settings["sort_direction"]  = getattr(self, "_sort_direction", "desc")
        # Atomic write — same pattern as _save_cache_index.
        _tmp = self._settings_file.with_suffix(".tmp")
        try:
            # Merge _extra (forward-compat keys from newer versions) back to top level
            _out = {k: v for k, v in self._settings.items() if k != "_extra"}
            _out.update(self._settings.get("_extra", {}))
            _tmp.write_text(json.dumps(_out, indent=2), encoding="utf-8")
            _tmp.replace(self._settings_file)
        except Exception as e:
            log.warning("Could not save settings: %s", e)
            try:
                _tmp.unlink(missing_ok=True)
            except Exception:
                pass

    def _save_col_widths(self):
        widths = {}
        for cid, *_ in self.COLUMNS:
            try: widths[cid] = self.tree.column(cid, "width")
            except Exception: pass
        self._settings["col_widths"] = widths
        self._save_settings()

    def _apply_settings_to_ui(self):
        rh = self._settings.get("row_height", 40)
        fs = self._settings.get("font_size", 9)
        ttk.Style(self).configure("Treeview", rowheight=rh, font=(_FONT_UI, fs))
        col_map = {cid: (key, head, w) for cid, key, head, w, _anc in self.COLUMNS}
        order   = self._settings.get("col_order", [c for c,*_ in self.COLUMNS])
        order   = [c for c in order if c in col_map]
        order  += [c for c,*_ in self.COLUMNS if c not in order]
        widths  = self._settings.get("col_widths", {})
        visible = [c for c in order if self._settings.get(col_map[c][0], True)]
        self.tree.configure(displaycolumns=visible)
        active_col = getattr(self, "_active_sort_col", "")
        active_dir = self._col_sort_state.get(active_col, "none") if active_col else "none"
        arrow_map  = {"asc": " \u25b2", "desc": " \u25bc"}
        for cid in order:
            key, head, dw = col_map[cid]
            if self._settings.get(key, True):
                self.tree.column(cid, width=widths.get(cid, dw), minwidth=36)
                arrow = arrow_map.get(active_dir, "") if cid == active_col else ""
                self.tree.heading(cid, text=head + arrow)

    # ── window ─────────────────────────────────────────────────────────────────

    def _init_window(self):
        self.title("SubFinder")
        self.configure(bg=C["bg"])
        free = self._settings.get("free_resize", True)
        save_pos = self._settings.get("save_position", True)
        saved = self._settings.get("win_geometry", "")
        if saved and (free or save_pos):
            try: self.geometry(saved)
            except Exception: self.geometry("{}x{}".format(DEFAULT_W, DEFAULT_H))
        elif saved and not free:
            # Lock to last user-set size even if save_position is off
            try:
                m = _GEO_SIZE_RE.match(saved)
                if m:
                    self.geometry("{}x{}".format(m.group(1), m.group(2)))
                else:
                    self.geometry("{}x{}".format(DEFAULT_W, DEFAULT_H))
            except Exception:
                self.geometry("{}x{}".format(DEFAULT_W, DEFAULT_H))
        else:
            # First launch (no saved geometry) — center on screen
            self.update_idletasks()  # ensure winfo_screenwidth is accurate
            _sw = self.winfo_screenwidth()
            _sh = self.winfo_screenheight()
            _x = max(0, (_sw - DEFAULT_W) // 2)
            _y = max(0, (_sh - DEFAULT_H) // 2)
            self.geometry("{}x{}+{}+{}".format(DEFAULT_W, DEFAULT_H, _x, _y))
        self.resizable(True, True)
        if not free:
            # Lock: use last saved size as both min and max, preventing resize
            try:
                geo = self._settings.get("win_geometry", "")
                m = _GEO_SIZE_RE.match(geo) if geo else None
                lock_w = int(m.group(1)) if m else DEFAULT_W
                lock_h = int(m.group(2)) if m else DEFAULT_H
            except Exception:
                lock_w, lock_h = DEFAULT_W, DEFAULT_H
            self.resizable(False, False)
            self.minsize(lock_w, lock_h)
        self.protocol("WM_DELETE_WINDOW", self._on_close)

    def _apply_theme(self):
        global C
        old_C = dict(C)
        C = dict(THEMES.get(self._settings.get("theme","Default"), THEMES["Default"]))
        
        # 1. Update the main window background
        self.configure(bg=C["bg"])
        
        # 2. Update all TTK Styles
        self._init_styles()
        
        # 3. Recursively update all standard TK widgets (Labels, Frames, Text, etc.)
        bg_roles = ["bg", "surface", "card", "border", "hover", "sel_bg", "accent", "danger"]
        fg_roles = ["text", "dim", "accent", "border", "danger", "sel_fg"]

        def match_color(cur_hex, roles):
            if not cur_hex: return None
            cur_hex = str(cur_hex).lower()
            for role in roles:
                if old_C.get(role, "").lower() == cur_hex: return C[role]
            for role, hexval in old_C.items():
                if hexval.lower() == cur_hex: return C[role]
            return None

        def _refresh_widget(w):
            # The outer try/except catches any Tcl error from ttk internal child widgets
            # (heading bar, cell area) that don't support bg/fg configure.  ttk widgets
            # are re-themed by _init_styles() above, so this walk is redundant for them
            # but harmless — the exception is silently swallowed.
            try:
                keys = w.keys()
                if 'bg' in keys:
                    new_bg = match_color(w.cget('bg'), bg_roles)
                    if new_bg: w.configure(bg=new_bg)
                if 'fg' in keys:
                    new_fg = match_color(w.cget('fg'), fg_roles)
                    if new_fg: w.configure(fg=new_fg)
                if 'activebackground' in keys:
                    new_abg = match_color(w.cget('activebackground'), bg_roles)
                    if new_abg: w.configure(activebackground=new_abg)
                if 'activeforeground' in keys:
                    new_afg = match_color(w.cget('activeforeground'), fg_roles)
                    if new_afg: w.configure(activeforeground=new_afg)
                if 'selectcolor' in keys:
                    new_sc = match_color(w.cget('selectcolor'), bg_roles)
                    if new_sc: w.configure(selectcolor=new_sc)
                if 'insertbackground' in keys:
                    new_ibg = match_color(w.cget('insertbackground'), fg_roles)
                    if new_ibg: w.configure(insertbackground=new_ibg)
                if 'highlightbackground' in keys:
                    new_hb = match_color(w.cget('highlightbackground'), bg_roles)
                    if new_hb: w.configure(highlightbackground=new_hb)

                # Special case: Canvas text items (Status bar)
                if isinstance(w, tk.Canvas):
                    for item in w.find_all():
                        if w.type(item) == "text":
                            new_fill = match_color(w.itemcget(item, "fill"), fg_roles)
                            if new_fill: w.itemconfigure(item, fill=new_fill)

                # Special case: Text widget internal tags (Fixes the Help window)
                if isinstance(w, tk.Text):
                    for tag in w.tag_names():
                        try:
                            tag_fg = w.tag_cget(tag, "foreground")
                            if tag_fg:
                                new_tag_fg = match_color(tag_fg, fg_roles)
                                if new_tag_fg: w.tag_configure(tag, foreground=new_tag_fg)
                            
                            tag_bg = w.tag_cget(tag, "background")
                            if tag_bg:
                                new_tag_bg = match_color(tag_bg, bg_roles)
                                if new_tag_bg: w.tag_configure(tag, background=new_tag_bg)
                        except Exception:
                            pass

                for child in w.winfo_children():
                    _refresh_widget(child)
            except Exception:
                pass

        _refresh_widget(self)

        # 4. Also re-theme any open secondary Toplevel windows — they are NOT
        # in self's widget tree so _refresh_widget(self) above never reaches them.
        for _win_attr in ("_settings_win", "_log_win", "_help_win"):
            _win = getattr(self, _win_attr, None)
            if _win is not None:
                try:
                    if _win.winfo_exists():
                        _win.configure(bg=C["bg"])
                        _refresh_widget(_win)
                except Exception:
                    pass

        # 5. Refresh internal components
        self._configure_tags()
        self._apply_settings_to_ui()
        self._refresh_tree()

    def _init_styles(self):
        s = ttk.Style(self)
        s.theme_use("clam")
        base = dict(background=C["bg"], foreground=C["text"], fieldbackground=C["card"],
                    borderwidth=0, relief="flat", troughcolor=C["surface"],
                    selectbackground=C["sel_bg"], selectforeground=C["sel_fg"])
        s.configure(".", **base)
        s.configure("TFrame",    background=C["bg"])
        s.configure("TLabel",    background=C["bg"], foreground=C["text"], font=(_FONT_UI,10))
        s.configure("Dim.TLabel",background=C["bg"], foreground=C["dim"],  font=(_FONT_UI,9))
        s.configure("Head.TLabel",background=C["bg"],foreground=C["text"], font=(_FONT_UI,15,"bold"))
        # Pick white or black text on TButton based on accent luminance
        try:
            _a = C["accent"].lstrip("#")
            _r, _g, _b = int(_a[0:2],16), int(_a[2:4],16), int(_a[4:6],16)
            _lum = 0.299*_r + 0.587*_g + 0.114*_b
            _btn_fg = "#000000" if _lum > 140 else "#ffffff"
        except Exception:
            _btn_fg = "#ffffff"  # safe fallback: white text is readable on any accent color
        s.configure("TButton",   background=C["accent"], foreground=_btn_fg,
                    font=(_FONT_UI,10,"bold"), padding=(16,8), borderwidth=0, relief="flat")
        # Lighten the accent colour by ~20% for the hover state.
        # Near-white channels (>215) are darkened instead to avoid #ffffff on white bg.
        try:
            _a = C["accent"].lstrip("#")
            def _hover_channel(ch: int) -> int:
                return min(255, ch + 40)
            _btn_hover = "#{:02x}{:02x}{:02x}".format(
                _hover_channel(int(_a[0:2], 16)),
                _hover_channel(int(_a[2:4], 16)),
                _hover_channel(int(_a[4:6], 16)),
            )
        except Exception:
            _btn_hover = C["accent"]
        # Disabled state: compute readable foreground against the border bg
        try:
            _bd = C["border"].lstrip("#")
            _br, _bg2, _bb = int(_bd[0:2],16), int(_bd[2:4],16), int(_bd[4:6],16)
            _blum = 0.299*_br + 0.587*_bg2 + 0.114*_bb
            _dis_fg = "#000000" if _blum > 100 else "#aaaaaa"
        except Exception:
            _dis_fg = C["dim"]
        s.map("TButton", background=[("active", _btn_hover), ("disabled", C["border"])],
              foreground=[("active", _btn_fg), ("disabled", _dis_fg)])
        s.configure("Ghost.TButton", background=C["card"], foreground=C["text"],
                    font=(_FONT_UI,9), padding=(10,6), borderwidth=1, relief="flat")
        s.map("Ghost.TButton", background=[("active",C["hover"])], foreground=[("active",C["text"])])
        s.configure("Mini.TButton", background=C["card"], foreground=C["dim"],
                    font=(_FONT_UI,8), padding=(6,4), borderwidth=1, relief="flat")
        s.map("Mini.TButton", background=[("active",C["hover"])], foreground=[("active",C["text"])])
        s.configure("Small.TButton", background=C["card"], foreground=C["text"],
                    font=(_FONT_UI,10), padding=(2,2), borderwidth=1, relief="flat",
                    lightcolor=C["card"], darkcolor=C["card"], bordercolor=C["border"])
        s.map("Small.TButton", background=[("active",C["hover"])], foreground=[("active",C["text"])],
              lightcolor=[("active",C["hover"])], darkcolor=[("active",C["hover"])])
        # ConfigBtn.TButton — compact labelled gear button used for API settings rows
        s.configure("ConfigBtn.TButton", background=C["card"], foreground=C["dim"],
                    font=(_FONT_UI, 9), padding=(6, 4), borderwidth=1, relief="flat",
                    lightcolor=C["border"], darkcolor=C["border"], bordercolor=C["border"])
        s.map("ConfigBtn.TButton",
              background=[("active", C["hover"])],
              foreground=[("active", C["text"])],
              lightcolor=[("active", C["hover"])],
              darkcolor=[("active", C["hover"])])
        try:
            _d = C["danger"].lstrip("#")
            _dr, _dg, _db = int(_d[0:2],16), int(_d[2:4],16), int(_d[4:6],16)
            _dlum = 0.299*_dr + 0.587*_dg + 0.114*_db
            _warn_fg = "#000000" if _dlum > 140 else "#ffffff"
        except Exception:
            _warn_fg = C["bg"]
        try:
            _dh = C["danger"].lstrip("#")
            _dhr, _dhg, _dhb = int(_dh[0:2],16), int(_dh[2:4],16), int(_dh[4:6],16)
            _warn_dark = "#{:02x}{:02x}{:02x}".format(
                max(0, _dhr - 20), max(0, _dhg - 20), max(0, _dhb - 20))
            _warn_dim  = "#{:02x}{:02x}{:02x}".format(
                int(_dhr * 0.55), int(_dhg * 0.55), int(_dhb * 0.55))
        except Exception:
            _warn_dark = C["danger"]
            _warn_dim  = C["border"]
        s.configure("Warn.TButton", background=_warn_dark, foreground=_warn_fg,
                    font=(_FONT_UI,9,"bold"), padding=(10,6), borderwidth=0, relief="flat")
        s.map("Warn.TButton",
              background=[("disabled", _warn_dim), ("active", C["danger"])],
              foreground=[("disabled", _warn_fg),  ("active", _warn_fg)])
        # Stop.TButton — same as Warn.TButton but resting state is danger-10
        # (slightly brighter) instead of danger-20.  Applied only to btn_stop.
        try:
            _stop_rest = "#{:02x}{:02x}{:02x}".format(
                max(0, _dhr - 10), max(0, _dhg - 10), max(0, _dhb - 10))
        except Exception:
            _stop_rest = C["danger"]
        s.configure("Stop.TButton", background=_stop_rest, foreground=_warn_fg,
                    font=(_FONT_UI,9,"bold"), padding=(10,6), borderwidth=0, relief="flat")
        s.map("Stop.TButton",
              background=[("disabled", _warn_dim), ("active", C["danger"])],
              foreground=[("disabled", _warn_fg),  ("active", _warn_fg)])
        s.configure("Plus.TButton", background=C["accent"], foreground=_btn_fg,
                    font=(_FONT_UI,10,"bold"), padding=(2,2), borderwidth=0, relief="flat")
        s.map("Plus.TButton",
              background=[("disabled", C["border"]), ("active", _btn_hover)],
              foreground=[("disabled", _dis_fg),     ("active", _btn_fg)])
        # ── Icon-only button styles (Segoe MDL2 Assets on Windows, UI font fallback elsewhere) ──
        # Icon.TButton — neutral ghost icon (drag handle, etc.)
        s.configure("Icon.TButton", background=C["surface"], foreground=C["dim"],
                    font=(_FONT_ICON, 11), padding=(3, 3),
                    borderwidth=0, relief="flat")
        s.map("Icon.TButton",
              background=[("active", C["hover"])],
              foreground=[("active", C["text"])])
        # IconAccent.TButton — accent-coloured icon (add)
        s.configure("IconAccent.TButton", background=C["surface"], foreground=C["accent"],
                    font=(_FONT_ICON, 11), padding=(3, 3),
                    borderwidth=0, relief="flat")
        s.map("IconAccent.TButton",
              background=[("active", C["hover"])],
              foreground=[("active", _btn_hover)])
        # IconDanger.TButton — danger icon (delete/remove)
        s.configure("IconDanger.TButton", background=C["surface"], foreground=C["dim"],
                    font=(_FONT_ICON, 11), padding=(3, 3),
                    borderwidth=0, relief="flat")
        s.map("IconDanger.TButton",
              background=[("active", C["hover"])],
              foreground=[("active", C["danger"])])
        # ConfigIcon.TButton — gear icon used in API settings rows
        s.configure("ConfigIcon.TButton", background=C["card"], foreground=C["dim"],
                    font=(_FONT_ICON, 12), padding=(4, 4),
                    borderwidth=1, relief="flat",
                    lightcolor=C["border"], darkcolor=C["border"], bordercolor=C["border"])
        s.map("ConfigIcon.TButton",
              background=[("active", C["hover"])],
              foreground=[("active", C["accent"])],
              lightcolor=[("active", C["hover"])],
              darkcolor=[("active", C["hover"])])
        # GeminiSave.TButton — filled accent save button with text label
        s.configure("GeminiSave.TButton", background=C["accent"], foreground=_btn_fg,
                    font=(_FONT_UI, 10, "bold"), padding=(14, 7),
                    borderwidth=0, relief="flat")
        s.map("GeminiSave.TButton",
              background=[("active", _btn_hover), ("disabled", C["border"])],
              foreground=[("active", _btn_fg), ("disabled", _dis_fg)])
        # GeminiCancel.TButton — ghost cancel with text label
        s.configure("GeminiCancel.TButton", background=C["card"], foreground=C["dim"],
                    font=(_FONT_UI, 10), padding=(14, 7),
                    borderwidth=0, relief="flat")
        s.map("GeminiCancel.TButton",
              background=[("active", C["hover"])],
              foreground=[("active", C["text"])])
        s.configure("GeminiStatus.TLabel", background=C["card"], foreground=C["success"],
                    font=(_FONT_UI, 9))
        s.configure("TEntry", fieldbackground=C["card"], foreground=C["text"],
                    insertcolor=C["accent"], padding=(10,7), font=(_FONT_UI,11),
                    borderwidth=1, relief="flat")
        s.map("TEntry", fieldbackground=[("readonly", C["card"])],
              foreground=[("readonly", C["dim"])])
        s.configure("TCombobox", fieldbackground=C["card"], foreground=C["text"],
                    background=C["card"], padding=(8,6), font=(_FONT_UI,10),
                    borderwidth=1, relief="flat")
        s.map("TCombobox", fieldbackground=[("readonly",C["card"])],
              foreground=[("readonly",C["text"])])
        s.configure("Treeview", background=C["surface"], foreground=C["text"],
                    fieldbackground=C["surface"],
                    rowheight=self._settings.get("row_height", 40),
                    font=(_FONT_UI, self._settings.get("font_size", 9)), borderwidth=0)
        s.configure("Treeview.Heading", background=C["card"], foreground=C["dim"],
                    relief="flat", font=(_FONT_UI,9,"bold"), padding=(8,7))
        s.map("Treeview", background=[("selected",C["sel_bg"])], foreground=[("selected",C["sel_fg"])])
        s.map("Treeview.Heading", background=[("active",C["hover"])])
        s.configure("TScrollbar", background=C["surface"], troughcolor=C["surface"],
                    arrowcolor=C["dim"], borderwidth=0, relief="flat", width=6)
        s.map("TScrollbar", background=[("active",C["dim"]),("!active",C["surface"]),("disabled",C["surface"])],
              troughcolor=[("active",C["surface"]),("!active",C["surface"])])
        s.configure("TProgressbar", background=C["accent"], troughcolor=C["card"],
                    borderwidth=0, thickness=3)

    # ── layout ─────────────────────────────────────────────────────────────────

    def _build_ui(self):
        # header — top row: title left, buttons right
        hdr = ttk.Frame(self)
        hdr.pack(fill="x", padx=22, pady=(18,2))
        tk.Label(hdr, text="", font=(_FONT_EMOJI,22),
                 bg=C["bg"], fg=C["text"]).pack(side="left", padx=(0,10))
        ttk.Label(hdr, text="SubFinder", style="Head.TLabel").pack(side="left", pady=(0,9))
        _btn_help = ttk.Button(hdr, text="❓", style="Ghost.TButton", width=3,
                               command=self._open_readme)
        _btn_help.pack(side="right", padx=(0,0))
        _btn_log = ttk.Button(hdr, text="", style="Ghost.TButton", width=3,
                              command=self._open_log)
        _btn_log.pack(side="right", padx=(0,4))
        _btn_settings = ttk.Button(hdr, text="", style="Ghost.TButton", width=3,
                                   command=self._open_settings)
        _btn_settings.pack(side="right", padx=(0,4))
        _Tooltip(_btn_help,     "Help")
        _Tooltip(_btn_log,      "View log")
        _Tooltip(_btn_settings, "Settings")
        self.status_var = tk.StringVar(value="")
        tk.Frame(self, bg=C["border"], height=1).pack(fill="x", pady=(8,0))

        # search row
        row1 = ttk.Frame(self)
        row1.pack(fill="x", padx=22, pady=(14,6))
        row1.columnconfigure(1, weight=1)
        ttk.Label(row1, text="Search:", style="Dim.TLabel").grid(row=0, column=0, sticky="w", padx=(0,8))
        self.q_var   = tk.StringVar()
        self.q_entry = ttk.Entry(row1, textvariable=self.q_var)
        self.q_entry.grid(row=0, column=1, sticky="ew", padx=(0,8))
        self.q_entry.bind("<Return>", lambda _e: self._start_search())
        self.btn_search = ttk.Button(row1, text="", width=3, command=self._start_search)
        self.btn_search.grid(row=0, column=2)
        _Tooltip(self.btn_search, "Search")

        # filter row
        row2 = ttk.Frame(self)
        row2.pack(fill="x", padx=22, pady=(0,14))
        def lbl(t): ttk.Label(row2, text=t, style="Dim.TLabel").pack(side="left", padx=(0,5))
        lbl("Language:")

        # ── multi-checkbox language dropdown ──────────────────────────────────
        # Initialise selected languages from settings (stored as a list of names)
        _saved_langs = self._settings.get("last_languages", None)
        if _saved_langs is None:
            # Migrate from old single-language setting
            _old = self._settings.get("last_language", "English")
            _saved_langs = [_old] if _old in LANGUAGES else ["English"]
        self._lang_checks: dict = {}   # name → BooleanVar
        for name in sorted(LANGUAGES.keys()):
            self._lang_checks[name] = tk.BooleanVar(value=(name in _saved_langs))

        # Button that shows current selection and opens the dropdown
        self._lang_btn_var = tk.StringVar()
        def _update_lang_btn():
            sel = [n for n, v in self._lang_checks.items() if v.get()]
            if not sel:
                self._lang_btn_var.set("(none)")
            elif len(sel) == 1:
                self._lang_btn_var.set(sel[0])
            else:
                self._lang_btn_var.set("{} languages".format(len(sel)))
        _update_lang_btn()

        def _save_lang_selection():
            sel = [n for n, v in self._lang_checks.items() if v.get()]
            self._settings["last_languages"] = sel
            # Keep lang_var in sync so session cache stores the correct primary language.
            # NOTE: self.lang_var is defined ~120 lines below this closure at the
            # lang_var StringVar assignment.  It is guaranteed to exist before this
            # closure can ever be invoked (user must click the dropdown after _build_ui
            # completes, which runs that assignment first).
            if sel:
                self.lang_var.set(sel[0])
            self._save_settings()   # save immediately, no debounce

        def _refresh_lang_values():
            names = sorted(LANGUAGES.keys())
            vals = [("✓ " if self._lang_checks[n].get() else "    ") + n for n in names]
            self._lang_combo["values"] = vals
            _update_lang_btn()

        self._lang_dropdown_win = None

        def _close_lang_dropdown():
            if self._lang_dropdown_win and self._lang_dropdown_win.winfo_exists():
                self._lang_dropdown_win.destroy()
            self._lang_dropdown_win = None
            self.after_idle(self.focus_set)

        def _open_lang_dropdown():
            if self._lang_dropdown_win and self._lang_dropdown_win.winfo_exists():
                _close_lang_dropdown(); return

            cb = self._lang_combo
            cb.update_idletasks()

            # Read the exact colors ttk uses for THIS combobox on THIS platform
            # by querying the style engine directly
            st = ttk.Style(self)
            bg  = st.lookup("TCombobox", "fieldbackground", default=C["card"])
            fg  = st.lookup("TCombobox", "foreground",      default=C["text"])
            sbg = st.lookup("TCombobox", "selectbackground",default=C["sel_bg"])
            sfg = st.lookup("TCombobox", "selectforeground",default=C["sel_fg"])
            font = (_FONT_UI, 10)

            win = tk.Toplevel(self)
            self._lang_dropdown_win = win  # Fix: assign so the toggle guard works
            win.overrideredirect(True)
            win.configure(bg=C["text"])

            x = cb.winfo_rootx()
            y = cb.winfo_rooty() + cb.winfo_height()
            w = cb.winfo_width()

            # Outer frame with 1px accent border
            outer = tk.Frame(win, bg=bg, bd=0)
            outer.pack(fill="both", expand=True, padx=1, pady=1)

            lb = tk.Listbox(outer, bg=bg, fg=fg,
                            selectbackground=sbg, selectforeground=sfg,
                            font=font, relief="flat", bd=0,
                            highlightthickness=0, activestyle="none",
                            width=0, exportselection=False)

            names = sorted(LANGUAGES.keys())
            for n in names:
                prefix = "✓ " if self._lang_checks[n].get() else "    "
                lb.insert("end", prefix + n)

            sb = ttk.Scrollbar(outer, orient="vertical", command=lb.yview)
            lb.configure(yscrollcommand=sb.set)

            show = min(len(names), 15)
            lb.configure(height=show)

            if len(names) > show:
                sb.pack(side="right", fill="y")
            lb.pack(side="left", fill="both", expand=True)

            def _on_pick(e):
                idx = lb.nearest(e.y)
                if idx < 0 or idx >= len(names): return
                n = names[idx]
                self._lang_checks[n].set(not self._lang_checks[n].get())
                _save_lang_selection()
                _update_lang_btn()
                # Redraw the listbox item in place
                lb.delete(idx)
                prefix = "✓ " if self._lang_checks[n].get() else "    "
                lb.insert(idx, prefix + n)

            lb.bind("<Button-1>", _on_pick)
            lb.bind("<MouseWheel>", lambda e: lb.yview_scroll(
                int(-e.delta) if sys.platform == "darwin" else int(-1*(e.delta/120)), "units"))
            # Linux/X11 uses Button-4 (scroll up) and Button-5 (scroll down)
            # instead of <MouseWheel>.  Without these bindings the dropdown
            # list cannot be scrolled with the mouse wheel on Linux.
            lb.bind("<Button-4>", lambda e: lb.yview_scroll(-1, "units"))
            lb.bind("<Button-5>", lambda e: lb.yview_scroll( 1, "units"))

            win.update_idletasks()
            win.geometry("{}x{}+{}+{}".format(w, win.winfo_reqheight(), x, y))

            win.bind("<FocusOut>", lambda e: self.after(100, _close_lang_dropdown))
            win.bind("<Escape>",   lambda e: _close_lang_dropdown())
            win.protocol("WM_DELETE_WINDOW", _close_lang_dropdown)
            win.focus_set()

        for var in self._lang_checks.values():
            var.trace_add("write", lambda *_: _update_lang_btn())

        # ── Language combobox — identical widget to Sort by ──────────────────────
        self._lang_combo = ttk.Combobox(row2, textvariable=self._lang_btn_var,
                                        state="readonly", width=14)
        self._lang_combo["values"] = ["__placeholder__"]
        _refresh_lang_values()
        self._lang_combo.pack(side="left", padx=(0, 16))

        # Intercept every way the native dropdown can open and use ours instead
        def _intercept(e):
            self._lang_combo.after_idle(_open_lang_dropdown)
            return "break"
        self._lang_combo.bind("<Button-1>",           _intercept)
        self._lang_combo.bind("<ButtonRelease-1>",    lambda e: "break")
        self._lang_combo.bind("<space>",              _intercept)
        self._lang_combo.bind("<Return>",             _intercept)
        self._lang_combo.bind("<<ComboboxSelected>>", lambda e: "break")

        # Keep a compat StringVar so other code that reads lang_var still works
        self.lang_var = tk.StringVar(value=_saved_langs[0] if _saved_langs else "English")

        lbl("Sort by:")
        self.sort_var = tk.StringVar(value=self._settings.get("sort_var", "Score"))
        # Restore column sort state
        self._col_sort_state  = dict(self._settings.get("sort_col_state", {}))
        self._active_sort_col = self._settings.get("sort_active_col", "")
        self._sort_direction  = self._settings.get("sort_direction", "desc")
        _sort_options = ["Score", "Language", "Format", "Provider", "Release"]

        self._sort_combo = ttk.Combobox(row2, textvariable=self.sort_var,
                                        state="readonly", width=12)
        self._sort_combo["values"] = _sort_options
        self._sort_combo.pack(side="left")
        self._sort_dropdown_win = None

        def _close_sort_dropdown():
            if self._sort_dropdown_win and self._sort_dropdown_win.winfo_exists():
                self._sort_dropdown_win.destroy()
            self._sort_dropdown_win = None
            self.after_idle(self.focus_set)

        def _open_sort_dropdown():
            if self._sort_dropdown_win and self._sort_dropdown_win.winfo_exists():
                _close_sort_dropdown(); return

            cb = self._sort_combo
            cb.update_idletasks()

            st = ttk.Style(self)
            bg  = st.lookup("TCombobox", "fieldbackground", default=C["card"])
            fg  = st.lookup("TCombobox", "foreground",      default=C["text"])
            sbg = st.lookup("TCombobox", "selectbackground",default=C["sel_bg"])
            sfg = st.lookup("TCombobox", "selectforeground",default=C["sel_fg"])
            font = (_FONT_UI, 10)

            win = tk.Toplevel(self)
            win.overrideredirect(True)
            win.configure(bg=C["text"])
            self._sort_dropdown_win = win

            x = cb.winfo_rootx()
            y = cb.winfo_rooty() + cb.winfo_height()
            w = cb.winfo_width()

            outer = tk.Frame(win, bg=bg, bd=0)
            outer.pack(fill="both", expand=True, padx=1, pady=1)

            lb = tk.Listbox(outer, bg=bg, fg=fg,
                            selectbackground=sbg, selectforeground=sfg,
                            font=font, relief="flat", bd=0,
                            highlightthickness=0, activestyle="none",
                            width=0, exportselection=False)

            # Populates the listbox with checkmarks for the active sort
            def _repopulate_lb():
                lb.delete(0, "end")
                for opt in _sort_options:
                    prefix = "✓ " if self.sort_var.get() == opt else "    "
                    lb.insert("end", prefix + opt)

            _repopulate_lb()
            lb.configure(height=len(_sort_options))
            lb.pack(fill="both", expand=True)

            _sort_to_col = {"Score":"score","Language":"language","Format":"fmt",
                            "Provider":"provider","Release":"release"}

            def _on_pick(e):
                idx = lb.nearest(e.y)
                if idx < 0 or idx >= len(_sort_options): return

                raw   = lb.get(idx)
                clean = raw.replace("✓ ", "").strip()

                if self.sort_var.get() == clean:
                    cur = self._sort_direction
                    self._sort_direction = "asc" if cur == "desc" else "desc"
                    col = _sort_to_col.get(clean, "")
                    if col:
                        self._col_sort_state[col] = self._sort_direction
                        self._update_heading_arrows(col, self._sort_direction)
                    self._refresh_tree()
                else:
                    self._sort_direction = "desc"
                    col = _sort_to_col.get(clean, "")
                    if col:
                        self._col_sort_state[col] = "desc"
                        self._update_heading_arrows(col, "desc")
                    self.sort_var.set(clean)
                    _repopulate_lb()

                self._save_settings()
                self.after(150, _close_sort_dropdown)

            lb.bind("<Button-1>", _on_pick)

            win.update_idletasks()
            win.geometry("{}x{}+{}+{}".format(w, win.winfo_reqheight(), x, y))

            win.bind("<FocusOut>", lambda e: self.after(100, _close_sort_dropdown))
            win.bind("<Escape>",   lambda e: _close_sort_dropdown())
            win.protocol("WM_DELETE_WINDOW", _close_sort_dropdown)
            win.focus_set()

        def _intercept_sort(e):
            self._sort_combo.after_idle(_open_sort_dropdown)
            return "break"
        self._sort_combo.bind("<Button-1>",           _intercept_sort)
        self._sort_combo.bind("<ButtonRelease-1>",    lambda e: "break")
        self._sort_combo.bind("<space>",              _intercept_sort)
        self._sort_combo.bind("<Return>",             _intercept_sort)
        self._sort_combo.bind("<<ComboboxSelected>>", lambda e: "break")
        self.sort_var.trace_add("write", lambda *_: self._refresh_tree())
        self.btn_stop = ttk.Button(row2, text="■", style="Stop.TButton", width=3,
                                   command=self._stop_search, state="disabled")
        self.btn_stop.pack(side="right")
        _Tooltip(self.btn_stop, "Stop search")

        # progress
        self.progress = ttk.Progressbar(self, mode="indeterminate", style="TProgressbar")
        # The progressbar is always packed (never hidden) so the layout never shifts
        # when a search starts.  At rest it draws as a thin 3px inactive stripe.
        self.progress.pack(fill="x", padx=22, pady=(0,6))

        # treeview
        tree_wrap = ttk.Frame(self)
        tree_wrap.pack(fill="both", expand=True, padx=22)
        cols = tuple(cid for cid, *_ in self.COLUMNS)
        self.tree = ttk.Treeview(tree_wrap, columns=cols, show="headings", selectmode="browse")
        for cid, _skey, head, w, anc in self.COLUMNS:
            self.tree.heading(cid, text=head, command=lambda c=cid: self._col_sort(c))
            self.tree.column(cid, width=w, minwidth=36, anchor=anc)

        vsb = ttk.Scrollbar(tree_wrap, orient="vertical", command=self.tree.yview)
        def _on_yscroll(first, last):
            if float(first) <= 0.0 and float(last) >= 1.0: vsb.pack_forget()
            else:
                if not vsb.winfo_ismapped():
                    vsb.pack(side="right", fill="y", before=self.tree)
            vsb.set(first, last)
        self.tree.configure(yscrollcommand=_on_yscroll)
        self.tree.pack(side="left", fill="both", expand=True)
        self._configure_tags()
        self.tree.bind("<<TreeviewSelect>>", self._on_select)
        self.tree.bind("<Double-1>",         self._on_tree_double_click)
        self.tree.bind("<Return>", lambda _e: self._do_load(
            close_after=self._settings.get("close_on_dbl_click", True)))
        # Right-click context menu (row = full menu; empty area = minimal menu)
        self.tree.bind("<Button-3>",        self._on_tree_right_click)
        self.tree.bind("<Button-3>",        self._on_tree_empty_right_click, add="+")
        # Global window right-click: same two-item menu on any non-treeview area.
        # bind_all fires for every widget; the handler filters out the treeview.
        self.bind_all("<Button-3>",         self._on_window_right_click, add="+")
        # Column drag-reorder: click and hold a heading then drag to another to reorder.
        self.tree.bind("<ButtonPress-1>",   self._on_heading_press)
        self.tree.bind("<B1-Motion>",       self._on_col_drag_motion)
        self.tree.bind("<ButtonRelease-1>", self._on_col_drag_release)
        self._drag_target_col = ""  # col id currently highlighted as drop target
        self._setup_cell_tooltip()

        # detail panel (not packed yet)
        self.detail_frame = tk.Frame(self, bg=C["card"])
        self.detail_text  = tk.Text(self.detail_frame, bg=C["card"], fg=C["text"],
                                    font=(_FONT_MONO,9), wrap="word", relief="flat",
                                    bd=0, state="disabled", height=4)
        self.detail_text.pack(fill="both", expand=True, padx=12, pady=8)

        # bottom container — holds the actual bottom bar + optional warning banner below it
        self._bottom_container = tk.Frame(self, bg=C["bg"])
        self._bottom_container.pack(fill="x", padx=22, pady=12)
        _bottom_container = self._bottom_container

        # actual bottom bar (packed first = appears above the warning banner)
        self._bot = ttk.Frame(_bottom_container)
        self._bot.pack(fill="x")

        # warning banner (packed after = appears below the bottom bar)
        # Mirrors the detail panel: expands the window when shown, shrinks it back when hidden.
        # NOTE: There are 5 near-identical warning banners below (pywin32, subliminal, pysubs2,
        # ffsubsync/alass, ffmpeg).  They share the same amber palette, layout, and expand/collapse mechanics.
        # They are intentionally inline (not refactored into a helper) so each banner's dismiss
        # key, warning text, and hyperlink are co-located and easy to find/edit independently.

        # ── pywin32 warning banner ────────────────────────────────────────────
        # Shown on Windows when pywin32 is not installed (needed for IPC).
        # Exact same structure as the subliminal banner above.
        self._warn_banner_pywin32 = None
        if not _PYWIN32_OK and not self._settings.get("pywin32_warn_dismissed", False):
            # Amber warning colours — intentionally outside the theme palette so that
            # _apply_theme()'s match_color() never re-colors these widgets on theme switch.
            _wb_bdr  = "#c8860a"   # amber border
            _wb_bg   = "#2d2000"   # deep amber-black background
            _wb_icon = "#ffc107"   # bright amber icon
            _wb_head = "#ffe082"   # warm white headline
            _wb_body = "#c8a84b"   # muted amber body text

            # Outer border frame → inner content frame
            _pywin32_warn_outer = tk.Frame(_bottom_container, bg=_wb_bdr)
            _pywin32_warn_inner = tk.Frame(_pywin32_warn_outer, bg=_wb_bg, padx=10, pady=7)
            _pywin32_warn_inner.pack(fill="both", expand=True, padx=1, pady=1)
            self._warn_banner_pywin32 = _pywin32_warn_outer

            # right-side: dismiss controls (packed BEFORE left so it never gets squeezed off)
            _pywin32_right = tk.Frame(_pywin32_warn_inner, bg=_wb_bg)
            _pywin32_right.pack(side="right", padx=(8, 0), pady=0)

            # left-side: frame with three labels — icon (large amber), bold
            # headline, and body text — all packed side-by-side so each can
            # carry its own font/colour independently.
            _pywin32_warn_left = tk.Frame(_pywin32_warn_inner, bg=_wb_bg)
            _pywin32_warn_left.pack(side="left", fill="x", expand=True)

            _pywin32_warn_icon_lbl = tk.Label(_pywin32_warn_left, bg=_wb_bg,
                                              font=(_FONT_EMOJI or _FONT_UI, 11),
                                              fg=_wb_icon, text="⚠", anchor="w",
                                              cursor="arrow")
            _pywin32_warn_icon_lbl.pack(side="left", padx=(0, 6))

            _pywin32_warn_bold_lbl = tk.Label(_pywin32_warn_left, bg=_wb_bg,
                                              font=(_FONT_UI, 9, "bold"),
                                              fg=_wb_head,
                                              text="pywin32 not installed,",
                                              anchor="w", cursor="arrow")
            _pywin32_warn_bold_lbl.pack(side="left")

            _pywin32_warn_text = tk.Label(_pywin32_warn_left, bg=_wb_bg,
                                          font=(_FONT_UI, 9), relief="flat",
                                          anchor="w", justify="left", cursor="arrow",
                                          text="auto-loading into mpv disabled.")
            _pywin32_warn_text.config(fg=_wb_body)
            _pywin32_warn_text.pack(side="left", fill="x", expand=True)

            def _on_pywin32_banner_resize(e):
                new_w = max(50, e.width - _pywin32_right.winfo_reqwidth()
                            - _pywin32_warn_icon_lbl.winfo_reqwidth()
                            - _pywin32_warn_bold_lbl.winfo_reqwidth() - 60)
                _pywin32_warn_text.config(wraplength=new_w)
            _pywin32_warn_inner.bind("<Configure>", _on_pywin32_banner_resize)

            def _collapse_pywin32_warn_banner():
                """Unpack the banner and shrink the window by the banner's actual rendered height."""
                if not (self._warn_banner_pywin32 is not None and self._warn_banner_pywin32.winfo_ismapped()):
                    if self._warn_banner_pywin32 is not None:
                        self._warn_banner_pywin32.pack_forget()
                    return
                banner_h = self._warn_banner_pywin32.winfo_height()
                self._warn_banner_pywin32.pack_forget()
                geo = self.geometry()
                m = _GEO_SIZE_RE.match(geo)
                if m:
                    new_h = max(1, int(m.group(2)) - banner_h - 8)
                    self.geometry("{}x{}{}".format(m.group(1), new_h, m.group(3)))
                self._pre_warn_h = 0

            def _dismiss_pywin32_warn(e=None, permanent=False):
                _collapse_pywin32_warn_banner()
                if permanent:
                    self._settings["pywin32_warn_dismissed"] = True
                    self._save_settings()

            _pywin32_dont_show_lbl = tk.Label(_pywin32_right,
                                              text="Don't show again",
                                              bg=_wb_bg, fg=_wb_body,
                                              font=(_FONT_UI, 8), cursor="hand2")
            _pywin32_dont_show_lbl.pack(side="left", padx=(0, 2))
            _pywin32_dont_show_lbl.bind("<Enter>", lambda e: _pywin32_dont_show_lbl.config(fg=_wb_head))
            _pywin32_dont_show_lbl.bind("<Leave>", lambda e: _pywin32_dont_show_lbl.config(fg=_wb_body))
            _pywin32_dont_show_lbl.bind("<Button-1>", lambda e: _dismiss_pywin32_warn(permanent=True))

            tk.Label(_pywin32_right, text="·", bg=_wb_bg, fg=_wb_bdr,
                     font=(_FONT_UI, 8)).pack(side="left", padx=4)

            _pywin32_hide_lbl = tk.Label(_pywin32_right, text="Hide",
                                         bg=_wb_bg, fg=_wb_body,
                                         font=(_FONT_UI, 8), cursor="hand2")
            _pywin32_hide_lbl.pack(side="left")
            _pywin32_hide_lbl.bind("<Enter>", lambda e: _pywin32_hide_lbl.config(fg=_wb_head))
            _pywin32_hide_lbl.bind("<Leave>", lambda e: _pywin32_hide_lbl.config(fg=_wb_body))
            _pywin32_hide_lbl.bind("<Button-1>", lambda e: _dismiss_pywin32_warn(permanent=False))

            # Defer pack + window expansion so the window is fully rendered first.
            # Guard: _pywin32_warn_banner_expanded ensures this fires exactly once even if
            # after() somehow fires multiple times (prevents infinite height growth).
            _pywin32_warn_banner_expanded = [False]
            def _expand_pywin32_warn_banner():
                if _pywin32_warn_banner_expanded[0]:
                    return
                _pywin32_warn_banner_expanded[0] = True
                geo = self.geometry()
                m = _GEO_SIZE_RE.match(geo)
                if m:
                    self._pre_warn_h = int(m.group(2))
                self._warn_banner_pywin32.pack(fill="x", pady=(8, 0))
                self.update_idletasks()
                geo2 = self.geometry()
                m2 = _GEO_SIZE_RE.match(geo2)
                if m2:
                    extra = self._warn_banner_pywin32.winfo_reqheight() + 8
                    self.geometry("{}x{}{}".format(m2.group(1), int(m2.group(2)) + extra, m2.group(3)))
            self.after(50, _expand_pywin32_warn_banner)

        self._warn_banner = None
        if not SUBLIMINAL_OK and not self._settings.get("subliminal_warn_dismissed", False):
            # Amber warning colours — intentionally outside the theme palette so that
            # _apply_theme()'s match_color() never re-colors these widgets on theme switch.
            _wb_bdr  = "#c8860a"   # amber border
            _wb_bg   = "#2d2000"   # deep amber-black background
            _wb_icon = "#ffc107"   # bright amber icon
            _wb_head = "#ffe082"   # warm white headline
            _wb_body = "#c8a84b"   # muted amber body text

            # Outer border frame → inner content frame
            _warn_outer = tk.Frame(_bottom_container, bg=_wb_bdr)
            _warn_inner = tk.Frame(_warn_outer, bg=_wb_bg, padx=10, pady=7)
            _warn_inner.pack(fill="both", expand=True, padx=1, pady=1)
            self._warn_banner = _warn_outer

            # right-side: dismiss controls (packed BEFORE left so it never gets squeezed off)
            _right = tk.Frame(_warn_inner, bg=_wb_bg)
            _right.pack(side="right", padx=(8, 0), pady=0)

            # left-side: frame with three labels — icon (large amber), bold
            # headline, and body text — all packed side-by-side so each can
            # carry its own font/colour independently.
            _warn_left = tk.Frame(_warn_inner, bg=_wb_bg)
            _warn_left.pack(side="left", fill="x", expand=True)

            _warn_icon_lbl = tk.Label(_warn_left, bg=_wb_bg,
                                      font=(_FONT_EMOJI or _FONT_UI, 11),
                                      fg=_wb_icon, text="⚠", anchor="w",
                                      cursor="arrow")
            _warn_icon_lbl.pack(side="left", padx=(0, 6))

            _warn_bold_lbl = tk.Label(_warn_left, bg=_wb_bg,
                                      font=(_FONT_UI, 9, "bold"),
                                      fg=_wb_head,
                                      text="subliminal not installed,",
                                      anchor="w", cursor="arrow")
            _warn_bold_lbl.pack(side="left")

            _warn_text = tk.Label(_warn_left, bg=_wb_bg,
                                  font=(_FONT_UI, 9), relief="flat",
                                  anchor="w", justify="left", cursor="arrow",
                                  text="searches need an API key.")
            _warn_text.config(fg=_wb_body)
            _warn_text.pack(side="left", fill="x", expand=True)

            def _on_banner_resize(e):
                new_w = max(50, e.width - _right.winfo_reqwidth()
                            - _warn_icon_lbl.winfo_reqwidth()
                            - _warn_bold_lbl.winfo_reqwidth() - 60)
                _warn_text.config(wraplength=new_w)
            _warn_inner.bind("<Configure>", _on_banner_resize)

            def _collapse_warn_banner():
                """Unpack the banner and shrink the window by the banner's actual rendered height."""
                if not (self._warn_banner is not None and self._warn_banner.winfo_ismapped()):
                    if self._warn_banner is not None:
                        self._warn_banner.pack_forget()
                    return
                banner_h = self._warn_banner.winfo_height()
                self._warn_banner.pack_forget()
                geo = self.geometry()
                m = _GEO_SIZE_RE.match(geo)
                if m:
                    new_h = max(1, int(m.group(2)) - banner_h - 8)
                    self.geometry("{}x{}{}".format(m.group(1), new_h, m.group(3)))
                self._pre_warn_h = 0

            def _dismiss_warn(e=None, permanent=False):
                _collapse_warn_banner()
                if permanent:
                    self._settings["subliminal_warn_dismissed"] = True
                    self._save_settings()

            _dont_show_lbl = tk.Label(_right,
                                      text="Don't show again",
                                      bg=_wb_bg, fg=_wb_body,
                                      font=(_FONT_UI, 8), cursor="hand2")
            _dont_show_lbl.pack(side="left", padx=(0, 2))
            _dont_show_lbl.bind("<Enter>", lambda e: _dont_show_lbl.config(fg=_wb_head))
            _dont_show_lbl.bind("<Leave>", lambda e: _dont_show_lbl.config(fg=_wb_body))
            _dont_show_lbl.bind("<Button-1>", lambda e: _dismiss_warn(permanent=True))

            tk.Label(_right, text="·", bg=_wb_bg, fg=_wb_bdr,
                     font=(_FONT_UI, 8)).pack(side="left", padx=4)

            _hide_lbl = tk.Label(_right, text="Hide",
                                 bg=_wb_bg, fg=_wb_body,
                                 font=(_FONT_UI, 8), cursor="hand2")
            _hide_lbl.pack(side="left")
            _hide_lbl.bind("<Enter>", lambda e: _hide_lbl.config(fg=_wb_head))
            _hide_lbl.bind("<Leave>", lambda e: _hide_lbl.config(fg=_wb_body))
            _hide_lbl.bind("<Button-1>", lambda e: _dismiss_warn(permanent=False))

            # Defer pack + window expansion so the window is fully rendered first.
            # Guard: _warn_banner_expanded ensures this fires exactly once even if
            # after() somehow fires multiple times (prevents infinite height growth).
            _warn_banner_expanded = [False]
            def _expand_warn_banner():
                if _warn_banner_expanded[0]:
                    return
                _warn_banner_expanded[0] = True
                geo = self.geometry()
                m = _GEO_SIZE_RE.match(geo)
                if m:
                    self._pre_warn_h = int(m.group(2))
                self._warn_banner.pack(fill="x", pady=(8, 0))
                self.update_idletasks()
                geo2 = self.geometry()
                m2 = _GEO_SIZE_RE.match(geo2)
                if m2:
                    extra = self._warn_banner.winfo_reqheight() + 8
                    self.geometry("{}x{}{}".format(m2.group(1), int(m2.group(2)) + extra, m2.group(3)))
            self.after(50, _expand_warn_banner)

        # ── pysubs2 warning banner ────────────────────────────────────────────
        # Shown when pysubs2 is not installed (needed for AI translation support).
        # Exact same structure as the subliminal banner above.
        self._warn_banner_pysubs2 = None
        if not _PYSUBS2_OK and not self._settings.get("pysubs2_warn_dismissed", False):
            # Amber warning colours — intentionally outside the theme palette so that
            # _apply_theme()'s match_color() never re-colors these widgets on theme switch.
            _wb_bdr  = "#c8860a"   # amber border
            _wb_bg   = "#2d2000"   # deep amber-black background
            _wb_icon = "#ffc107"   # bright amber icon
            _wb_head = "#ffe082"   # warm white headline
            _wb_body = "#c8a84b"   # muted amber body text

            # Outer border frame → inner content frame
            _pysubs2_warn_outer = tk.Frame(_bottom_container, bg=_wb_bdr)
            _pysubs2_warn_inner = tk.Frame(_pysubs2_warn_outer, bg=_wb_bg, padx=10, pady=7)
            _pysubs2_warn_inner.pack(fill="both", expand=True, padx=1, pady=1)
            self._warn_banner_pysubs2 = _pysubs2_warn_outer

            # right-side: dismiss controls (packed BEFORE left so it never gets squeezed off)
            _pysubs2_right = tk.Frame(_pysubs2_warn_inner, bg=_wb_bg)
            _pysubs2_right.pack(side="right", padx=(8, 0), pady=0)

            # left-side: frame with three labels — icon (large amber), bold
            # headline, and body text — all packed side-by-side so each can
            # carry its own font/colour independently.
            _pysubs2_warn_left = tk.Frame(_pysubs2_warn_inner, bg=_wb_bg)
            _pysubs2_warn_left.pack(side="left", fill="x", expand=True)

            _pysubs2_warn_icon_lbl = tk.Label(_pysubs2_warn_left, bg=_wb_bg,
                                              font=(_FONT_EMOJI or _FONT_UI, 11),
                                              fg=_wb_icon, text="⚠", anchor="w",
                                              cursor="arrow")
            _pysubs2_warn_icon_lbl.pack(side="left", padx=(0, 6))

            _pysubs2_warn_bold_lbl = tk.Label(_pysubs2_warn_left, bg=_wb_bg,
                                              font=(_FONT_UI, 9, "bold"),
                                              fg=_wb_head,
                                              text="pysubs2 not installed,",
                                              anchor="w", cursor="arrow")
            _pysubs2_warn_bold_lbl.pack(side="left")

            _pysubs2_warn_text = tk.Label(_pysubs2_warn_left, bg=_wb_bg,
                                          font=(_FONT_UI, 9), relief="flat",
                                          anchor="w", justify="left", cursor="arrow",
                                          text="needed for AI translation support.")
            _pysubs2_warn_text.config(fg=_wb_body)
            _pysubs2_warn_text.pack(side="left", fill="x", expand=True)

            def _on_pysubs2_banner_resize(e):
                new_w = max(50, e.width - _pysubs2_right.winfo_reqwidth()
                            - _pysubs2_warn_icon_lbl.winfo_reqwidth()
                            - _pysubs2_warn_bold_lbl.winfo_reqwidth() - 60)
                _pysubs2_warn_text.config(wraplength=new_w)
            _pysubs2_warn_inner.bind("<Configure>", _on_pysubs2_banner_resize)

            def _collapse_pysubs2_warn_banner():
                """Unpack the banner and shrink the window by the banner's actual rendered height."""
                if not (self._warn_banner_pysubs2 is not None and self._warn_banner_pysubs2.winfo_ismapped()):
                    if self._warn_banner_pysubs2 is not None:
                        self._warn_banner_pysubs2.pack_forget()
                    return
                banner_h = self._warn_banner_pysubs2.winfo_height()
                self._warn_banner_pysubs2.pack_forget()
                geo = self.geometry()
                m = _GEO_SIZE_RE.match(geo)
                if m:
                    new_h = max(1, int(m.group(2)) - banner_h - 8)
                    self.geometry("{}x{}{}".format(m.group(1), new_h, m.group(3)))
                self._pre_warn_h = 0

            def _dismiss_pysubs2_warn(e=None, permanent=False):
                _collapse_pysubs2_warn_banner()
                if permanent:
                    self._settings["pysubs2_warn_dismissed"] = True
                    self._save_settings()

            _pysubs2_dont_show_lbl = tk.Label(_pysubs2_right,
                                              text="Don't show again",
                                              bg=_wb_bg, fg=_wb_body,
                                              font=(_FONT_UI, 8), cursor="hand2")
            _pysubs2_dont_show_lbl.pack(side="left", padx=(0, 2))
            _pysubs2_dont_show_lbl.bind("<Enter>", lambda e: _pysubs2_dont_show_lbl.config(fg=_wb_head))
            _pysubs2_dont_show_lbl.bind("<Leave>", lambda e: _pysubs2_dont_show_lbl.config(fg=_wb_body))
            _pysubs2_dont_show_lbl.bind("<Button-1>", lambda e: _dismiss_pysubs2_warn(permanent=True))

            tk.Label(_pysubs2_right, text="·", bg=_wb_bg, fg=_wb_bdr,
                     font=(_FONT_UI, 8)).pack(side="left", padx=4)

            _pysubs2_hide_lbl = tk.Label(_pysubs2_right, text="Hide",
                                         bg=_wb_bg, fg=_wb_body,
                                         font=(_FONT_UI, 8), cursor="hand2")
            _pysubs2_hide_lbl.pack(side="left")
            _pysubs2_hide_lbl.bind("<Enter>", lambda e: _pysubs2_hide_lbl.config(fg=_wb_head))
            _pysubs2_hide_lbl.bind("<Leave>", lambda e: _pysubs2_hide_lbl.config(fg=_wb_body))
            _pysubs2_hide_lbl.bind("<Button-1>", lambda e: _dismiss_pysubs2_warn(permanent=False))

            # Defer pack + window expansion so the window is fully rendered first.
            # Guard: _pysubs2_warn_banner_expanded ensures this fires exactly once even if
            # after() somehow fires multiple times (prevents infinite height growth).
            _pysubs2_warn_banner_expanded = [False]
            def _expand_pysubs2_warn_banner():
                if _pysubs2_warn_banner_expanded[0]:
                    return
                _pysubs2_warn_banner_expanded[0] = True
                geo = self.geometry()
                m = _GEO_SIZE_RE.match(geo)
                if m:
                    self._pre_warn_h = int(m.group(2))
                self._warn_banner_pysubs2.pack(fill="x", pady=(8, 0))
                self.update_idletasks()
                geo2 = self.geometry()
                m2 = _GEO_SIZE_RE.match(geo2)
                if m2:
                    extra = self._warn_banner_pysubs2.winfo_reqheight() + 8
                    self.geometry("{}x{}{}".format(m2.group(1), int(m2.group(2)) + extra, m2.group(3)))
            self.after(50, _expand_pysubs2_warn_banner)

        # ── ffsubsync / alass warning banner ─────────────────────────────────
        # Shown when neither ffsubsync nor alass is detected anywhere on the
        # system.  Exact same structure as the subliminal banner above.
        self._warn_banner_sync = None
        if not _SYNC_TOOL_OK and not self._settings.get("ffsubsync_warn_dismissed", False):
            # Amber warning colours — intentionally outside the theme palette so that
            # _apply_theme()'s match_color() never re-colors these widgets on theme switch.
            _wb_bdr  = "#c8860a"   # amber border
            _wb_bg   = "#2d2000"   # deep amber-black background
            _wb_icon = "#ffc107"   # bright amber icon
            _wb_head = "#ffe082"   # warm white headline
            _wb_body = "#c8a84b"   # muted amber body text

            # Outer border frame → inner content frame
            _sync_warn_outer = tk.Frame(_bottom_container, bg=_wb_bdr)
            _sync_warn_inner = tk.Frame(_sync_warn_outer, bg=_wb_bg, padx=10, pady=7)
            _sync_warn_inner.pack(fill="both", expand=True, padx=1, pady=1)
            self._warn_banner_sync = _sync_warn_outer

            # right-side: dismiss controls (packed BEFORE left so it never gets squeezed off)
            _sync_right = tk.Frame(_sync_warn_inner, bg=_wb_bg)
            _sync_right.pack(side="right", padx=(8, 0), pady=0)

            # left-side: frame with three labels — icon (large amber), bold
            # headline, and body text — all packed side-by-side so each can
            # carry its own font/colour independently.
            _sync_warn_left = tk.Frame(_sync_warn_inner, bg=_wb_bg)
            _sync_warn_left.pack(side="left", fill="x", expand=True)

            _sync_warn_icon_lbl = tk.Label(_sync_warn_left, bg=_wb_bg,
                                           font=(_FONT_EMOJI or _FONT_UI, 11),
                                           fg=_wb_icon, text="⚠", anchor="w",
                                           cursor="arrow")
            _sync_warn_icon_lbl.pack(side="left", padx=(0, 6))

            _sync_warn_bold_lbl = tk.Label(_sync_warn_left, bg=_wb_bg,
                                           font=(_FONT_UI, 9, "bold"),
                                           fg=_wb_head,
                                           text="ffsubsync not installed,",
                                           anchor="w", cursor="arrow")
            _sync_warn_bold_lbl.pack(side="left")

            _sync_warn_text = tk.Label(_sync_warn_left, bg=_wb_bg,
                                       font=(_FONT_UI, 9), relief="flat",
                                       anchor="w", justify="left", cursor="arrow",
                                       text="Auto subtitle sync unavailable.")
            _sync_warn_text.config(fg=_wb_body)
            _sync_warn_text.pack(side="left", fill="x", expand=True)

            def _on_sync_banner_resize(e):
                new_w = max(50, e.width - _sync_right.winfo_reqwidth()
                            - _sync_warn_icon_lbl.winfo_reqwidth()
                            - _sync_warn_bold_lbl.winfo_reqwidth() - 60)
                _sync_warn_text.config(wraplength=new_w)
            _sync_warn_inner.bind("<Configure>", _on_sync_banner_resize)

            def _collapse_sync_warn_banner():
                """Unpack the banner and shrink the window by the banner's actual rendered height."""
                if not (self._warn_banner_sync is not None and self._warn_banner_sync.winfo_ismapped()):
                    if self._warn_banner_sync is not None:
                        self._warn_banner_sync.pack_forget()
                    return
                banner_h = self._warn_banner_sync.winfo_height()
                self._warn_banner_sync.pack_forget()
                geo = self.geometry()
                m = _GEO_SIZE_RE.match(geo)
                if m:
                    new_h = max(1, int(m.group(2)) - banner_h - 8)
                    self.geometry("{}x{}{}".format(m.group(1), new_h, m.group(3)))
                self._pre_warn_h = 0

            def _dismiss_sync_warn(e=None, permanent=False):
                _collapse_sync_warn_banner()
                if permanent:
                    self._settings["ffsubsync_warn_dismissed"] = True
                    self._save_settings()

            _sync_dont_show_lbl = tk.Label(_sync_right,
                                           text="Don't show again",
                                           bg=_wb_bg, fg=_wb_body,
                                           font=(_FONT_UI, 8), cursor="hand2")
            _sync_dont_show_lbl.pack(side="left", padx=(0, 2))
            _sync_dont_show_lbl.bind("<Enter>", lambda e: _sync_dont_show_lbl.config(fg=_wb_head))
            _sync_dont_show_lbl.bind("<Leave>", lambda e: _sync_dont_show_lbl.config(fg=_wb_body))
            _sync_dont_show_lbl.bind("<Button-1>", lambda e: _dismiss_sync_warn(permanent=True))

            tk.Label(_sync_right, text="·", bg=_wb_bg, fg=_wb_bdr,
                     font=(_FONT_UI, 8)).pack(side="left", padx=4)

            _sync_hide_lbl = tk.Label(_sync_right, text="Hide",
                                      bg=_wb_bg, fg=_wb_body,
                                      font=(_FONT_UI, 8), cursor="hand2")
            _sync_hide_lbl.pack(side="left")
            _sync_hide_lbl.bind("<Enter>", lambda e: _sync_hide_lbl.config(fg=_wb_head))
            _sync_hide_lbl.bind("<Leave>", lambda e: _sync_hide_lbl.config(fg=_wb_body))
            _sync_hide_lbl.bind("<Button-1>", lambda e: _dismiss_sync_warn(permanent=False))

            # Defer pack + window expansion so the window is fully rendered first.
            # Guard: _sync_warn_banner_expanded ensures this fires exactly once even if
            # after() somehow fires multiple times (prevents infinite height growth).
            _sync_warn_banner_expanded = [False]
            def _expand_sync_warn_banner():
                if _sync_warn_banner_expanded[0]:
                    return
                _sync_warn_banner_expanded[0] = True
                geo = self.geometry()
                m = _GEO_SIZE_RE.match(geo)
                if m:
                    self._pre_warn_h = int(m.group(2))
                self._warn_banner_sync.pack(fill="x", pady=(8, 0))
                self.update_idletasks()
                geo2 = self.geometry()
                m2 = _GEO_SIZE_RE.match(geo2)
                if m2:
                    extra = self._warn_banner_sync.winfo_reqheight() + 8
                    self.geometry("{}x{}{}".format(m2.group(1), int(m2.group(2)) + extra, m2.group(3)))
            self.after(50, _expand_sync_warn_banner)

        # ── ffmpeg warning banner ─────────────────────────────────────────────
        # Shown when ffmpeg is not found on the system (needed for ffsubsync).
        # Exact same structure as the subliminal banner above.
        self._warn_banner_ffmpeg = None
        if not _FFMPEG_OK and not self._settings.get("ffmpeg_warn_dismissed", False):
            # Amber warning colours — intentionally outside the theme palette so that
            # _apply_theme()'s match_color() never re-colors these widgets on theme switch.
            _wb_bdr  = "#c8860a"   # amber border
            _wb_bg   = "#2d2000"   # deep amber-black background
            _wb_icon = "#ffc107"   # bright amber icon
            _wb_head = "#ffe082"   # warm white headline
            _wb_body = "#c8a84b"   # muted amber body text

            # Outer border frame → inner content frame
            _ffmpeg_warn_outer = tk.Frame(_bottom_container, bg=_wb_bdr)
            _ffmpeg_warn_inner = tk.Frame(_ffmpeg_warn_outer, bg=_wb_bg, padx=10, pady=7)
            _ffmpeg_warn_inner.pack(fill="both", expand=True, padx=1, pady=1)
            self._warn_banner_ffmpeg = _ffmpeg_warn_outer

            # right-side: dismiss controls (packed BEFORE left so it never gets squeezed off)
            _ffmpeg_right = tk.Frame(_ffmpeg_warn_inner, bg=_wb_bg)
            _ffmpeg_right.pack(side="right", padx=(8, 0), pady=0)

            # left-side: frame with three labels — icon (large amber), bold
            # headline, and body text — all packed side-by-side so each can
            # carry its own font/colour independently.
            _ffmpeg_warn_left = tk.Frame(_ffmpeg_warn_inner, bg=_wb_bg)
            _ffmpeg_warn_left.pack(side="left", fill="x", expand=True)

            _ffmpeg_warn_icon_lbl = tk.Label(_ffmpeg_warn_left, bg=_wb_bg,
                                             font=(_FONT_EMOJI or _FONT_UI, 11),
                                             fg=_wb_icon, text="⚠", anchor="w",
                                             cursor="arrow")
            _ffmpeg_warn_icon_lbl.pack(side="left", padx=(0, 6))

            _ffmpeg_warn_bold_lbl = tk.Label(_ffmpeg_warn_left, bg=_wb_bg,
                                             font=(_FONT_UI, 9, "bold"),
                                             fg=_wb_head,
                                             text="ffmpeg not installed,",
                                             anchor="w", cursor="arrow")
            _ffmpeg_warn_bold_lbl.pack(side="left")

            _ffmpeg_warn_text = tk.Label(_ffmpeg_warn_left, bg=_wb_bg,
                                         font=(_FONT_UI, 9), relief="flat",
                                         anchor="w", justify="left", cursor="arrow",
                                         text="needed for ffsubsync.")
            _ffmpeg_warn_text.config(fg=_wb_body)
            _ffmpeg_warn_text.pack(side="left", fill="x", expand=True)

            def _on_ffmpeg_banner_resize(e):
                new_w = max(50, e.width - _ffmpeg_right.winfo_reqwidth()
                            - _ffmpeg_warn_icon_lbl.winfo_reqwidth()
                            - _ffmpeg_warn_bold_lbl.winfo_reqwidth() - 60)
                _ffmpeg_warn_text.config(wraplength=new_w)
            _ffmpeg_warn_inner.bind("<Configure>", _on_ffmpeg_banner_resize)

            def _collapse_ffmpeg_warn_banner():
                """Unpack the banner and shrink the window by the banner's actual rendered height."""
                if not (self._warn_banner_ffmpeg is not None and self._warn_banner_ffmpeg.winfo_ismapped()):
                    if self._warn_banner_ffmpeg is not None:
                        self._warn_banner_ffmpeg.pack_forget()
                    return
                banner_h = self._warn_banner_ffmpeg.winfo_height()
                self._warn_banner_ffmpeg.pack_forget()
                geo = self.geometry()
                m = _GEO_SIZE_RE.match(geo)
                if m:
                    new_h = max(1, int(m.group(2)) - banner_h - 8)
                    self.geometry("{}x{}{}".format(m.group(1), new_h, m.group(3)))
                self._pre_warn_h = 0

            def _dismiss_ffmpeg_warn(e=None, permanent=False):
                _collapse_ffmpeg_warn_banner()
                if permanent:
                    self._settings["ffmpeg_warn_dismissed"] = True
                    self._save_settings()

            _ffmpeg_dont_show_lbl = tk.Label(_ffmpeg_right,
                                             text="Don't show again",
                                             bg=_wb_bg, fg=_wb_body,
                                             font=(_FONT_UI, 8), cursor="hand2")
            _ffmpeg_dont_show_lbl.pack(side="left", padx=(0, 2))
            _ffmpeg_dont_show_lbl.bind("<Enter>", lambda e: _ffmpeg_dont_show_lbl.config(fg=_wb_head))
            _ffmpeg_dont_show_lbl.bind("<Leave>", lambda e: _ffmpeg_dont_show_lbl.config(fg=_wb_body))
            _ffmpeg_dont_show_lbl.bind("<Button-1>", lambda e: _dismiss_ffmpeg_warn(permanent=True))

            tk.Label(_ffmpeg_right, text="·", bg=_wb_bg, fg=_wb_bdr,
                     font=(_FONT_UI, 8)).pack(side="left", padx=4)

            _ffmpeg_hide_lbl = tk.Label(_ffmpeg_right, text="Hide",
                                        bg=_wb_bg, fg=_wb_body,
                                        font=(_FONT_UI, 8), cursor="hand2")
            _ffmpeg_hide_lbl.pack(side="left")
            _ffmpeg_hide_lbl.bind("<Enter>", lambda e: _ffmpeg_hide_lbl.config(fg=_wb_head))
            _ffmpeg_hide_lbl.bind("<Leave>", lambda e: _ffmpeg_hide_lbl.config(fg=_wb_body))
            _ffmpeg_hide_lbl.bind("<Button-1>", lambda e: _dismiss_ffmpeg_warn(permanent=False))

            # Defer pack + window expansion so the window is fully rendered first.
            # Guard: _ffmpeg_warn_banner_expanded ensures this fires exactly once even if
            # after() somehow fires multiple times (prevents infinite height growth).
            _ffmpeg_warn_banner_expanded = [False]
            def _expand_ffmpeg_warn_banner():
                if _ffmpeg_warn_banner_expanded[0]:
                    return
                _ffmpeg_warn_banner_expanded[0] = True
                geo = self.geometry()
                m = _GEO_SIZE_RE.match(geo)
                if m:
                    self._pre_warn_h = int(m.group(2))
                self._warn_banner_ffmpeg.pack(fill="x", pady=(8, 0))
                self.update_idletasks()
                geo2 = self.geometry()
                m2 = _GEO_SIZE_RE.match(geo2)
                if m2:
                    extra = self._warn_banner_ffmpeg.winfo_reqheight() + 8
                    self.geometry("{}x{}{}".format(m2.group(1), int(m2.group(2)) + extra, m2.group(3)))
            self.after(50, _expand_ffmpeg_warn_banner)

        self.count_var = tk.StringVar(value="")
        self._status_canvas = tk.Canvas(self._bot, height=18, bg=C["bg"], highlightthickness=0)
        self._status_text_id = self._status_canvas.create_text(
            4, 9, anchor="w", fill=C["dim"], font=(_FONT_UI, 9), text="")
        self._scroll_anim = None

        def _update_status_canvas(*_):
            self._status_canvas.itemconfigure(self._status_text_id, text=self.status_var.get())
            self._status_canvas.coords(self._status_text_id, 4, 9)
        self.status_var.trace_add("write", _update_status_canvas)

        def _on_hover(e):
            if self._scroll_anim: self.after_cancel(self._scroll_anim)
            bbox = self._status_canvas.bbox(self._status_text_id)
            if not bbox: return
            canvas_w = self._status_canvas.winfo_width()
            text_w = bbox[2] - bbox[0]
            if text_w <= canvas_w: return
            overflow = text_w - canvas_w + 8
            def scroll(step=0):
                if step > overflow:
                    return
                self._status_canvas.coords(self._status_text_id, 4 - step, 9)
                self._scroll_anim = self.after(16, scroll, step + 2)
            scroll()

        def _on_leave(e):
            if self._scroll_anim: self.after_cancel(self._scroll_anim)
            self._status_canvas.coords(self._status_text_id, 4, 9)

        self._status_canvas.bind("<Enter>", _on_hover)
        self._status_canvas.bind("<Leave>", _on_leave)
        self.btn_load = ttk.Button(self._bot, text="", width=3,
                                   command=lambda: self._do_load(close_after=False), state="disabled")
        self.btn_load.pack(side="right", padx=(8,0))
        _Tooltip(self.btn_load, "Load subtitle")
        self.detail_btn = ttk.Button(self._bot, text="", style="Ghost.TButton", width=3,
                                     command=self._toggle_detail)
        self.detail_btn.pack(side="right", padx=(0,4))
        _Tooltip(self.detail_btn, "Show detail panel")
        self._status_canvas.pack(side="left", fill="x", expand=True, padx=(0, 8))

    def _configure_tags(self):
        self.tree.tag_configure("excellent",      foreground=C["green"])
        self.tree.tag_configure("good",           foreground=C["accent"])
        self.tree.tag_configure("fair",           foreground=C["yellow"])
        self.tree.tag_configure("poor",           foreground=C["dim"])
        self.tree.tag_configure("downloaded",     background=C["card"], foreground=C["green"])
        self.tree.tag_configure("mpv_loaded",      background=C["card"], foreground=C["accent"])
        self.tree.tag_configure("dup_downloaded", background=C["card"], foreground=C["green"])
        self.tree.tag_configure("toggle_row",     foreground=C["accent"],
                                background=C["surface"], font=(_FONT_UI,10,"bold underline"))

    # ── startup ───────────────────────────────────────────────────────────────

    def _on_close(self):
        self._save_col_widths()
        # Persist current language selection
        self._settings["last_languages"] = [
            name for name, var in self._lang_checks.items() if var.get()
        ]
        if self._settings.get("free_resize", True) or self._settings.get("save_position", True):
            # Don't save geometry while maximized — would lock window to screen
            # size on next open instead of restoring the pre-maximized size.
            geo = None if self.wm_state() == "zoomed" else self.geometry()
            if geo is not None and self.detail_visible and self._pre_detail_h:
                m = _GEO_SIZE_RE.match(geo)
                if m:
                    geo = "{}x{}{}".format(m.group(1), self._pre_detail_h, m.group(3))
            if geo is not None:
                # If any warning banners are still visible, subtract their combined
                # height before saving so the window does not grow on every reopen.
                _banners = [
                    self._warn_banner_pywin32,
                    self._warn_banner,
                    self._warn_banner_pysubs2,
                    self._warn_banner_sync,
                    self._warn_banner_ffmpeg,
                ]
                for _b in _banners:
                    if _b is not None and _b.winfo_ismapped():
                        m = _GEO_SIZE_RE.match(geo)
                        if m:
                            _bh = _b.winfo_height()
                            geo = "{}x{}{}".format(
                                m.group(1),
                                max(1, int(m.group(2)) - _bh - 8),
                                m.group(3),
                            )
                self._settings["win_geometry"] = geo
        # Cancel any pending debounced save and flush immediately so settings
        # are never lost when the window closes between debounce ticks.
        if hasattr(self, "_save_settings_after_id") and self._save_settings_after_id:
            try:
                self.after_cancel(self._save_settings_after_id)
            except Exception:
                pass
            self._save_settings_after_id = None
        self._flush_settings()
        self._save_session_snapshot()
        self.destroy()

    def _on_tree_double_click(self, event):
        region = self.tree.identify_region(event.x, event.y)
        if region == "heading":
            return  # headings handled separately via _on_heading_press
        sel = self.tree.selection()
        if not sel: return
        if "toggle_row" in self.tree.item(sel[0], "tags"):
            self._secondary_expanded = not self._secondary_expanded
            self._refresh_tree(); return
        self._do_load(close_after=self._settings.get("close_on_dbl_click", True))

    # ── cell truncation tooltip ───────────────────────────────────────────────

    def _setup_cell_tooltip(self):
        """Show a tooltip with the full cell text when the text is truncated by the column width.
        Only shown when content is actually cut off; no tooltip when the full text fits."""
        self._cell_tip_win  = None   # active tooltip Toplevel (or None)
        self._cell_tip_id   = None   # pending after() handle
        self._cell_tip_key  = None   # (row_iid, col_id) currently shown

        # Measure font once — matches the Treeview row font set in _apply_settings_to_ui.
        # Re-read each time a tooltip fires so it picks up font-size changes.
        def _font_for_tree():
            fs = self._settings.get("font_size", 9)
            try:
                import tkinter.font as _tkfont
                return _tkfont.Font(family=_FONT_UI, size=fs)
            except Exception:
                return None

        def _cancel_pending():
            if self._cell_tip_id:
                self.tree.after_cancel(self._cell_tip_id)
                self._cell_tip_id = None

        def _hide_tip():
            _cancel_pending()
            if self._cell_tip_win:
                try:
                    self._cell_tip_win.destroy()
                except Exception:
                    pass
                self._cell_tip_win = None
            self._cell_tip_key = None

        def _show_tip(text, rx, ry):
            _hide_tip()
            win = tk.Toplevel(self.tree)
            win.overrideredirect(True)
            win.attributes("-topmost", True)
            bg  = C.get("card",   "#101828")
            fg  = C.get("text",   "#ccd6f6")
            bdr = C.get("accent", "#4d9de0")
            outer = tk.Frame(win, bg=bdr, bd=1)
            outer.pack(fill="both", expand=True)
            tk.Label(outer, text=text, bg=bg, fg=fg,
                     font=(_FONT_UI, self._settings.get("font_size", 9)),
                     padx=6, pady=3, relief="flat").pack()
            win.update_idletasks()
            tw = win.winfo_reqwidth()
            th = win.winfo_reqheight()
            _max_w, _max_h = win.wm_maxsize()
            sx = _max_w if _max_w > 0 else self.tree.winfo_screenwidth()
            sy = _max_h if _max_h > 0 else self.tree.winfo_screenheight()
            x  = min(rx + 12, sx - tw - 4)
            y  = ry + 16
            if y + th > sy:
                y = ry - th - 4
            win.geometry("+{}+{}".format(x, y))
            self._cell_tip_win = win

        # Map column id → attribute name on Sub.
        # NOTE: _COL_ATTR is defined for all columns but the tooltip handler below
        # only fires for col_id == "release" (early return on line ~6515).
        # Keeping it here for potential future per-column tooltip expansion.
        _COL_ATTR = {"score": None, "release": "release", "language": "language",
                     "provider": "provider", "fmt": "fmt"}

        def _on_motion(event):
            # Ignore heading row — tooltip only for data cells
            if self.tree.identify_region(event.x, event.y) != "cell":
                _hide_tip(); return
            # Identify cell under pointer
            row_iid = self.tree.identify_row(event.y)
            col_num  = self.tree.identify_column(event.x)   # '#1', '#2', ...
            if not row_iid or not col_num:
                _hide_tip(); return

            # Map column number to id
            try:
                col_idx = int(col_num.lstrip("#")) - 1
                _dc = self.tree.cget("displaycolumns")
                displayed = list(_dc) if not isinstance(_dc, str) else [_dc]
                if displayed == ["#all"]:
                    displayed = [c for c, *_ in self.COLUMNS]
                if col_idx < 0 or col_idx >= len(displayed):
                    _hide_tip(); return
                col_id = displayed[col_idx]
            except Exception:
                _hide_tip(); return

            key = (row_iid, col_id)
            if key == self._cell_tip_key:
                return  # already showing tip for this cell — nothing to do

            # Get the text that was placed in this cell
            try:
                vals = self.tree.item(row_iid, "values")
                # values tuple matches display column order
                cell_text = vals[col_idx] if col_idx < len(vals) else ""
                cell_text = str(cell_text)
            except Exception:
                _hide_tip(); return

            if col_id != "release":
                _hide_tip(); return

            # Measure text width vs column width
            try:
                col_width = self.tree.column(col_id, "width")
                font = _font_for_tree()
                text_px = font.measure(cell_text) if font else len(cell_text) * 7
                # Add a small margin for cell padding (typically ~6px each side)
                fits = (text_px + 14) <= col_width
            except Exception:
                _hide_tip(); return

            if fits:
                # Text is not cut off — hide any existing tip and do nothing
                _hide_tip()
                return

            # Text is truncated — schedule tooltip
            _cancel_pending()
            rx = event.x_root
            ry = event.y_root
            self._cell_tip_key = key
            self._cell_tip_id  = self.tree.after(
                500, lambda: _show_tip(cell_text, rx, ry))

        def _on_leave(_event=None):
            _hide_tip()

        self.tree.bind("<Motion>",  _on_motion,  add="+")
        self.tree.bind("<Leave>",   _on_leave,   add="+")
        self.tree.bind("<Button-1>", lambda _e: _hide_tip(), add="+")
        self.tree.bind("<Button-3>", lambda _e: _hide_tip(), add="+")

    # ── column drag-reorder ───────────────────────────────────────────────────

    def _col_id_at(self, x):
        """Return the column id under the given x-coordinate in the heading row, or ''."""
        try:
            col = self.tree.identify_column(x)          # e.g. '#1', '#2' …
            if not col: return ""
            col_idx = int(col.lstrip("#")) - 1          # 0-based
            _dc = self.tree.cget("displaycolumns")
            # cget may return a string "#all", a tuple ("#all",), or a tuple of col ids
            # depending on the Tkinter version — normalise to a list in all cases.
            if isinstance(_dc, str):
                displayed = [_dc]
            else:
                displayed = list(_dc)
            if displayed == ["#all"]:
                displayed = [c for c,*_ in self.COLUMNS]
            if 0 <= col_idx < len(displayed):
                return displayed[col_idx]
        except Exception:
            pass
        return ""

    def _on_heading_press(self, event):
        """Single press — if on a heading, start tracking for a potential column drag."""
        region = self.tree.identify_region(event.x, event.y)
        if region != "heading":
            # Row or cell click — just reset drag state silently, don't consume event
            self._col_drag_source = None
            self._col_drag_active = False
            self._col_drag_press_x = 0
            return
        cid = self._col_id_at(event.x)
        if not cid:
            return
        self._col_drag_source = cid
        self._col_drag_active = False   # not yet active — need to move first
        self._col_drag_press_x = event.x

    def _on_col_drag_motion(self, event):
        """Motion with button-1 held — activate drag if moved enough from press point."""
        if not self._col_drag_source:
            return
        # Activate drag mode after moving at least 8px horizontally
        if not self._col_drag_active:
            if abs(event.x - getattr(self, "_col_drag_press_x", event.x)) >= 8:
                self._col_drag_active = True
            else:
                return

        # Highlight the target heading
        region = self.tree.identify_region(event.x, event.y)
        target = self._col_id_at(event.x) if region == "heading" else ""
        is_valid_target = bool(target and target != self._col_drag_source)

        # Update heading text: mark source with [ ], target with ← arrow.
        # Non-dragged columns keep their sort arrow if one is currently active.
        _arrow = {"asc": " \u25b2", "desc": " \u25bc"}.get(
            self._col_sort_state.get(self._active_sort_col, ""), "")
        for cid, _, head, _, _anc in self.COLUMNS:
            if cid == self._col_drag_source:
                self.tree.heading(cid, text="[ {} ]".format(head))
            elif cid == target and is_valid_target:
                self.tree.heading(cid, text="\u2190 {}".format(head))
            else:
                # Preserve the sort arrow on whichever column is currently sorted
                suffix = _arrow if cid == self._active_sort_col else ""
                self.tree.heading(cid, text=head + suffix)

        self._drag_target_col = target if is_valid_target else ""
        self.tree.config(cursor="fleur" if not is_valid_target else "exchange")

    def _on_col_drag_release(self, event):
        """On button release, move column if we were in drag mode."""
        if not self._col_drag_active or not self._col_drag_source:
            self._col_drag_cancel()
            return
        # Save source before cancel resets it
        src = self._col_drag_source
        self._col_drag_cancel()
        region = self.tree.identify_region(event.x, event.y)
        if region != "heading":
            return
        target = self._col_id_at(event.x)
        if not target or target == src:
            return
        # Reorder col_order in settings
        order = list(self._settings.get("col_order", [c for c,*_ in self.COLUMNS]))
        if src not in order or target not in order:
            return
        src_i = order.index(src)
        tgt_i = order.index(target)
        order.remove(src)
        # After removing src, recalculate target index
        tgt_i_new = order.index(target)
        if src_i < tgt_i:
            # Moving right: insert after target
            order.insert(tgt_i_new + 1, src)
        else:
            # Moving left: insert before target
            order.insert(tgt_i_new, src)
        self._settings["col_order"] = order
        self._save_settings()
        self._apply_settings_to_ui()
        log.debug("col reorder: %s → %s  result: %s", src, target, order)

    def _col_drag_cancel(self):
        self._col_drag_active = False
        self._col_drag_source = None
        self._col_drag_press_x = 0
        self._drag_target_col = ""
        self.tree.config(cursor="")
        active_dir = self._col_sort_state.get(self._active_sort_col, "")
        self._update_heading_arrows(self._active_sort_col, active_dir if active_dir != "none" else "")
        if self._col_drag_after:
            try: self.after_cancel(self._col_drag_after)
            except Exception: pass
            self._col_drag_after = None

    def _show_cached_packs(self):
        """Display season pack results on startup without touching the session cache."""
        n, ns = len(self.results), len(self.secondary_results)
        total = n + ns
        self.status_var.set("{} subtitle{} found".format(total, "s" if total != 1 else ""))
        self.count_var.set("{} results  +  {} more".format(n, ns) if ns else "{} results".format(n))
        self._refresh_tree()
        children = self.tree.get_children()
        if children:
            self.tree.focus(children[0])
            self.tree.selection_set(children[0])

    def _on_start(self):
        # Restore cached downloads
        idx = _load_cache_index()
        self._last_dl_path.update(idx)

        if self.video_path:
            # For URLs extract the real filename instead of showing a UUID
            if _URL_SCHEME_RE.match(self.video_path):
                _fn = re.search(r"[?&]filename=([^&]+)", self.video_path)
                if _fn:
                    _display = Path(urllib.parse.unquote(_fn.group(1))).name
                else:
                    _display = self.video_path.split("?")[0].rstrip("/").split("/")[-1]
            else:
                _display = Path(self.video_path).name
            self.status_var.set("\u25B6  {}".format(_display))

            # ── Query resolution — reliability first, then speed, then last resort
            #
            # Priority for URLs:
            #   1. &filename= in URL           — most reliable (full release name), instant
            #   2. IPC pipe "path" property    — same URL mpv is playing, likely has &filename=, free
            #   3. Content-Disposition header  — reliable CDN-provided release name, costs one HEAD req
            #   4. URL path segment heuristic  — free/instant but unreliable (UUIDs, garbled segments)
            #   5. IPC pipe media-title        — free/instant but rarely has S/E info
            #
            # For local files: clean_filename() is definitive; pipe title only if that gives nothing.
            #
            # At every step: a result WITH S/E info (SxxExx) wins over one without,
            # so a human episode title like "Number 2 with a Bullet" never silently
            # beats a proper release filename.

            q = ""
            _best_no_se = ""   # best result found so far that lacks S/E info, kept as fallback

            def _accept(candidate, source):
                """Return True and update q/_best_no_se if candidate is an improvement."""
                nonlocal q, _best_no_se
                if not candidate:
                    return False
                if _RE_SXEX.search(candidate):
                    q = candidate
                    log.debug("query from %s (has S/E): %r", source, q)
                    return True          # S/E found — stop searching
                if not _best_no_se:
                    _best_no_se = candidate
                    log.debug("query from %s (no S/E, kept as fallback): %r", source, candidate)
                return False

            if _URL_SCHEME_RE.match(self.video_path):
                # 1. &filename= in the URL
                if not q:
                    _fn_match = re.search(r"[?&]filename=([^&]+)", self.video_path)
                    if _fn_match:
                        _accept(clean_filename(urllib.parse.unquote(_fn_match.group(1))), "&filename=")

                # 2. IPC pipe "path" — same URL mpv holds, may have &filename= even if CLI arg didn't
                #    Uses _ipc_command so it works on both Windows (named pipe) and Unix (socket).
                if not q:
                    _pr = _ipc_command(["get_property", "path"])
                    if _pr is not None:
                        _pipe_path = _pr.get("data", "")
                        if _pipe_path and _pipe_path != self.video_path:
                            _pm = re.search(r"[?&]filename=([^&]+)", _pipe_path)
                            if _pm:
                                _accept(clean_filename(urllib.parse.unquote(_pm.group(1))), "pipe path &filename=")
                            if not q:
                                _accept(clean_filename(_pipe_path), "pipe path heuristic")

                # 3. Content-Disposition header — reliable but costs a network round-trip.
                # Use a lightweight persistent cache keyed by URL content key so we
                # never re-fetch the same URL's filename on subsequent launches.
                if not q:
                    _url_ck = _content_key(self.video_path)
                    _cd_cache_file = SESSION_CACHE_FILE.parent / "cd_cache.json"
                    _cached_hdr = ""
                    try:
                        if _cd_cache_file.exists():
                            _cd_data = json.loads(_cd_cache_file.read_text(encoding="utf-8"))
                            _cached_hdr = _cd_data.get(_url_ck, "") or _cd_data.get(self.video_path, "")
                    except Exception:
                        pass
                    if _cached_hdr:
                        log.debug("Content-Disposition: using cached value %r", _cached_hdr)
                        _accept(clean_filename(_cached_hdr), "Content-Disposition header (cached)")
                    else:
                        hdr_name = get_filename_from_headers(self.video_path)
                        if hdr_name:
                            self._cd_filename = hdr_name
                            self._cd_url_ck   = _url_ck
                            self._cd_cache_file = _cd_cache_file
                            _accept(clean_filename(hdr_name), "Content-Disposition header")

                # 4. URL path segment heuristic — free/instant but unreliable
                if not q:
                    _accept(clean_filename(self.video_path), "URL path heuristic")

                # 5. IPC pipe media-title — rarely has S/E but better than nothing
                if not q:
                    mpv_title = get_mpv_title()
                    if mpv_title:
                        _accept(clean_title(mpv_title), "media-title")

                # Use best non-S/E fallback if nothing with S/E was found
                if not q and _best_no_se:
                    q = _best_no_se
                    log.debug("query: using best non-S/E fallback: %r", q)

            else:
                # Local file — filename is definitive
                q = clean_filename(self.video_path)
                # Pipe title only if filename gave nothing at all
                if not q:
                    mpv_title = get_mpv_title()
                    if mpv_title:
                        q = clean_title(mpv_title)
                        log.debug("query from media-title (local file fallback): %r", q)
        else:
            q = ""
        self.q_var.set(q)

        # ── Beat-mpv retry: if we got nothing, poll until mpv sets media-title ──
        # When SubFinder opens before (or at the same time as) mpv finishes loading
        # a file, get_mpv_title() returns "" because the IPC pipe isn't ready yet.
        # This background poller retries up to 10 times at 1s intervals and updates
        # the search box as soon as mpv has a title — but only if the user hasn't
        # typed anything manually in the meantime.
        if not q and self.video_path:
            _initial_q_for_retry = q  # "" at this point

            def _retry_get_title(attempt: int = 0) -> None:
                # Stop if the user has typed something
                if self.q_var.get().strip() != _initial_q_for_retry:
                    return
                mpv_title = get_mpv_title()
                if mpv_title:
                    resolved = clean_title(mpv_title)
                    if resolved:
                        log.debug("beat-mpv retry #%d: resolved %r", attempt, resolved)
                        self.q_var.set(resolved)
                        return
                if attempt < 9:
                    self.after(1000, _retry_get_title, attempt + 1)
                else:
                    log.debug("beat-mpv retry: exhausted 10 attempts, giving up")

            self.after(500, _retry_get_title, 0)

        # Update the status bar now that we have the best possible display name.
        # The initial set at startup used the raw URL segment (e.g. "download.aspx");
        # if Content-Disposition or another source resolved a real name, show that instead.
        if self.video_path and _URL_SCHEME_RE.match(self.video_path) and q:
            self.status_var.set("\u25B6  {}".format(q))

        # Persist Content-Disposition filename immediately so next launch is instant.
        # Uses the same atomic write pattern as every other cache write in this
        # codebase (write to .tmp, then rename) so a crash mid-write cannot corrupt
        # the cache file.
        if hasattr(self, "_cd_filename") and self._cd_filename:
            try:
                _cd_data = {}
                if self._cd_cache_file.exists():
                    _cd_data = json.loads(self._cd_cache_file.read_text(encoding="utf-8"))
                _cd_data[self._cd_url_ck] = self._cd_filename
                _cd_tmp = self._cd_cache_file.with_suffix(".tmp")
                _cd_tmp.write_text(json.dumps(_cd_data, ensure_ascii=False, indent=2),
                                   encoding="utf-8")
                _cd_tmp.replace(self._cd_cache_file)
                log.debug("Content-Disposition cached: %r → %r", self._cd_url_ck, self._cd_filename)
            except Exception as e:
                log.warning("Could not write cd_cache: %s", e)
                try:
                    # Clean up any partial .tmp file left by the failed atomic write.
                    self._cd_cache_file.with_suffix(".tmp").unlink(missing_ok=True)
                except Exception:
                    pass

        loaded_from_cache = False
        if self.video_path and self.video_path.strip():
            try:
                sessions = _load_session_cache()
                # Use the resolved query (show name) as the cache key when available —
                # this makes the cache URL-agnostic for signed/expiring URLs where
                # Content-Disposition is the only stable identifier.
                _ck = q.lower().strip() if q and q.strip() else _content_key(self.video_path)
                # Normalize local path for legacy lookup: resolve, lowercase, forward slashes.
                _norm_vp = (str(Path(self.video_path).resolve()).lower().replace("\\", "/")
                            if self.video_path and not _URL_SCHEME_RE.match(self.video_path)
                            else self.video_path)
                # Fall back to content_key, normalized path, and raw path for legacy entries.
                session = (sessions.get(_ck)
                           or sessions.get(_content_key(self.video_path))
                           or sessions.get(_norm_vp)
                           or sessions.get(self.video_path))
                if session:
                    self.results = session.get("results", [])
                    self.secondary_results = session.get("secondary_results", [])
                    _restored_q = session.get("query", q)
                    self.q_var.set(_restored_q)
                    self.lang_var.set(session.get("lang", self.lang_var.get()))
                    self._multi_lang_search = session.get("multi_lang", False)
                    # Restore which subtitle was loaded into mpv so "Remove from mpv"
                    # shows correctly after a window close/reopen.
                    # Verify the sub_id still exists in the current results before
                    # restoring — prevents phantom "Remove" entries for subs that were
                    # deleted from cache between sessions.
                    _all_ids = {s.sub_id for s in self.results + self.secondary_results}
                    _saved_primary = session.get("mpv_primary_sub_id", "")
                    _saved_secondary = session.get("mpv_secondary_sub_id", "")
                    if _saved_primary and _saved_primary in _all_ids:
                        self._mpv_primary_sub_id = _saved_primary
                    if _saved_secondary and _saved_secondary in _all_ids:
                        self._mpv_secondary_sub_id = _saved_secondary
                    # Restore mpv track ID maps so Remove from mpv works after reopen.
                    # Keys are sub_id strings; values are integer mpv track IDs.
                    # Guard: only restore entries whose sub_id is still in current results.
                    _saved_psids = session.get("mpv_primary_sids", {})
                    _saved_ssids = session.get("mpv_secondary_sids", {})
                    self._mpv_primary_sids = {
                        k: v for k, v in _saved_psids.items() if k in _all_ids
                    }
                    self._mpv_secondary_sids = {
                        k: v for k, v in _saved_ssids.items() if k in _all_ids
                    }
                    loaded_from_cache = True
                    log.info("Loaded previous search session from cache.")
            except Exception as e:
                log.warning("Could not load session cache: %s — deleting corrupt file", e)
                SESSION_CACHE_FILE.unlink(missing_ok=True)

        # Always check for cached season packs and merge them into whatever
        # results we already have — whether from session cache or empty.
        # This way season packs show alongside search results, and survive
        # after mpv restarts since the zip is re-downloaded if missing.
        if loaded_from_cache:
            self.after(0, self._show_cached_packs)
        elif q and self._settings.get("auto_search", False):
            self.after(200, self._start_search)

        # Run season-pack discovery in a background thread — find_cached_season_packs
        # may re-download a missing archive over the network (synchronous HTTP, up to
        # 30 s timeout), which would freeze the UI if called directly here on the main
        # thread.  The worker merges any found packs and schedules _show_cached_packs
        # on the main thread when done.
        if self.video_path:
            _snap_results   = list(self.results)
            _snap_secondary = list(self.secondary_results)

            def _season_pack_worker():
                cached_packs = find_cached_season_packs(self.video_path)
                if not cached_packs:
                    return
                log.info("Merging %d cached season pack result(s) into results", len(cached_packs))
                existing_ids = {s.sub_id for s in _snap_results + _snap_secondary}
                oscom_enabled = self._settings.get("provider_subliminal", False)
                # For season pack merges, check if current primary results contain
                # any direct results — if so, direct_ok=True so subliminal packs
                # are also excluded here for consistency.
                direct_ok = any(s.provider == "opensubtitlescom_direct"
                                for s in _snap_results)
                PRIMARY = _primary_providers(oscom_enabled, direct_ok=direct_ok)
                new_primary, new_secondary = [], []
                for s in cached_packs:
                    if s.sub_id not in existing_ids:
                        if s.provider in PRIMARY:
                            new_primary.append(s)
                        else:
                            new_secondary.append(s)
                if new_primary or new_secondary:
                    self.after(0, _merge_season_packs, new_primary, new_secondary)

            def _merge_season_packs(new_primary, new_secondary):
                existing_ids = {s.sub_id for s in self.results + self.secondary_results}
                for s in new_primary:
                    if s.sub_id not in existing_ids:
                        self.results.append(s)
                for s in new_secondary:
                    if s.sub_id not in existing_ids:
                        self.secondary_results.append(s)
                self._show_cached_packs()

            threading.Thread(target=_season_pack_worker, daemon=True, name="subfinder-season-pack").start()

    # ── readme / help ─────────────────────────────────────────────────────────

    def _open_readme(self):
        if self._help_win and self._help_win.winfo_exists():
            self._help_win.lift(); self._help_win.focus_set(); return
        win = tk.Toplevel(self)
        self._help_win = win
        win.title("Help")
        win.configure(bg=C["bg"])
        win.resizable(True, True)
        _help_geo = self._settings.get("help_win_geometry", "")
        win.geometry(_help_geo if _help_geo else "700x560")
        self._clamp_window_to_screen(win)
        def _help_save_and_close():
            self._settings["help_win_geometry"] = win.geometry()
            self._save_settings()
            win.destroy()
        win.protocol("WM_DELETE_WINDOW", _help_save_and_close)

        top_bar = ttk.Frame(win)
        top_bar.pack(fill="x", padx=22, pady=(13, 0))
        tk.Label(top_bar, text="", font=(_FONT_EMOJI,22),
                 bg=C["bg"], fg=C["text"]).pack(side="left", padx=(0,10))
        ttk.Label(top_bar, text="SubFinder", style="Head.TLabel").pack(side="left", pady=(0,9))
        tk.Frame(win, bg=C["border"], height=1).pack(fill="x", pady=(6, 0))

        txt = tk.Text(
            win, bg=C["surface"], fg=C["text"],
            font=(_FONT_UI, 10), wrap="word", relief="flat",
            bd=0, state="normal", padx=20, pady=14,
            cursor="arrow",
        )
        sb = ttk.Scrollbar(win, orient="vertical", command=txt.yview)
        txt.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        txt.pack(fill="both", expand=True)

        # ── Tags ───────────────────────────────────────────────────────────
        # Layout constants
        _BUL  = 20   # lmargin1: left edge where bullet glyph sits
        _WRAP = 34   # lmargin2: where wrapped bullet-line text continues

        # Compute the tab stop dynamically: measure every kv key at the actual
        # kk font size, take the widest, then add a fixed gap for breathing room.
        # This ensures the value column always sits just past the longest key —
        # no wasted space, no overflow.
        _kk_font = tkinter.font.Font(family=_FONT_UI, size=9)
        _ALL_KV_KEYS = [
            # Keyboard shortcuts
            "Ctrl+S", "Enter", "Double-click", "Alt+F4", "Up / Down",
            # Searching
            "Run a search:", "Stop:", "Language:", "Sort:", "Columns:", "Score:",
            # Right-Click on Empty Area
            "Add Subtitle File…:", "Extract Current Subtitle:", "Extract All Subtitles:",
            # Providers
            "OpenSubtitles.com:", "SubDL:",
            # Settings
            "Auto-search:", "Double-click closes:", "Lock window size:", "Remember position:",
            "Theme:", "Row height / Font:", "Providers:", "API keys:",
            "OS.com gear (⚙):", "Gemini translation:", "  API KEYS:", "  MODEL CHAIN:",
            "  BLOCKS PER REQUEST:", "Clear All Caches:",
            # Warning Banners
            "subliminal not installed:", "ffsubsync not installed:",
            "pysubs2 not installed:", "ffmpeg not installed:",
            "pywin32 not installed:",
            # Right-Click Menu
            "Load as Primary / Secondary:", "Remove Primary / Secondary:",
            "Show in Explorer:", "Copy File Path / URL / Release:",
            "Translate to…:", "Strip HI / SDH annotations:",
            "Auto sync (ffsubsync/alass):", "Delete from Cache:", "Remove from List:",
            # File Locations
            "Script:", "Logs:", "Config:", "Cache & index:", "Temp archives:", "Log file:",
        ]
        # lmargin1=8 for kk + "  " prefix (2 spaces measured at kk font)
        _kk_prefix_w = 8 + _kk_font.measure("  ")
        _KV_V = max(_kk_prefix_w + _kk_font.measure(k) for k in _ALL_KV_KEYS) + 14

        txt.configure(tabs=(_KV_V,))

        # Section headings
        txt.tag_configure("h1",
            font=(_FONT_UI, 12, "bold"), foreground=C["accent"],
            spacing1=18, spacing3=6)
        txt.tag_configure("h2",
            font=(_FONT_UI, 10, "bold"), foreground=C["text"],
            spacing1=12, spacing3=3)

        # Regular paragraph / body text
        txt.tag_configure("body", font=(_FONT_UI, 10), foreground=C["text"])

        # Bullet-line base tags — carry lmargin so wrapped lines indent correctly.
        txt.tag_configure("bul",
            font=(_FONT_UI, 10), foreground=C["text"],
            lmargin1=_BUL, lmargin2=_WRAP, spacing1=2, spacing3=2)
        txt.tag_configure("bul_ok",
            font=(_FONT_UI, 10), foreground=C["green"],
            lmargin1=_BUL, lmargin2=_WRAP, spacing1=2, spacing3=2)
        txt.tag_configure("bul_warn",
            font=(_FONT_UI, 10), foreground=C["yellow"],
            lmargin1=_BUL, lmargin2=_WRAP, spacing1=2, spacing3=2)

        # Inline colour overrides (no margins — layered on top of bul / body tags)
        txt.tag_configure("c_warn",  foreground=C["yellow"])
        txt.tag_configure("c_green", foreground=C["green"])

        # UI element references — bold accent, same size as body. Google style guide standard:
        # names of buttons/menus/items in bold, no brackets, no font size change.
        txt.tag_configure("c_ui",
            font=(_FONT_UI, 10, "bold"), foreground=C["accent"])

        # Inline code: monospace + accent colour (no background — keeps selection highlight visible)
        txt.tag_configure("c_code",
            font=(_FONT_MONO, 9), foreground=C["accent"])

        # kv rows: dim key, tab-aligned value
        txt.tag_configure("kk",
            font=(_FONT_UI, 9), foreground=C["dim"],
            lmargin1=8, lmargin2=8)
        txt.tag_configure("kv",
            font=(_FONT_UI, 10), foreground=C["text"],
            lmargin1=_KV_V, lmargin2=_KV_V)
        txt.tag_configure("kv_warn",
            font=(_FONT_UI, 10), foreground=C["yellow"],
            lmargin1=_KV_V, lmargin2=_KV_V)
        # Combined tags: monospace+accent colour WITH correct kv wrap-indent.
        # Used by _kv() for _code() spans so lmargin2 is never lost on wrap.
        txt.tag_configure("kv_code",
            font=(_FONT_MONO, 9), foreground=C["accent"],
            lmargin1=_KV_V, lmargin2=_KV_V)
        txt.tag_configure("kv_warn_code",
            font=(_FONT_MONO, 9), foreground=C["accent"],
            lmargin1=_KV_V, lmargin2=_KV_V)

        txt.tag_configure("dim", font=(_FONT_UI, 9), foreground=C["dim"])
        txt.tag_configure("sep", font=(_FONT_UI, 2), foreground=C["border"],
                          spacing1=6, spacing3=8)

        # ── Helper functions ───────────────────────────────────────────────

        def _h1(t):
            txt.insert("end", t + "\n", "h1")

        def _h2(t):
            txt.insert("end", t + "\n", "h2")

        def _blank():
            txt.insert("end", "\n")

        def _sep():
            txt.insert("end", "─" * 80 + "\n", "sep")

        def _ui(label):
            """Inline UI reference — button, menu item, dropdown, key.
            Accent bold size-11, no brackets."""
            return (label, "c_ui")

        def _code(label):
            """Inline monospace code span."""
            return (label, "c_code")

        def _warn(label):
            """Inline warning-colour span."""
            return (label, "c_warn")

        def _p(*parts):
            """Paragraph: plain strings or (text, tag) tuples."""
            for part in parts:
                if isinstance(part, tuple):
                    txt.insert("end", part[0], part[1])
                else:
                    txt.insert("end", part, "body")
            txt.insert("end", "\n")

        def _ind(*parts, tag="bul"):
            """Bullet line. All text inserted under `tag` for correct lmargin;
            inline colour spans are layered on top via tag_add afterwards."""
            txt.insert("end", "•  ", tag)
            spans = []
            for part in parts:
                if isinstance(part, tuple):
                    s = txt.index("end-1c")
                    txt.insert("end", part[0], tag)
                    spans.append((s, txt.index("end-1c"), part[1]))
                else:
                    txt.insert("end", part, tag)
            txt.insert("end", "\n")
            for s, e, inline_tag in spans:
                txt.tag_add(inline_tag, s, e)

        def _kv(k, *parts, vt=""):
            """Key-value row using a tab stop for pixel-accurate alignment.
            Parts may be plain strings or (text, tag) tuples for inline styling."""
            txt.insert("end", "  " + k, "kk")
            txt.insert("end", "\t", "kk")
            base = "kv_warn" if vt == "warn" else "kv"
            for part in parts:
                if isinstance(part, tuple):
                    text, inline_tag = part
                    # For c_code spans use a dedicated combined tag that carries
                    # both the monospace font/accent colour AND the correct lmargin2.
                    # This avoids tag_raise (which wiped lmargin2) and the tuple-tag
                    # approach (which lost the theme colour due to tag priority order).
                    if inline_tag == "c_code":
                        resolved = "kv_warn_code" if vt == "warn" else "kv_code"
                    else:
                        resolved = inline_tag
                    txt.insert("end", text, resolved)
                else:
                    txt.insert("end", part, base)
            txt.insert("end", "\n")

        # ── Keyboard Shortcuts ─────────────────────────────────────────────
        _h1("Keyboard Shortcuts")
        _kv("Ctrl+S",       "Open SubFinder.")
        _kv("Enter",        "In search box: run a search. In results list: load selected subtitle.")
        _kv("Double-click", "Load subtitle (optionally closes the window \u2014 see Settings).")
        _kv("Alt+F4",       "Close the SubFinder window.")
        _kv("Up / Down",    "Navigate the results list.")
        _sep()

        # \u2500\u2500 Searching \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500
        _h1("Searching")
        _p("The search box is pre-filled automatically from the video. SubFinder tries "
           "several sources in order: the ", _code("&filename="), " parameter in the URL, "
           "the mpv IPC path, a Content-Disposition header (one lightweight HEAD request), "
           "a URL path segment heuristic, and finally the mpv media title. A result with "
           "a season/episode tag (", _code("S01E05"), ") always wins over one without.")
        _blank()
        _kv("Run a search:",  "Type a title and press Enter, or click ", _ui("\ue1a3"), ".")
        _kv("Stop:",          "Click ", _ui("\u25a0"), " to cancel a search in progress.")
        _kv("Language:",      "Click the ", _ui("Language"), " dropdown and check one or more "
                              "languages. All checked languages are searched in a single pass.")
        _kv("Sort:",          "Use the ", _ui("Sort by"), " dropdown to order results by "
                              "Score, Language, Format, Provider, or Release. "
                              "Clicking a column heading also sorts and toggles asc/desc.")
        _kv("Columns:",       "Drag any column heading left or right to reorder.")
        _kv("Score:",         "Match quality 0\u2013100\u202f%. "
                              "99\u202f% = byte-exact hash match (best). Lower = query-matched.")
        _blank()
        _p("Primary results appear in the main list. Secondary / fallback results sit below "
           "a ", _ui("\u25ba  N more results"), " toggle row. Click it to expand or collapse.")
        _sep()

        # \u2500\u2500 Loading \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500
        _h1("Loading Subtitles")
        _p("Downloaded subtitles are cached on disk. Cached rows are highlighted "
           "and load instantly \u2014 no re-download needed.")
        _blank()
        _p("Double-click a row, or select it and press Enter or click ",
           _ui("\ue118"), " to load it into mpv as the primary subtitle.")
        _p("Right-click any row and choose ", _ui("Load as Secondary Subtitle"),
           " to load a second subtitle track simultaneously (e.g. for dual-language display).")
        _blank()
        _p("Once a subtitle is loaded into mpv its row is highlighted in ",
           _warn("accent colour"), ". Right-clicking it then shows ",
           _ui("Remove Primary from mpv"), " or ", _ui("Remove Secondary from mpv"),
           " instead of Load. This state is saved and restored when you reopen SubFinder.")
        _blank()
        _p("Click ", _ui("\ue169"), " to toggle the detail panel, which shows the full "
           "release name, provider, format, score, and download URL for the selected row.")
        _blank()
        _p("Right-click any downloaded row to access ", _ui("Show in Explorer"), ", ",
           _ui("Copy File Path"), ", and ", _ui("Copy URL"), ".")
        _p("For locally-added subtitles, right-click shows ",
           _ui("Remove from List"), " (never deletes the file on disk).")
        _p("For embedded subtitles, ", _ui("Delete from Cache"),
           " removes the extracted temp file. For downloaded subtitles it also removes "
           "the season-pack archive and all sibling episode files.")
        _sep()

        # \u2500\u2500 Right-Click on Empty Area \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500
        _h1("Right-Click on Empty Area")
        _p("Right-clicking anywhere in the window that is not a result row "
           "(empty list area, header, or any non-treeview region) opens a small menu:")
        _blank()
        _kv("Add Subtitle File\u2026:", "Browse for any subtitle file on disk and add it "
                                         "to the results list as a local subtitle.")
        _kv("Extract Current Subtitle:", "Extract only the subtitle track currently active "
                                         "in mpv from the local video file.")
        _kv("Extract All Subtitles:",   "Extract every text-based subtitle track from the "
                                         "local video file (SRT, ASS, SSA, VTT). "
                                         "Image-based tracks (PGS, DVD) are not supported.")
        _blank()
        _p("Extract items only appear when a ", _warn("local file"), " (not a streaming URL) "
           "is playing. For HTTP sources, use ", _ui("Extract All Subtitles"),
           " from the row right-click menu instead \u2014 SubFinder uses mpv\u2019s "
           "dump-cache IPC command to write the already-buffered stream to a temp file, "
           "then runs ", _code("ffmpeg"), " on that. Requires ", _code("ffmpeg"), " and the mpv IPC server.")
        _sep()

        # \u2500\u2500 Providers \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500
        _h1("Providers")
        _kv("OpenSubtitles.com:", "Largest subtitle database. Free API key required. "
                                   "Gear (\u2699) button opens username\u202f+\u202fpassword entry "
                                   "for a higher daily download quota.")
        _kv("SubDL:",             "Fast, reliable alternative. Free API key required.")
        _blank()
        _p("When an OS.com API key is configured and the ", _ui("OpenSubtitles"),
           " checkbox is enabled, SubFinder uses the direct REST API as the primary "
           "search path. If it returns no results, ", _code("subliminal"), " (if installed) is tried as "
           "a fallback. With the checkbox ", _warn("unchecked"),
           ", ", _code("subliminal"), " falls back to the legacy provider \u2014 no API key needed for that.")
        _blank()
        _p("Enable providers and paste API keys in ", _ui("\ue115 Settings"), ". "
           "Both OS.com and SubDL can be active at the same time.")
        _sep()

        # \u2500\u2500 Season Packs \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500
        _h1("Season Packs")
        _p("When a SubDL result is a full-season archive (", _code(".zip"), " or ", _code(".rar"), "), SubFinder "
           "extracts the subtitle that best matches the current episode. The archive is "
           "kept on disk so every other episode in that season loads instantly from cache.")
        _blank()
        _ind("ZIP packs work out of the box.", tag="bul_ok")
        _ind("RAR packs require ", _warn("WinRAR or 7-Zip"),
             " to be installed. SubFinder checks the registry and common install paths.",
             tag="bul_warn")
        _blank()
        _p("Cached packs appear on startup before you run a search. Right-click a "
           "downloaded row and choose ", _ui("Delete from Cache"),
           " to remove the pack, all extracted episode files, and all index entries.")
        _sep()

        # \u2500\u2500 Translation \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500
        _h1("Translation")
        _p("Right-click any subtitle row \u2192 ", _ui("Translate to \u2026"),
           ". If the subtitle is already downloaded, translation starts immediately. "
           "If not yet downloaded, SubFinder downloads it first, then translates.")
        _blank()
        _ind("Supports ", _warn(".srt, .ass, .ssa, .vtt"), " formats. "
             "Non-SRT files are converted automatically if ", _code("pysubs2"), " is installed "
             "(", _code("pip install pysubs2"), ").")
        _ind("Requires a Gemini API key \u2014 get one free at ",
             _code("aistudio.google.com"),
             ", then add it in ",
             _ui("\ue115 Settings \u2192 Gemini translation \u2192 Configure (\u2699)"), ".")
        _ind("Multiple API keys are supported. Each key runs as a parallel worker "
             "processing different chunks simultaneously \u2014 more keys = faster translation. "
             "Use a different Google account per key; same-account keys share the same quota pool.")
        _ind("Translated files are cached. Right-clicking the same row again loads "
             "instantly \u2014 no re-translation, no quota usage.")
        _ind("If a model is deprecated by Google, update or remove it in ",
             _ui("\ue115 Settings \u2192 Gemini translation \u2192 Configure (\u2699)"),
             " under MODEL CHAIN.")
        _sep()

        # \u2500\u2500 Settings \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500
        _h1("\ue115 Settings")
        _kv("Auto-search:",          "Run a search automatically when the window opens.")
        _kv("Double-click closes:",  "Close the window after a subtitle is loaded.")
        _kv("Lock window size:",     "Prevent the window from being resized.")
        _kv("Remember position:",    "Restore the last window position on launch.")
        _kv("Theme:",                str(len(THEMES)) + " built-in colour themes.")
        _kv("Row height / Font:",    "Scale the results list to your preference.")
        _kv("Columns:",              "Toggle Score, Release, Language, Provider, and Format "
                                     "on or off. Hiding Language adds a [XX] indicator next "
                                     "to the release name instead.")
        _kv("Providers:",            "Turn OpenSubtitles and / or SubDL on or off.")
        _kv("API keys:",             "Stored locally. Only sent to their respective providers.")
        _kv("OS.com gear (\u2699):", "Enter username\u202f+\u202fpassword for a higher daily quota.")
        _kv("Gemini translation:",   "Badge shows current key count, model count, and chunk "
                                     "size. Click gear (\u2699) to open the configuration popup.")
        _kv("  API KEYS:",           "One key per row. Drag handles to reorder. "
                                     "\u2295 adds a row, \u00d7 removes. "
                                     "Keys are used in parallel during translation.")
        _kv("  MODEL CHAIN:",        "Models are tried top to bottom. On error (", _code("503"), ", timeout, "
                                     "truncation) SubFinder automatically falls back to the "
                                     "next model. Any number of models can be added or removed.")
        _kv("  BLOCKS PER REQUEST:", "Subtitle blocks sent per API call. "
                                     "Lower = safer for flagged content; higher = fewer calls.")
        _kv("Clear All Caches:",     "Deletes all downloads, the index, and the log.", vt="warn")
        _sep()

        # \u2500\u2500 Warning Banners \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500
        _h1("Warning Banners")
        _p("Amber banners appear below the bottom bar when a required dependency is "
           "missing. Each has ", _ui("Hide"), " (session-only) and ",
           _ui("Don\u2019t show again"), " (permanent).")
        _blank()
        _kv("pywin32 not installed:",    "Auto-loading into mpv is disabled (Windows only). "
                                          "Install: ", _code("pip install pywin32"), ".")
        _kv("subliminal not installed:", "Searches that rely on ", _code("subliminal"), " won\u2019t run. "
                                          "Install: ", _code("pip install subliminal"), ".")
        _kv("pysubs2 not installed:",    "Translation of ASS/SSA/VTT files is unavailable. "
                                          "Install: ", _code("pip install pysubs2"), ".")
        _kv("ffsubsync not installed:",  "Auto sync is unavailable. "
                                          "Install: ", _code("pip install ffsubsync"),
                                          ", or download alass from ",
                                          _code("github.com/kaegi/alass"), ".")
        _kv("ffmpeg not installed:",     "Auto sync and embedded subtitle extraction are "
                                          "unavailable. Download from ", _code("ffmpeg.org"), ".")
        _sep()

        # \u2500\u2500 Right-Click Menu Reference \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500
        _h1("Right-Click Menu (on a result row)")
        _kv("Load as Primary / Secondary:",    "Download (if needed) and load into mpv.")
        _kv("Remove Primary / Secondary:",     "Remove the loaded track from mpv via IPC.")
        _kv("Show in Explorer:",               "Open the folder with the file selected.")
        _kv("Copy File Path / URL / Release:", "Copy to clipboard.")
        _kv("Translate to\u2026:",             "Translate to any language via Gemini. "
                                               "Works on both downloaded and not-yet-downloaded rows.")
        _kv("Strip HI / SDH annotations:",    "Remove speaker labels, [sound effects], and "
                                               "\u266a music lines in-place, then reload in mpv. "
                                               "Shown when HI/SDH patterns are detected in the "
                                               "subtitle content or inferred from the release name.")
        _kv("Auto sync (ffsubsync/alass):",   "Correct subtitle timing against the video audio. "
                                               "Works for local files and direct HTTP/HTTPS URLs. "
                                               "For URLs, ", _code("ffmpeg"), " extracts up to 10\u202fmin of audio "
                                               "to a temp WAV; this WAV is cached for 2\u202fhours so "
                                               "subsequent syncs of the same video are near-instant. "
                                               "Live streams (", _code("HLS/DASH"), ") are not supported.")
        _kv("Delete from Cache:",             "Remove the file, archive, and all cache entries.",
                                               vt="warn")
        _kv("Remove from List:",              "Remove a local subtitle from the results list "
                                               "without touching the file on disk.")
        _sep()

        # \u2500\u2500 Troubleshooting \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500
        _h1("Troubleshooting")
        _h2("No results")
        _ind("Make sure at least one provider is configured with a valid API key.")
        _ind("Simplify the query \u2014 remove the year, resolution, and release tags.")
        _ind("Open ", _ui("\ue16d Log"), " for detailed error messages.")
        _blank()
        _h2("Subtitle doesn\u2019t appear in mpv after loading")
        _ind(_code("pywin32"), " is needed for auto-injection on Windows: ",
             _code("pip install pywin32"))
        _ind("Without it a dialog shows the file path \u2014 drag the ", _code(".srt"), " into mpv, "
             "or use mpv\u2019s right-click \u2192 Subtitles \u2192 Load.")
        _blank()
        _h2("\"Remove from mpv\" not showing after reopening SubFinder")
        _ind("SubFinder saves which subtitle was loaded when you close the window and "
             "restores it on reopen. If the saved subtitle is no longer in the results "
             "list (e.g. cache was cleared), the Remove option won\u2019t appear.")
        _blank()
        _h2("Pre-filled search query is wrong or empty")
        _ind("Enable the mpv IPC server so SubFinder can read the media path directly:")
        _ind("Windows \u2014 add ", _code("input-ipc-server=\\\\.\\pipe\\mpvpipe"),
             " to ", _code("mpv.conf"), ", then ", _code("pip install pywin32"))
        _ind("Linux / macOS \u2014 add ", _code("input-ipc-server=/tmp/mpv-socket"),
             " to ", _code("mpv.conf"), ". No extra packages needed.")
        _ind("Restart mpv after editing ", _code("mpv.conf"), ".")
        _blank()
        _h2("Translation times out or fails mid-way")
        _ind("SubFinder automatically falls back to the next model in the chain when "
             "a request times out or the model returns ", _code("503"), ". If all models fail, wait a "
             "few minutes and try again.")
        _ind("Adding a second API key from a different Google account improves resilience "
             "\u2014 configure in ", _ui("\ue115 Settings \u2192 Gemini translation \u2192 Configure (\u2699)"), ".")
        _ind("If a specific model is deprecated, update its name under MODEL CHAIN in "
             "the same popup.")
        _blank()
        _h2("Auto sync takes a long time for streaming URLs")
        _ind(_code("ffmpeg"), " must fetch and index the remote container before extracting audio. "
             "For large ", _code("MKV"), " files this can take several minutes on the first run. "
             "After the first sync the extracted WAV is cached for 2\u202fhours \u2014 "
             "subsequent syncs of the same video start near-instantly.")
        _blank()
        _h2("RAR pack fails to extract")
        _ind("Install ", _warn("WinRAR"), " or ", _warn("7-Zip"), ", then restart mpv.", tag="bul_warn")
        _ind("SubFinder checks the Windows registry and common install paths automatically.")
        _blank()
        _h2("Season pack not appearing for other episodes")
        _ind("The archive must still exist on disk.")
        _ind("The show name must loosely match the video filename.")
        _ind("Open SubFinder \u2014 cached packs appear before you run a search.")
        _blank()
        _h2("subliminal errors")
        _ind("Reinstall: ",
             _code("pip install --upgrade subliminal babelfish dogpile.cache"))
        _ind("Then use ", _ui("Clear All Caches"), " in ", _ui("\ue115 Settings"),
             " to flush a corrupted cache.")
        _blank()
        _h2("Multiple windows opening on rapid Ctrl+S")
        _ind("Fixed. SubFinder now enforces a strict single-instance lock on one TCP "
             "port. Only one window can run at a time.")
        _sep()

        # \u2500\u2500 File Locations \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500
        _h1("File Locations")
        _kv("Script:",         _code(str(SCRIPT_DIR)))
        _kv("Logs:",           _code(str(LOG_DIR)))
        _kv("Config:",         _code(str(CONFIG_DIR)))
        _kv("Cache & index:",  _code(str(CACHE_DIR)))
        _kv("Temp archives:",  _code(str(TEMP_DIR)))
        _kv("Log file:",       _code(str(LOG_FILE)))
        # win.update() pumps the full event loop so the OS maps the window
        # and the Text widget receives a real height before we scroll.
        # Without this, txt.see("1.0") is a no-op on Windows because the
        # widget has zero height at the time of the call.
        win.update()
        txt.see("1.0")
        txt.config(state="disabled")

    # ── log viewer ────────────────────────────────────────────────────────────

    @staticmethod
    def _clamp_window_to_screen(win):
        """Ensure *win* is fully visible on the current screen.

        Call after win.geometry() and win.update_idletasks().  Clamps the +X+Y
        position so the window never appears partially or fully off-screen when
        geometry was saved on a larger or different monitor setup.

        Uses wm_maxsize() as the virtual desktop size proxy — it reports the
        total usable area across all monitors combined, which is a better bound
        than winfo_screenwidth/height (primary-monitor only) on multi-monitor
        setups.
        """
        try:
            win.update_idletasks()
            geo = win.geometry()          # e.g. "900x600+2400+100"
            m = _GEO_RE.match(geo)
            if not m:
                return
            w, h, x, y = int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(4))
            # wm_maxsize() returns the maximum window size Tk permits, which on
            # most platforms reflects the full virtual desktop (all monitors).
            # On most Linux WMs it returns (0, 0) — fall back to winfo_vrootwidth/
            # height which reflects the virtual root (multi-monitor on Linux) before
            # falling all the way back to the single-monitor winfo_screen* values.
            max_w, max_h = win.wm_maxsize()
            if max_w > 0:
                sw = max_w
            else:
                try:
                    sw = win.winfo_vrootwidth()
                    if sw <= 0:
                        sw = win.winfo_screenwidth()
                except Exception:
                    sw = win.winfo_screenwidth()
            if max_h > 0:
                sh = max_h
            else:
                try:
                    sh = win.winfo_vrootheight()
                    if sh <= 0:
                        sh = win.winfo_screenheight()
                except Exception:
                    sh = win.winfo_screenheight()
            x = max(0, min(x, sw - w))
            y = max(0, min(y, sh - h))
            win.geometry("{}x{}+{}+{}".format(w, h, x, y))
        except Exception:
            pass

    def _open_log(self):
        if self._log_win and self._log_win.winfo_exists():
            self._log_win.lift(); self._log_win.focus_set(); return
        win = tk.Toplevel(self)
        self._log_win = win
        win.title("subfinder.log")
        win.configure(bg=C["bg"])
        geo = self._settings.get("log_win_geometry","")
        win.geometry(geo if geo else "900x600")
        self._clamp_window_to_screen(win)
        def _save_and_close():
            self._settings["log_win_geometry"] = win.geometry()
            self._save_settings(); win.destroy()
        # Note: WM_DELETE_WINDOW is set below (after _on_log_close is defined),
        # so that the tail-poll after_id is always cancelled on close.
        top_bar = ttk.Frame(win)
        top_bar.pack(fill="x", padx=22, pady=(8, 0))
        ttk.Label(top_bar, text=str(LOG_FILE), style="Dim.TLabel").pack(side="left")
        _btn_reload = tk.Button(top_bar, text="\ue1cd", bg=C["card"], fg=C["text"],
                                activebackground=C["hover"], activeforeground=C["text"],
                                relief="flat", bd=1,
                                font=(_FONT_UI,8), width=4, height=1,
                                command=lambda: _reload())
        _btn_reload.pack(side="right")
        _btn_clear = tk.Button(top_bar, text="\ue107", bg=C["card"], fg=C["text"],
                               activebackground=C["hover"], activeforeground=C["text"],
                               relief="flat", bd=1,
                               font=(_FONT_UI,8), width=4, height=1,
                               command=lambda: _clear_log())
        _btn_clear.pack(side="right", padx=(0,10))
        _Tooltip(_btn_reload, "Refresh")
        _Tooltip(_btn_clear,  "Clear log")
        tk.Frame(win, bg=C["border"], height=1).pack(fill="x", pady=(8, 0))
        txt = tk.Text(win, bg=C["surface"], fg=C["text"], font=(_FONT_MONO,9),
                      wrap="none", relief="flat", bd=0, state="disabled")
        sb_v = ttk.Scrollbar(win, orient="vertical", command=txt.yview)
        sb_h = ttk.Scrollbar(win, orient="horizontal", command=txt.xview)
        txt.configure(yscrollcommand=sb_v.set, xscrollcommand=sb_h.set)
        sb_v.pack(side="right", fill="y")
        sb_h.pack(side="bottom", fill="x")
        txt.pack(fill="both", expand=True)
        # Live tail state — tracks file offset so only new bytes are appended.
        _tail_state = {"offset": 0, "after_id": None, "user_scrolled": False}

        def _at_bottom():
            """Return True if the scrollbar thumb is at (or very near) the bottom."""
            try:
                pos = txt.yview()
                return pos[1] >= 0.999
            except Exception:
                return True

        def _on_scroll(*_args):
            _tail_state["user_scrolled"] = not _at_bottom()

        txt.configure(yscrollcommand=lambda *a: (sb_v.set(*a), _on_scroll(*a)))

        def _tail_poll():
            """Append only new bytes since last poll; reschedule every 500 ms."""
            if not win.winfo_exists():
                return
            try:
                size = LOG_FILE.stat().st_size if LOG_FILE.exists() else 0
            except OSError:
                size = 0
            cur_offset = _tail_state["offset"]
            # Handle log rotation (file shrank)
            if size < cur_offset:
                cur_offset = 0
                txt.config(state="normal")
                txt.delete("1.0", "end")
                txt.config(state="disabled")
                _tail_state["user_scrolled"] = False
            if size > cur_offset:
                try:
                    with LOG_FILE.open("rb") as fh:
                        fh.seek(cur_offset)
                        new_bytes = fh.read(size - cur_offset)
                    new_text = new_bytes.decode("utf-8", errors="replace")
                    was_at_bottom = not _tail_state["user_scrolled"]
                    txt.config(state="normal")
                    txt.insert("end", new_text)
                    txt.config(state="disabled")
                    if was_at_bottom:
                        txt.see("end")
                    _tail_state["offset"] = size
                except Exception:
                    pass
            _tail_state["after_id"] = win.after(500, _tail_poll)

        def _reload():
            """Manual refresh: reset offset and reload full file."""
            _tail_state["offset"] = 0
            _tail_state["user_scrolled"] = False
            txt.config(state="normal"); txt.delete("1.0", "end")
            try:
                content = LOG_FILE.read_text(encoding="utf-8", errors="replace")
            except Exception:
                content = "(log file not found)"
            txt.insert("end", content); txt.see("end"); txt.config(state="disabled")
            try:
                _tail_state["offset"] = LOG_FILE.stat().st_size if LOG_FILE.exists() else 0
            except OSError:
                _tail_state["offset"] = 0

        def _clear_log():
            try:
                LOG_FILE.write_text("", encoding="utf-8")
                _tail_state["offset"] = 0
                _tail_state["user_scrolled"] = False
                txt.config(state="normal"); txt.delete("1.0", "end"); txt.config(state="disabled")
            except Exception as e:
                messagebox.showerror("Error", "Could not clear: {}".format(e), parent=win)

        def _on_log_close():
            if _tail_state["after_id"]:
                win.after_cancel(_tail_state["after_id"])
                _tail_state["after_id"] = None
            _save_and_close()

        win.protocol("WM_DELETE_WINDOW", _on_log_close)

        _reload()
        # _reload() sets _tail_state["offset"] to the current file size after rendering
        # the full content.  The first _tail_poll() therefore starts from that offset and
        # appends only new lines — it cannot double-read existing content.
        _tail_poll()

    # ── settings dialog ───────────────────────────────────────────────────────

    def _open_settings(self):
        if self._settings_win and self._settings_win.winfo_exists():
            self._settings_win.lift(); self._settings_win.focus_set(); return
        win = tk.Toplevel(self)
        self._settings_win = win
        win.title("Settings")
        win.configure(bg=C["bg"])
        win.resizable(False, False)
        win.grab_set()
        def _save_and_close():
            self._settings["settings_win_geometry"] = win.geometry()
            self._save_settings(); win.destroy()
        win.protocol("WM_DELETE_WINDOW", _save_and_close)

        ttk.Label(win, text="  Settings", style="Head.TLabel").pack(anchor="w", padx=22, pady=(18,2))
        tk.Frame(win, bg=C["border"], height=1).pack(fill="x", pady=(8, 0))
        body = ttk.Frame(win)
        body.pack(fill="both", expand=True, padx=22, pady=14)

        # boolean toggles
        bools = [("auto_search","Auto-search when the window opens"),
                 ("close_on_dbl_click","Close window after double-clicking a subtitle")]
        bool_vars = {}
        for key, label in bools:
            var = tk.BooleanVar(value=self._settings.get(key, False))
            bool_vars[key] = var
            tk.Checkbutton(body, text=label, variable=var, bg=C["bg"], fg=C["text"],
                           activebackground=C["bg"], activeforeground=C["accent"],
                           selectcolor=C["card"], font=(_FONT_UI,10), bd=0, highlightthickness=0
                           ).pack(anchor="w", pady=3)

        # lock resize (inverted: checked = locked, unchecked = free resize)
        _lock_var_raw = tk.BooleanVar(value=not self._settings.get("free_resize", True))
        # free_var is still the canonical name used in _apply() — keep it in sync
        free_var = tk.BooleanVar(value=self._settings.get("free_resize", True))
        def _on_lock_toggle(*_):
            free_var.set(not _lock_var_raw.get())
        _lock_var_raw.trace_add("write", _on_lock_toggle)
        tk.Checkbutton(body, text="Lock window size",
                       variable=_lock_var_raw, bg=C["bg"], fg=C["text"],
                       activebackground=C["bg"], activeforeground=C["accent"],
                       selectcolor=C["card"], font=(_FONT_UI,10), bd=0, highlightthickness=0
                       ).pack(anchor="w", pady=3)

        save_pos_var = tk.BooleanVar(value=self._settings.get("save_position", True))
        tk.Checkbutton(body, text="Remember window position on close",
                       variable=save_pos_var, bg=C["bg"], fg=C["text"],
                       activebackground=C["bg"], activeforeground=C["accent"],
                       selectcolor=C["card"], font=(_FONT_UI,10), bd=0, highlightthickness=0
                       ).pack(anchor="w", pady=3)

        ttk.Separator(body, orient="horizontal").pack(fill="x", pady=(8,6))

        # theme
        tf = ttk.Frame(body); tf.pack(fill="x", pady=4)
        ttk.Label(tf, text="Theme:", style="Dim.TLabel").pack(side="left")
        theme_var = tk.StringVar(value=self._settings.get("theme","Default"))
        theme_combo = ttk.Combobox(tf, textvariable=theme_var, values=list(THEMES.keys()),
                                   state="readonly", width=14)
        theme_combo.pack(side="left", padx=(10,0))

        def _on_theme_select(event):
            self._settings["theme"] = theme_var.get()
            self._save_settings()
            self._apply_theme()  # This updates the global 'C' color dict
            
            # 1. Update the settings window background
            win.configure(bg=C["bg"])

        theme_combo.bind("<<ComboboxSelected>>", _on_theme_select)

        def _clear_all_caches_gui():
            if messagebox.askyesno("Clear All Caches", "Are you sure you want to clear all subtitle caches, downloaded files, and the log?", parent=win):
                try:
                    # ── Disk: primary cache files ─────────────────────────────
                    SESSION_CACHE_FILE.unlink(missing_ok=True)
                    CACHE_INDEX_FILE.unlink(missing_ok=True)
                    # Content-Disposition filename cache — must be wiped so stale
                    # filenames don't survive a full cache clear and keep pre-filling
                    # the search box with wrong titles on the next launch.
                    (CACHE_DIR / "cd_cache.json").unlink(missing_ok=True)
                    # Trigger file — stale trigger could cause phantom auto-loads.
                    TRIGGER_FILE.unlink(missing_ok=True)
                    # Atomic-write temp files left behind by a crash or mid-write close.
                    SESSION_CACHE_FILE.with_suffix(".tmp").unlink(missing_ok=True)
                    CACHE_INDEX_FILE.with_name(CACHE_INDEX_FILE.name + ".writing").unlink(missing_ok=True)

                    # ── Disk: TEMP_DIR (downloaded subtitles, archives, etc.) ─
                    if TEMP_DIR.is_dir():
                        for f in TEMP_DIR.iterdir():
                            if f.is_file():
                                f.unlink(missing_ok=True)

                    # ── Disk: subliminal DBM (all backend suffix variants) ────
                    for _dbm_pat in ("subliminal_cache.dbm", "subliminal_cache.dbm.db",
                                     "subliminal_cache.dbm.bak", "subliminal_cache.dbm.dir",
                                     "subliminal_cache.dbm.dat"):
                        _dbm_f = CACHE_DIR / _dbm_pat
                        if _dbm_f.is_file():
                            _dbm_f.unlink(missing_ok=True)

                    # ── Disk: log file + all rotated backups (.1 / .2 / .3) ──
                    if LOG_FILE.is_file():
                        LOG_FILE.write_text("", encoding="utf-8")
                    for _n in range(1, 5):
                        _rotated = LOG_FILE.with_name(LOG_FILE.name + ".{}".format(_n))
                        _rotated.unlink(missing_ok=True)

                    # ── In-memory: download path map ─────────────────────────
                    self._last_dl_path.clear()

                    # ── In-memory: mpv subtitle tracking ─────────────────────
                    self._mpv_primary_sub_id   = ""
                    self._mpv_secondary_sub_id = ""
                    self._mpv_primary_sids.clear()
                    self._mpv_secondary_sids.clear()

                    # ── In-memory: result rows — clear tree and lists ─────────
                    self.results           = []
                    self.secondary_results = []
                    self._secondary_expanded = False
                    self._tree_tags_dirty    = True
                    self._refresh_tree()
                    self._on_select()

                    # ── In-memory: Gemini model token-limit cache ─────────────
                    _model_token_limit_cache.clear()

                    # ── In-memory: settings cache ─────────────────────────────
                    _settings_cache.clear()

                    # ── In-memory: JWT token — force fresh login on next DL ───
                    # Clearing caches is the common recovery action when downloads
                    # are failing with 403; a stale token would make the very next
                    # attempt fail again without a process restart.
                    with _oscom_jwt_lock:
                        global _oscom_jwt_token, _oscom_jwt_expiry
                        _oscom_jwt_token  = ""
                        _oscom_jwt_expiry = 0.0

                    messagebox.showinfo("Success", "All caches and log cleared.", parent=win)
                except Exception as e:
                    messagebox.showerror("Error", "Could not clear some caches:\n{}".format(e), parent=win)

        ttk.Button(tf, text="Clear All Caches", style="Warn.TButton", command=_clear_all_caches_gui).pack(side="right")

        ttk.Separator(body, orient="horizontal").pack(fill="x", pady=(8,6))

        # column visibility
        ttk.Label(body, text="Columns:",
                  style="Dim.TLabel").pack(anchor="w", pady=(0,4))
        col_labels = {"col_score":"Score","col_release":"Release / Title",
                      "col_provider":"Provider",
                      "col_language":"Language",
                      "col_fmt":"Format"}
        key_to_cid = {"col_score":"score","col_release":"release","col_language":"language",
                      "col_provider":"provider","col_fmt":"fmt"}
        col_vars  = {}
        col_keys  = list(col_labels.keys())
        check_order = [k for k in col_keys if self._settings.get(k, True)]
        def _on_col_toggle(*_):
            for k in list(check_order):
                if not col_vars[k].get(): check_order.remove(k)
            for k in col_keys:
                if col_vars[k].get() and k not in check_order: check_order.append(k)
        cf = ttk.Frame(body); cf.pack(fill="x")
        for i, key in enumerate(col_keys):
            var = tk.BooleanVar(value=self._settings.get(key, True))
            col_vars[key] = var
            _cb = tk.Checkbutton(cf, text=col_labels[key], variable=var, bg=C["bg"], fg=C["text"],
                           activebackground=C["bg"], activeforeground=C["accent"],
                           selectcolor=C["card"], font=(_FONT_UI,10), bd=0, highlightthickness=0
                           )
            _cb.grid(row=i//3, column=i%3, sticky="w", pady=2, padx=(0,16))
            if key == "col_language":
                _Tooltip(_cb, "If unchecked, a language indicator will show next to the release name")
            var.trace_add("write", _on_col_toggle)

        ttk.Separator(body, orient="horizontal").pack(fill="x", pady=(8,6))

        # sizing
        ttk.Label(body, text="Results list:", style="Dim.TLabel").pack(anchor="w", pady=(0,4))
        sf = ttk.Frame(body); sf.pack(fill="x", pady=2)
        ttk.Label(sf, text="Row height (px):", style="Dim.TLabel").grid(row=0, column=0, sticky="w", pady=3)
        rh_var = tk.IntVar(value=self._settings.get("row_height", 40))
        ttk.Spinbox(sf, textvariable=rh_var, from_=24, to=72, increment=4,
                    width=6).grid(row=0, column=1, sticky="w", padx=(10,30))
        ttk.Label(sf, text="Font size (pt):", style="Dim.TLabel").grid(row=0, column=2, sticky="w", pady=3)
        fs_var = tk.IntVar(value=self._settings.get("font_size", 9))
        ttk.Spinbox(sf, textvariable=fs_var, from_=7, to=16, increment=1,
                    width=6).grid(row=0, column=3, sticky="w", padx=(10,0))

        ttk.Separator(body, orient="horizontal").pack(fill="x", pady=(8,6))

        # Providers
        _prov_lbl = ttk.Label(body, text="Providers:", style="Dim.TLabel")
        _prov_lbl.pack(anchor="w", pady=(0,4))
        prov_vars = {}
        prov_frame = ttk.Frame(body); prov_frame.pack(fill="x")
        for i, (key, label) in enumerate([
            ("provider_subliminal", "OpenSubtitles"),
            ("provider_subdl",      "SubDL"),
        ]):
            var = tk.BooleanVar(value=self._settings.get(key, False))
            prov_vars[key] = var
            tk.Checkbutton(prov_frame, text=label, variable=var, bg=C["bg"], fg=C["text"],
                           activebackground=C["bg"], activeforeground=C["accent"],
                           selectcolor=C["card"], font=(_FONT_UI,10), bd=0, highlightthickness=0
                           ).grid(row=0, column=i, sticky="w", pady=2, padx=(0,24))

        ttk.Separator(body, orient="horizontal").pack(fill="x", pady=(8,6))

        # API keys
        ttk.Label(body, text="API Keys:", style="Dim.TLabel").pack(anchor="w", pady=(0,4))
        af = ttk.Frame(body)
        af.pack(fill="x", pady=3)
        af.columnconfigure(0, minsize=150)
        af.columnconfigure(1, weight=1)
        af.columnconfigure(2, weight=0, minsize=40)  # Reserved for the settings buttons
        ttk.Label(af, text="OpenSubtitles API key:", style="Dim.TLabel").grid(row=1, column=0, sticky="w", pady=3)
        oscom_var = tk.StringVar(value=self._settings.get("oscom_api_key",""))
        ttk.Entry(af, textvariable=oscom_var, width=25).grid(row=1, column=1, sticky="ew", padx=(10,0), pady=3)

        # Credentials vars — defined here so _apply() can read them
        _oscom_username_var = tk.StringVar(value=self._settings.get("oscom_username", ""))
        _oscom_password_var = tk.StringVar(value=self._settings.get("oscom_password", ""))

        def _open_oscom_popup():
            pop = tk.Toplevel(win)
            pop.title("OpenSubtitles Credentials")
            pop.resizable(False, False)
            pop.grab_set()
            pf = ttk.Frame(pop, padding=14)
            pf.pack(fill="both", expand=True)
            ttk.Label(pf,
                      text="Provides a higher daily download quota.",
                      style="Dim.TLabel", wraplength=260).grid(
                row=0, column=0, columnspan=2, sticky="w", pady=(0, 10))
            _tmp_username = tk.StringVar(value=_oscom_username_var.get())
            _tmp_password = tk.StringVar(value=_oscom_password_var.get())
            for i, (label, var, show) in enumerate([
                ("Username", _tmp_username, ""),
                ("Password", _tmp_password, "*"),
            ], start=1):
                ttk.Label(pf, text=label + ":", style="Dim.TLabel").grid(
                    row=i, column=0, sticky="w", pady=3)
                ttk.Entry(pf, textvariable=var, width=26, show=show).grid(
                    row=i, column=1, sticky="w", padx=(8, 0), pady=3)
            def _save_oscom():
                _u = _tmp_username.get().strip()
                _p = _tmp_password.get().strip()
                _oscom_username_var.set(_u)
                _oscom_password_var.set(_p)
                # Write through to self._settings so _save_settings() persists the values.
                self._settings["oscom_username"] = _u
                self._settings["oscom_password"] = _p
                # Clear cached JWT so next download re-authenticates with new creds.
                # Must hold the lock — _get_oscom_jwt() may be running concurrently.
                with _oscom_jwt_lock:
                    global _oscom_jwt_token, _oscom_jwt_expiry
                    _oscom_jwt_token  = ""
                    _oscom_jwt_expiry = 0.0
                self._settings["oscom_popup_geometry"] = pop.geometry()
                self._save_settings()
                pop.destroy()
            def _close_oscom():
                self._settings["oscom_popup_geometry"] = pop.geometry()
                self._save_settings()
                pop.destroy()
            pop.protocol("WM_DELETE_WINDOW", _close_oscom)
            btn_row = ttk.Frame(pf)
            btn_row.grid(row=3, column=0, columnspan=2, pady=(12, 0), sticky="ew")
            btn_row.columnconfigure(0, weight=1)
            btn_row.columnconfigure(1, weight=1)
            ttk.Button(btn_row, text="Cancel", style="GeminiCancel.TButton", command=_close_oscom).grid(row=0, column=0, sticky="ew", padx=(0, 4))
            ttk.Button(btn_row, text="Save", command=_save_oscom).grid(row=0, column=1, sticky="ew", padx=(4, 0))
            # Restore last position
            _oscom_geo = self._settings.get("oscom_popup_geometry", "")
            if _oscom_geo:
                _m = re.search(r"([+-]\d+[+-]\d+)$", _oscom_geo)
                if _m:
                    pop.update_idletasks()
                    try:
                        pop.geometry(_m.group(1))
                        self._clamp_window_to_screen(pop)
                    except Exception:
                        pass

        _oscom_gear_frame = tk.Frame(af, width=32, height=28, bg=C["card"])
        _oscom_gear_frame.grid(row=1, column=2, padx=(6, 0), pady=3, sticky="e")
        _oscom_gear_frame.pack_propagate(False)
        _oscom_gear_frame.grid_propagate(False)
        _oscom_creds_btn = ttk.Button(_oscom_gear_frame, text="\uE713", command=_open_oscom_popup,
                                      style="ConfigIcon.TButton")
        _oscom_creds_btn.place(relx=0, rely=0, relwidth=1, relheight=1)
        ttk.Label(af, text="SubDL API key:", style="Dim.TLabel").grid(row=2, column=0, sticky="w", pady=3)
        subdl_var = tk.StringVar(value=self._settings.get("subdl_api_key",""))
        # columnspan=2 merges the entry cell and the button cell
        # sticky="ew" stretches it to fill that merged space entirely
        ttk.Entry(af, textvariable=subdl_var).grid(row=2, column=1, columnspan=2, sticky="ew", padx=(10, 0), pady=3)
        # ── Gemini translation row: summary badge + Configure button ──────────
        # The badge shows "N keys · N models · N blocks" and updates live on save.
        # All Gemini config lives inside _open_gemini_popup.
        ttk.Label(af, text="Gemini translation:", style="Dim.TLabel").grid(
            row=0, column=0, sticky="w", pady=3)

        _gemini_badge_var = tk.StringVar()

        def _update_gemini_badge():
            keys   = [k.strip() for k in self._settings.get("gemini_api_keys", []) if k.strip()]
            if not keys:
                leg = self._settings.get("gemini_api_key", "").strip()
                if leg:
                    keys = [leg]
            models = [m.strip() for m in self._settings.get("gemini_models", []) if m.strip()]
            n_models = sum(1 for m in models if m)
            n_keys   = len(keys)
            chunk    = self._settings.get("gemini_chunk_size", _GEMINI_CHUNK_SIZE)
            if n_keys == 0 and n_models == 0:
                _gemini_badge_var.set("not configured")
            else:
                _gemini_badge_var.set(
                    "{} key{} \u00b7 {} model{} \u00b7 {} blocks".format(
                        n_keys, "s" if n_keys != 1 else "",
                        n_models, "s" if n_models != 1 else "",
                        chunk))

        _update_gemini_badge()

        # Badge container — 1px border outer frame, inner card frame, label inside.
        # Fixed pixel width (200px) with geometry propagation disabled so that a
        # very long block-count string never pushes the Settings window wider.
        _badge_outer = tk.Frame(af, bg=C["border"], bd=0, width=200)
        _badge_outer.grid(row=0, column=1, sticky="ew", padx=(10, 0), pady=3)
        _badge_outer.grid_propagate(False)
        _badge_inner = tk.Frame(_badge_outer, bg=C["card"], bd=0)
        _badge_inner.pack(fill="both", expand=True, padx=1, pady=1)
        ttk.Label(_badge_inner, textvariable=_gemini_badge_var,
                style="GeminiStatus.TLabel",
                anchor="center").pack(fill="both", expand=True, padx=10, pady=5)

        # Internal state for the popup — defined here so _apply() can read them.
        # These are lists (for keys + models) and an int (chunk size).
        _gemini_keys_state:   list = list(self._settings.get("gemini_api_keys", []))
        _gemini_models_state: list = [m for m in self._settings.get("gemini_models", []) if m.strip()]
        if not _gemini_models_state:
            _gemini_models_state = ["gemini-2.5-flash-lite", "gemini-2.5-flash", "gemini-2.5-pro"]
        _gemini_chunk_state: list = [self._settings.get("gemini_chunk_size", 300)]
        # Migrate legacy single key into list on first open if list is empty
        if not _gemini_keys_state:
            leg = self._settings.get("gemini_api_key", "").strip()
            if leg:
                _gemini_keys_state.append(leg)

        def _open_gemini_popup():
            pop = tk.Toplevel(win)
            pop.withdraw()  # hide until fully laid out — prevents position flash
            pop.title("Gemini Translation")
            pf = ttk.Frame(pop, padding=(16, 14, 16, 14))
            pf.pack(fill="both", expand=True)

            # ── Scroll state ──────────────────────────────────────────────────
            # Cached pixel height of the scroll viewport when rows == 11.
            # Set once; reused every time total > 11.
            _scroll_cap_h = [None]   # [int | None]

            # Re-entrancy guard: prevents a <Configure> event fired inside
            # pop.geometry() from scheduling a second _resize_pop() before the
            # first one completes, which would cause a rapid resize loop on
            # slow machines or Linux WMs that emit synchronous Configure events.
            _resize_in_progress = [False]

            def _resize_pop():
                """Resize the popup window to fit its content after rows change."""
                if _resize_in_progress[0]:
                    return
                _resize_in_progress[0] = True
                try:
                    pop.update_idletasks()
                    _h = pop.winfo_reqheight()
                    if _h < 50:
                        return  # not yet rendered; _on_inner_resize will trigger naturally
                    _cur_geo = pop.geometry()
                    _m = re.match(r"(\d+)x(\d+)([+-]\d+[+-]\d+)?", _cur_geo)
                    if _m:
                        _w = _m.group(1)
                        _pos = _m.group(3) or "+0+0"
                        pop.geometry("{}x{}{}".format(_w, _h, _pos))
                    else:
                        pop.geometry("330x{}".format(_h))
                finally:
                    _resize_in_progress[0] = False

            ttk.Label(pf, text="Gemini translation",
                      font=(_FONT_UI, 11, "bold")).pack(anchor="w")
            ttk.Label(pf, text="Keys and models are tried top to bottom. The next is used automatically on errors.",
                      style="Dim.TLabel", justify="left", wraplength=298).pack(anchor="w", pady=(2, 10))

            ttk.Separator(pf, orient="horizontal").pack(fill="x", pady=(0, 10))

            # ── Work copies so Cancel reverts everything ──────────────────────
            _tmp_keys:   list = list(_gemini_keys_state)
            _tmp_models: list = list(_gemini_models_state)
            _tmp_chunk:  list = [_gemini_chunk_state[0]]

            # ── Scroll container (API KEYS + MODEL CHAIN combined) ────────────
            # Outer frame holds canvas + scrollbar side-by-side.
            _scroll_outer = tk.Frame(pf, bg=C.get("bg", "#010409"))
            _scroll_outer.pack(fill="x")

            # Scrollbar MUST be packed before the canvas so pack manager
            # reserves space for it on the right before the canvas fills remaining width.
            _scroll_vsb = ttk.Scrollbar(_scroll_outer, orient="vertical")
            _scroll_vsb.pack(side="right", fill="y")
            _scroll_vsb.pack_forget()  # hidden until total rows > 11

            _scroll_canvas = tk.Canvas(
                _scroll_outer,
                bg=C.get("bg", "#010409"),
                highlightthickness=0,
                bd=0,
                height=10,
            )
            _scroll_canvas.pack(side="left", fill="both", expand=True)
            _scroll_vsb.configure(command=_scroll_canvas.yview)

            # Inner frame — all keys/models content lives here
            _scroll_inner = tk.Frame(_scroll_canvas, bg=C.get("bg", "#010409"))
            _scroll_canvas_window = _scroll_canvas.create_window(
                (0, 0), window=_scroll_inner, anchor="nw")

            def _on_inner_resize(e):
                """Fires whenever _scroll_inner changes size.
                Sets canvas height = inner height (no-scroll) or the 11-row cap (scroll)."""
                inner_h = _scroll_inner.winfo_reqheight()
                if inner_h < 1:
                    return
                total_rows = len(_key_rows) + len(_model_rows)
                _scroll_canvas.configure(scrollregion=(0, 0, 0, inner_h))
                if total_rows <= 11:
                    _scroll_canvas.configure(height=inner_h)
                    if _scroll_vsb.winfo_ismapped():
                        _scroll_vsb.pack_forget()
                    _scroll_canvas.configure(yscrollcommand="")
                else:
                    if _scroll_cap_h[0] is None:
                        row_h = (_key_drag.get("row_h") or _model_drag.get("row_h") or 30)
                        _scroll_cap_h[0] = 11 * (row_h + 4) + 36
                    _scroll_canvas.configure(height=_scroll_cap_h[0])
                    if not _scroll_vsb.winfo_ismapped():
                        # Re-pack scrollbar on right THEN re-pack canvas so order is correct
                        _scroll_canvas.pack_forget()
                        _scroll_vsb.pack(side="right", fill="y")
                        _scroll_canvas.pack(side="left", fill="both", expand=True)
                    _scroll_canvas.configure(yscrollcommand=_scroll_vsb.set)
                pop.after(0, _resize_pop)

            def _on_scroll_canvas_configure(e):
                _scroll_canvas.itemconfigure(_scroll_canvas_window, width=e.width)

            _scroll_inner.bind("<Configure>", _on_inner_resize)
            _scroll_canvas.bind("<Configure>", _on_scroll_canvas_configure)

            # Mouse-wheel scrolling — bind to every widget inside the popup so
            # the scroll works regardless of which child widget the cursor is over.
            def _on_mousewheel(e):
                if _scroll_vsb.winfo_ismapped():
                    # macOS reports delta already in scroll units (no /120 needed);
                    # Windows/Linux report in multiples of 120.
                    _delta = int(-e.delta) if sys.platform == "darwin" else int(-1 * (e.delta / 120))
                    _scroll_canvas.yview_scroll(_delta, "units")

            def _bind_mousewheel_recursive(widget):
                widget.bind("<MouseWheel>", _on_mousewheel, add="+")
                for child in widget.winfo_children():
                    _bind_mousewheel_recursive(child)

            # Bind now on the scroll area; also called after each row rebuild.
            _bind_mousewheel_recursive(_scroll_outer)
            # Linux scroll events
            _scroll_canvas.bind("<Button-4>", lambda e: _on_mousewheel(type("E", (), {"delta": 120})()))
            _scroll_canvas.bind("<Button-5>", lambda e: _on_mousewheel(type("E", (), {"delta": -120})()))

            # ── Drag auto-scroll ───────────────────────────────────────────────
            # Proximity-based speed: the closer the cursor is to the edge,
            # the slower the scroll. The further into the hot zone, the faster.
            _autoscroll_id = [None]
            _AUTOSCROLL_ZONE  = 50    # px from edge that triggers scrolling
            _AUTOSCROLL_DELAY = 40    # ms between ticks
            _autoscroll_accum = [0.0] # fractional accumulator for sub-unit speeds

            def _autoscroll_tick():
                _autoscroll_id[0] = None
                if not _scroll_vsb.winfo_ismapped():
                    return
                if not _key_drag.get("active") and not _model_drag.get("active"):
                    _autoscroll_accum[0] = 0.0
                    return
                try:
                    cy = _scroll_canvas.winfo_pointery() - _scroll_canvas.winfo_rooty()
                    ch = _scroll_canvas.winfo_height()
                except Exception:
                    return

                raw_speed = 0.0
                if cy < _AUTOSCROLL_ZONE:
                    ratio = 1.0 - (cy / _AUTOSCROLL_ZONE)        # 0.0 at edge → 1.0 deep
                    raw_speed = -(0.05 + ratio * 0.95)            # 0.05 → 1.0 units/tick
                elif cy > ch - _AUTOSCROLL_ZONE:
                    ratio = 1.0 - ((ch - cy) / _AUTOSCROLL_ZONE)
                    raw_speed = (0.05 + ratio * 0.95)

                if raw_speed != 0.0:
                    _autoscroll_accum[0] += raw_speed
                    units = int(_autoscroll_accum[0])
                    if units != 0:
                        _scroll_canvas.yview_scroll(units, "units")
                        _autoscroll_accum[0] -= units
                else:
                    _autoscroll_accum[0] = 0.0

                _autoscroll_id[0] = pop.after(_AUTOSCROLL_DELAY, _autoscroll_tick)

            def _autoscroll_start():
                if _autoscroll_id[0] is None:
                    _autoscroll_id[0] = pop.after(_AUTOSCROLL_DELAY, _autoscroll_tick)

            def _autoscroll_stop():
                if _autoscroll_id[0] is not None:
                    pop.after_cancel(_autoscroll_id[0])
                    _autoscroll_id[0] = None

            # ── Section: API KEYS (inside scroll inner) ───────────────────────
            ttk.Label(_scroll_inner, text="API KEYS",
                      font=(_FONT_UI, 8, "bold"), foreground=C.get("dim", "#888")).pack(anchor="w", pady=(0, 4))

            _keys_frame = tk.Frame(_scroll_inner, bg=C.get("surface", "#03060a"))
            _keys_frame.pack(fill="x", pady=(0, 4))

            _key_vars: list = []
            _key_rows: list = []

            # Drag-reorder state for keys (live DDList-style shift)
            _key_drag: dict = {
                "active": False, "idx": None,
                "ghost": None,          # floating ghost Frame placed on pop
                "ghost_y_off": 0,       # cursor offset inside the dragged row
                "y_start": 0,           # absolute y_root at drag start
                "slot_y": [],           # snapshot of each row's y relative to _keys_frame
                "row_h": 30,            # row height (measured at drag start)
                "empty_slot": None,     # which slot index is currently "open"
            }

            def _flush_key_vars():
                for i, v in enumerate(_key_vars):
                    if i < len(_tmp_keys):
                        _tmp_keys[i] = v.get()

            # ── helpers ──────────────────────────────────────────────────────────
            def _key_ghost_destroy():
                g = _key_drag.get("ghost")
                if g:
                    try: g.destroy()
                    except Exception: pass
                _key_drag["ghost"] = None

            def _key_place_rows(skip_idx=None):
                """Re-place all rows at their canonical y positions, skipping skip_idx."""
                row_h = _key_drag["row_h"]
                gap   = 4
                y     = 0
                for i, row in enumerate(_key_rows):
                    if i == skip_idx:
                        y += row_h + gap
                        continue
                    row.place(in_=_keys_frame, x=0, y=y, relwidth=1, height=row_h)
                    y += row_h + gap
                # Update the container height so pack layout stays correct
                total = len(_key_rows) * (row_h + gap)
                _keys_frame.configure(height=max(total, 1))

            def _key_commit_virtual_order(dragged_idx, empty_slot):
                """Shift rows visually so empty_slot is open at the right position."""
                row_h = _key_drag["row_h"]
                gap   = 4
                y = 0
                for i in range(len(_key_rows)):
                    if i == dragged_idx:
                        # Dragged row is floating — don't move it
                        y += row_h + gap
                        continue
                    # Compute virtual index: skip dragged, insert gap at empty_slot
                    vi = i if i < dragged_idx else i - 1
                    dest_slot = vi if vi < empty_slot else vi + 1
                    dest_y = dest_slot * (row_h + gap)
                    _key_rows[i].place_configure(y=dest_y)
                    y += row_h + gap

            def _rebuild_key_rows():
                _key_ghost_destroy()
                for w in _keys_frame.winfo_children():
                    w.destroy()
                _key_vars.clear()
                _key_rows.clear()
                for i, k in enumerate(_tmp_keys):
                    row = tk.Frame(_keys_frame, bg=C.get("surface", "#03060a"))
                    _key_rows.append(row)
                    # ── Drag handle ───────────────────────────────────────────
                    _df = tk.Frame(row, width=26, height=26)
                    _df.pack(side="left", padx=(0, 3))
                    _df.pack_propagate(False)
                    handle = ttk.Button(_df, text=_GLYPH_DRAG, cursor="fleur",
                                        style="Icon.TButton")
                    handle.place(relx=0, rely=0, relwidth=1, relheight=1)
                    ttk.Label(row, text=str(i + 1),
                              style="Dim.TLabel", width=2).pack(side="left", padx=(0, 3))
                    v = tk.StringVar(value=k)
                    _key_vars.append(v)
                    ttk.Entry(row, textvariable=v, width=24).pack(side="left", padx=(0, 3))
                    _idx = i
                    def _remove_key(idx=_idx):
                        if len(_tmp_keys) <= 1:
                            return
                        _flush_key_vars()
                        del _tmp_keys[idx]
                        _rebuild_key_rows()
                        _resize_pop()
                    # ── Add button (last row only) ─────────────────────────────
                    if i == len(_tmp_keys) - 1:
                        _pf = tk.Frame(row, width=26, height=26)
                        _pf.pack(side="left", padx=(2, 0))
                        _pf.pack_propagate(False)
                        ttk.Button(_pf, text=_GLYPH_ADD, command=_add_key,
                                   style="IconAccent.TButton").place(relx=0, rely=0, relwidth=1, relheight=1)
                    # ── Delete button ──────────────────────────────────────────
                    _xf = tk.Frame(row, width=26, height=26)
                    _xf.pack(side="left", padx=(2, 0))
                    _xf.pack_propagate(False)
                    ttk.Button(_xf, text=_GLYPH_REMOVE, command=_remove_key,
                               style="IconDanger.TButton").place(relx=0, rely=0, relwidth=1, relheight=1)
                    # ── Drag bindings ─────────────────────────────────────────
                    def _on_key_drag_start(e, idx=_idx):
                        _flush_key_vars()
                        if not _key_rows:
                            return
                        _keys_frame.update_idletasks()
                        row_h = _key_rows[0].winfo_reqheight()
                        if row_h < 8:
                            row_h = 30
                        _key_drag["active"]    = True
                        _key_drag["idx"]       = idx
                        _key_drag["row_h"]     = row_h
                        _key_drag["empty_slot"] = idx
                        _key_drag["y_start"]   = e.y_root
                        # Cursor offset inside the dragged row
                        _key_drag["ghost_y_off"] = e.y
                        # Canvas scroll offset in pixels at drag start — used to
                        # compensate new_y when autoscroll shifts the canvas mid-drag
                        _key_drag["scroll_start"] = _scroll_canvas.yview()[0] * _scroll_inner.winfo_reqheight()

                        # Switch all rows to place() geometry
                        _key_place_rows()

                        # Lift the dragged row above siblings
                        _key_rows[idx].tkraise()

                        # Create a semi-transparent ghost on the popup window
                        src = _key_rows[idx]
                        ghost = tk.Frame(
                            pop,
                            width=src.winfo_width() or 280,
                            height=row_h,
                            bg=C.get("accent", "#4a9eff"),
                            highlightthickness=1,
                            highlightbackground=C.get("accent", "#4a9eff"),
                        )
                        # Position ghost over the dragged row
                        rx = _keys_frame.winfo_rootx() - pop.winfo_rootx()
                        ry = _keys_frame.winfo_rooty() - pop.winfo_rooty()
                        ghost.place(x=rx, y=ry + idx * (row_h + 4), width=src.winfo_width() or 280, height=row_h)
                        ghost.lower()   # keep ghost behind actual row for clean look
                        _key_drag["ghost"] = ghost

                    def _on_key_drag_motion(e, idx=_idx):
                        # Issue #4B: store latest event coords and schedule a single
                        # geometry flush per idle tick via after(0, ...).  This coalesces
                        # all B1-Motion events that arrive in one Tk event-loop cycle into
                        # one place_configure() call, eliminating the repaint overdraw that
                        # caused the button-flash on Windows.
                        d = _key_drag
                        if not d["active"] or d["idx"] != idx:
                            return
                        d["_last_motion_e"] = (e.y_root,)
                        if d.get("_motion_pending"):
                            return
                        d["_motion_pending"] = True

                        def _flush_key_motion(idx=idx):
                            d["_motion_pending"] = False
                            ev = d.get("_last_motion_e")
                            if not ev or not d["active"] or d["idx"] != idx:
                                return
                            y_root = ev[0]
                            row_h = d["row_h"]
                            gap   = 4

                            ghost = d.get("ghost")
                            if ghost:
                                rx = _keys_frame.winfo_rootx() - pop.winfo_rootx()
                                ry = _keys_frame.winfo_rooty() - pop.winfo_rooty() +                                      (y_root - pop.winfo_rooty()) - d["ghost_y_off"]
                                try:
                                    ghost.place_configure(y=max(0, ry))
                                except Exception:
                                    pass

                            delta = y_root - d["y_start"]
                            # Compensate for canvas scrolling since drag started
                            scroll_now = _scroll_canvas.yview()[0] * _scroll_inner.winfo_reqheight()
                            scroll_delta = scroll_now - d.get("scroll_start", scroll_now)
                            new_y = idx * (row_h + gap) + delta + scroll_delta
                            new_y = max(0, min((len(_key_rows) - 1) * (row_h + gap), new_y))
                            try:
                                _key_rows[idx].place_configure(y=new_y)
                            except Exception:
                                pass

                            cursor_frame_y = new_y + row_h // 2
                            hover_slot = max(0, min(len(_key_rows) - 1,
                                                    int(cursor_frame_y / (row_h + gap))))
                            if hover_slot != d["empty_slot"]:
                                d["empty_slot"] = hover_slot
                                _key_commit_virtual_order(idx, hover_slot)

                        pop.after(0, _flush_key_motion)
                        _autoscroll_start()

                    def _on_key_drag_end(e, idx=_idx):
                        d = _key_drag
                        if not d["active"] or d["idx"] != idx:
                            return
                        target = d["empty_slot"]
                        d["active"] = False
                        _autoscroll_stop()
                        _key_ghost_destroy()
                        if target != idx:
                            _flush_key_vars()
                            _tmp_keys.insert(target, _tmp_keys.pop(idx))
                        _rebuild_key_rows()

                    handle.bind("<ButtonPress-1>",  _on_key_drag_start)
                    handle.bind("<B1-Motion>",       _on_key_drag_motion)
                    handle.bind("<ButtonRelease-1>", _on_key_drag_end)

                # Initial placement using place() so drag works from the start
                if _key_rows:
                    _keys_frame.update_idletasks()
                    row_h = _key_rows[0].winfo_reqheight()
                    if row_h < 8:
                        row_h = 30
                    _key_drag["row_h"] = row_h
                    _key_place_rows()
                # Rebind mousewheel to any newly created child widgets
                _bind_mousewheel_recursive(_scroll_outer)

            def _add_key():
                _flush_key_vars()
                _tmp_keys.append("")
                _rebuild_key_rows()
                _resize_pop()

            # Always show at least one empty row so the entry field is visible
            if not _tmp_keys:
                _tmp_keys.append("")
            _rebuild_key_rows()

            # ── Quota warning (dismissible) ───────────────────────────────────
            _warn_dismissed = [self._settings.get("gemini_key_warning_dismissed", False)]

            # Warning colours — intentionally outside the theme palette so that
            # _apply_theme()'s match_color() never re-colors these widgets on theme switch.
            _warn_bg   = "#2d2000"   # deep amber-black background
            _warn_bdr  = "#c8860a"   # amber border
            _warn_icon = "#ffc107"   # bright amber icon
            _warn_head = "#ffe082"   # warm white headline
            _warn_body = "#c8a84b"   # muted amber body text
            _dim       = C.get("dim",    "#888888")
            _txt       = C.get("text",   "#e6edf3")

            # Outer frame is only created when visible; destroyed fully on dismiss
            _warn_container = [None]  # holds the frame reference

            def _show_warning():
                if _warn_container[0] is not None:
                    return  # already shown
                outer = tk.Frame(_scroll_inner, bg=_warn_bdr, padx=1, pady=1)
                outer.pack(fill="x", pady=(0, 8))
                inner = tk.Frame(outer, bg=_warn_bg, padx=10, pady=7)
                inner.pack(fill="x")
                _warn_container[0] = outer
                # Text widget with hanging indent — emoji on line 1, second line
                # indents to align under the text start, not the emoji.
                # lmargin1=0 (first line starts at left), lmargin2=20 (wrap indent).
                _warn_text = tk.Text(inner, bg=_warn_bg, fg=_warn_body,
                                     font=(_FONT_UI, 9), relief="flat", bd=0,
                                     highlightthickness=0, wrap="word",
                                     height=3, cursor="arrow",
                                     padx=0, pady=0, spacing1=0, spacing2=0, spacing3=0)
                _warn_text.tag_configure("icon", font=(_FONT_UI, 11), foreground=_warn_icon)
                _warn_text.tag_configure("bold", font=(_FONT_UI, 9, "bold"), foreground=_warn_head)
                _warn_text.tag_configure("hang", lmargin1=0, lmargin2=0)
                _warn_text.insert("end", "⚠  ", "icon")
                _warn_text.insert("end", "Use a ", "hang")
                _warn_text.insert("end", "different Google account", ("bold", "hang"))
                _warn_text.insert("end", " per key, same-account keys share the same quota pool.", "hang")
                _warn_text.config(state="disabled")
                _warn_text.pack(fill="x", expand=True)
                # Dismiss links
                bot = tk.Frame(inner, bg=_warn_bg)
                bot.pack(anchor="e", pady=(5, 0))
                _dont_lbl = tk.Label(bot, text="Don't show again",
                                     bg=_warn_bg, fg=_warn_body, font=(_FONT_UI, 8), cursor="hand2")
                _dont_lbl.pack(side="left")
                _dont_lbl.bind("<Enter>", lambda e: _dont_lbl.config(fg=_warn_head))
                _dont_lbl.bind("<Leave>", lambda e: _dont_lbl.config(fg=_warn_body))
                _dont_lbl.bind("<Button-1>", lambda e: [
                    _warn_dismissed.__setitem__(0, True), _dismiss_warning(permanent=True)])
                tk.Label(bot, text="  ·  ", bg=_warn_bg, fg=_warn_bdr,
                         font=(_FONT_UI, 8)).pack(side="left")
                _hide_lbl = tk.Label(bot, text="Hide",
                                     bg=_warn_bg, fg=_warn_body, font=(_FONT_UI, 8), cursor="hand2")
                _hide_lbl.pack(side="left")
                _hide_lbl.bind("<Enter>", lambda e: _hide_lbl.config(fg=_warn_head))
                _hide_lbl.bind("<Leave>", lambda e: _hide_lbl.config(fg=_warn_body))
                _hide_lbl.bind("<Button-1>", lambda e: _dismiss_warning(permanent=False))

            def _dismiss_warning(permanent=False):
                if permanent:
                    _warn_dismissed[0] = True
                if _warn_container[0] is not None:
                    _warn_container[0].destroy()
                    _warn_container[0] = None
                _resize_pop()

            if not _warn_dismissed[0]:
                _show_warning()

            ttk.Separator(_scroll_inner, orient="horizontal").pack(fill="x", pady=(0, 10))

            # ── Section: MODEL CHAIN (inside scroll inner) ────────────────────
            ttk.Label(_scroll_inner, text="MODEL CHAIN",
                      font=(_FONT_UI, 8, "bold"), foreground=C.get("dim","#888")).pack(anchor="w", pady=(0, 4))

            _models_frame = tk.Frame(_scroll_inner, bg=C.get("surface", "#03060a"))
            _models_frame.pack(fill="x", pady=(0, 4))

            _model_vars: list = []
            _model_rows: list = []

            # Drag-reorder state for models (live DDList-style shift)
            _model_drag: dict = {
                "active": False, "idx": None,
                "ghost": None,
                "ghost_y_off": 0,
                "y_start": 0,
                "row_h": 30,
                "empty_slot": None,
                "scroll_start": 0,  # canvas scroll offset (px) at drag start — matches _key_drag layout
            }

            def _flush_model_vars():
                for i, v in enumerate(_model_vars):
                    if i < len(_tmp_models):
                        _tmp_models[i] = v.get()

            def _model_ghost_destroy():
                g = _model_drag.get("ghost")
                if g:
                    try: g.destroy()
                    except Exception: pass
                _model_drag["ghost"] = None

            def _model_place_rows(skip_idx=None):
                row_h = _model_drag["row_h"]
                gap   = 4
                y     = 0
                for i, row in enumerate(_model_rows):
                    if i == skip_idx:
                        y += row_h + gap
                        continue
                    row.place(in_=_models_frame, x=0, y=y, relwidth=1, height=row_h)
                    y += row_h + gap
                total = len(_model_rows) * (row_h + gap)
                _models_frame.configure(height=max(total, 1))

            def _model_commit_virtual_order(dragged_idx, empty_slot):
                row_h = _model_drag["row_h"]
                gap   = 4
                for i in range(len(_model_rows)):
                    if i == dragged_idx:
                        continue
                    vi = i if i < dragged_idx else i - 1
                    dest_slot = vi if vi < empty_slot else vi + 1
                    dest_y = dest_slot * (row_h + gap)
                    _model_rows[i].place_configure(y=dest_y)

            def _rebuild_model_rows():
                _model_ghost_destroy()
                for w in _models_frame.winfo_children():
                    w.destroy()
                _model_vars.clear()
                _model_rows.clear()
                for i, m in enumerate(_tmp_models):
                    row = tk.Frame(_models_frame, bg=C.get("surface", "#03060a"))
                    _model_rows.append(row)
                    # ── Drag handle ───────────────────────────────────────────
                    _df = tk.Frame(row, width=26, height=26)
                    _df.pack(side="left", padx=(0, 3))
                    _df.pack_propagate(False)
                    handle = ttk.Button(_df, text=_GLYPH_DRAG, cursor="fleur",
                                        style="Icon.TButton")
                    handle.place(relx=0, rely=0, relwidth=1, relheight=1)
                    ttk.Label(row, text=str(i + 1),
                              style="Dim.TLabel", width=2).pack(side="left", padx=(0, 3))
                    v = tk.StringVar(value=m)
                    _model_vars.append(v)
                    ttk.Entry(row, textvariable=v, width=24).pack(side="left", padx=(0, 3))
                    _idx = i
                    def _remove_model(idx=_idx):
                        if len(_tmp_models) <= 1:
                            return
                        _flush_model_vars()
                        del _tmp_models[idx]
                        _rebuild_model_rows()
                        _resize_pop()
                    # ── Add button (last row only) ─────────────────────────────
                    if i == len(_tmp_models) - 1:
                        _pf = tk.Frame(row, width=26, height=26)
                        _pf.pack(side="left", padx=(2, 0))
                        _pf.pack_propagate(False)
                        ttk.Button(_pf, text=_GLYPH_ADD, command=_add_model,
                                   style="IconAccent.TButton").place(relx=0, rely=0, relwidth=1, relheight=1)
                    # ── Delete button ──────────────────────────────────────────
                    _xf = tk.Frame(row, width=26, height=26)
                    _xf.pack(side="left", padx=(2, 0))
                    _xf.pack_propagate(False)
                    ttk.Button(_xf, text=_GLYPH_REMOVE, command=_remove_model,
                               style="IconDanger.TButton").place(relx=0, rely=0, relwidth=1, relheight=1)
                    # ── Drag bindings ─────────────────────────────────────────
                    def _on_model_drag_start(e, idx=_idx):
                        _flush_model_vars()
                        if not _model_rows:
                            return
                        _models_frame.update_idletasks()
                        row_h = _model_rows[0].winfo_reqheight()
                        if row_h < 8:
                            row_h = 30
                        _model_drag["active"]    = True
                        _model_drag["idx"]       = idx
                        _model_drag["row_h"]     = row_h
                        _model_drag["empty_slot"] = idx
                        _model_drag["y_start"]   = e.y_root
                        _model_drag["ghost_y_off"] = e.y
                        _model_drag["scroll_start"] = _scroll_canvas.yview()[0] * _scroll_inner.winfo_reqheight()

                        _model_place_rows()
                        _model_rows[idx].tkraise()

                        src = _model_rows[idx]
                        ghost = tk.Frame(
                            pop,
                            width=src.winfo_width() or 280,
                            height=row_h,
                            bg=C.get("accent", "#4a9eff"),
                            highlightthickness=1,
                            highlightbackground=C.get("accent", "#4a9eff"),
                        )
                        rx = _models_frame.winfo_rootx() - pop.winfo_rootx()
                        ry = _models_frame.winfo_rooty() - pop.winfo_rooty()
                        ghost.place(x=rx, y=ry + idx * (row_h + 4), width=src.winfo_width() or 280, height=row_h)
                        ghost.lower()
                        _model_drag["ghost"] = ghost

                    def _on_model_drag_motion(e, idx=_idx):
                        # Issue #4B: same after(0,...) throttle as the keys motion handler.
                        # Coalesces all B1-Motion events into one geometry update per idle
                        # tick, eliminating the repaint overdraw that caused button-flash.
                        d = _model_drag
                        if not d["active"] or d["idx"] != idx:
                            return
                        d["_last_motion_e"] = (e.y_root,)
                        if d.get("_motion_pending"):
                            return
                        d["_motion_pending"] = True

                        def _flush_model_motion(idx=idx):
                            d["_motion_pending"] = False
                            ev = d.get("_last_motion_e")
                            if not ev or not d["active"] or d["idx"] != idx:
                                return
                            y_root = ev[0]
                            row_h = d["row_h"]
                            gap   = 4

                            ghost = d.get("ghost")
                            if ghost:
                                rx = _models_frame.winfo_rootx() - pop.winfo_rootx()
                                ry = _models_frame.winfo_rooty() - pop.winfo_rooty() + \
                                     (y_root - pop.winfo_rooty()) - d["ghost_y_off"]
                                try:
                                    ghost.place_configure(y=max(0, ry))
                                except Exception:
                                    pass

                            delta = y_root - d["y_start"]
                            # Compensate for canvas scrolling since drag started
                            scroll_now = _scroll_canvas.yview()[0] * _scroll_inner.winfo_reqheight()
                            scroll_delta = scroll_now - d.get("scroll_start", scroll_now)
                            new_y = idx * (row_h + gap) + delta + scroll_delta
                            new_y = max(0, min((len(_model_rows) - 1) * (row_h + gap), new_y))
                            try:
                                _model_rows[idx].place_configure(y=new_y)
                            except Exception:
                                pass

                            cursor_frame_y = new_y + row_h // 2
                            hover_slot = max(0, min(len(_model_rows) - 1,
                                                    int(cursor_frame_y / (row_h + gap))))
                            if hover_slot != d["empty_slot"]:
                                d["empty_slot"] = hover_slot
                                _model_commit_virtual_order(idx, hover_slot)

                        pop.after(0, _flush_model_motion)
                        _autoscroll_start()

                    def _on_model_drag_end(e, idx=_idx):
                        d = _model_drag
                        if not d["active"] or d["idx"] != idx:
                            return
                        target = d["empty_slot"]
                        d["active"] = False
                        _autoscroll_stop()
                        _model_ghost_destroy()
                        if target != idx:
                            _flush_model_vars()
                            _tmp_models.insert(target, _tmp_models.pop(idx))
                        _rebuild_model_rows()

                    handle.bind("<ButtonPress-1>",  _on_model_drag_start)
                    handle.bind("<B1-Motion>",       _on_model_drag_motion)
                    handle.bind("<ButtonRelease-1>", _on_model_drag_end)

                # Initial placement
                if _model_rows:
                    _models_frame.update_idletasks()
                    row_h = _model_rows[0].winfo_reqheight()
                    if row_h < 8:
                        row_h = 30
                    _model_drag["row_h"] = row_h
                    _model_place_rows()
                # Rebind mousewheel to any newly created child widgets
                _bind_mousewheel_recursive(_scroll_outer)

            def _add_model():
                _flush_model_vars()
                _tmp_models.append("")
                _rebuild_model_rows()
                _resize_pop()

            _rebuild_model_rows()

            ttk.Separator(pf, orient="horizontal").pack(fill="x", pady=(0, 10))

            # ── Section: BLOCKS PER REQUEST ───────────────────────────────────
            _bpr_label = ttk.Label(pf, text="BLOCKS PER REQUEST",
                      font=(_FONT_UI, 8, "bold"), foreground=C.get("dim","#888"))
            _bpr_label.pack(anchor="w", pady=(0, 4))

            _chunk_row = ttk.Frame(pf)
            _chunk_row.pack(fill="x", pady=(0, 2))

            _chunk_var = tk.StringVar(value=str(_tmp_chunk[0]))
            def _chunk_vcmd(P):
                return P == "" or (P.isdigit() and len(P) <= 7)
            _vcmd = (pop.register(_chunk_vcmd), "%P")
            ttk.Label(_chunk_row,
                      text="Subtitles sent per API call.\nLower = safer for flagged content.\nHigher = fewer calls.",
                      style="Dim.TLabel", justify="left").pack(side="left", anchor="w")

            # Wrap the entry in a frame that fills the row height vertically;
            # packing the entry inside with expand=True centers it perfectly
            # without using place(), so winfo_reqheight() stays accurate.
            _chunk_entry_wrap = ttk.Frame(_chunk_row)
            _chunk_entry_wrap.pack(side="right", fill="y")
            _chunk_entry = ttk.Entry(_chunk_entry_wrap, textvariable=_chunk_var, width=7,
                                     validate="key", validatecommand=_vcmd)
            _chunk_entry.pack(expand=True)

            ttk.Separator(pf, orient="horizontal").pack(fill="x", pady=(10, 8))

            # ── Save / Cancel ─────────────────────────────────────────────────
            def _save_gemini():
                # Flush StringVar values back to _tmp lists
                final_keys = []
                for v in _key_vars:
                    val = v.get().strip()
                    if val and val != "Paste key from a second Google account":
                        final_keys.append(val)
                final_models = [v.get().strip() for v in _model_vars if v.get().strip()]
                if not final_models:
                    messagebox.showwarning("No Models", "Please add at least one model.", parent=pop)
                    return
                if not final_keys:
                    if not messagebox.askyesno(
                        "No API Keys",
                        "No API keys are configured.\n\n"
                        "Gemini translation will be disabled until you add a key.\n\n"
                        "Save anyway?",
                        parent=pop,
                    ):
                        return

                _gemini_keys_state.clear()
                _gemini_keys_state.extend(final_keys)
                _gemini_models_state.clear()
                _gemini_models_state.extend(final_models)
                try:
                    chunk_val = int(_chunk_var.get())
                    chunk_val = max(50, min(1_000_000, chunk_val))
                except (ValueError, tk.TclError):
                    chunk_val = _gemini_chunk_state[0]   # keep last known good value
                    _chunk_var.set(str(chunk_val))       # restore display so field isn't blank
                _gemini_chunk_state[0] = chunk_val

                # Write directly into self._settings so save_settings() persists the real values
                self._settings.update({
                    "gemini_api_keys":        list(final_keys),
                    "gemini_api_key":         final_keys[0] if final_keys else "",
                    "gemini_models":          list(final_models),
                    "gemini_chunk_size":      chunk_val,
                    "gemini_key_warning_dismissed": _warn_dismissed[0],
                    "gemini_popup_geometry":  pop.geometry(),
                })
                self._save_settings()

                _update_gemini_badge()
                pop.destroy()

            def _close_gemini():
                self._settings["gemini_key_warning_dismissed"] = _warn_dismissed[0]
                self._settings["gemini_popup_geometry"] = pop.geometry()
                self._save_settings()
                pop.destroy()

            pop.protocol("WM_DELETE_WINDOW", _close_gemini)

            _btn_row = ttk.Frame(pf)
            _btn_row.pack(fill="x")
            _btn_row.columnconfigure(0, weight=1)
            _btn_row.columnconfigure(1, weight=1)

            # ── Cancel ────────────────────────────────────────────────────────
            _cancel_btn = ttk.Button(_btn_row, text="Cancel",
                                     style="GeminiCancel.TButton",
                                     command=_close_gemini)
            _cancel_btn.grid(row=0, column=0, sticky="ew", padx=(0, 4))

            # ── Save ──────────────────────────────────────────────────────────
            _save_btn = ttk.Button(_btn_row, text="Save",
                                   style="GeminiSave.TButton",
                                   command=_save_gemini)
            _save_btn.grid(row=0, column=1, sticky="ew", padx=(4, 0))

            # Restore last position (position only — size is driven by content via bindings)
            _gem_geo = self._settings.get("gemini_popup_geometry", "")
            if _gem_geo:
                _gm = re.search(r"([+-]\d+[+-]\d+)$", _gem_geo)
                if _gm:
                    try:
                        pop.geometry(_gm.group(1))
                        self._clamp_window_to_screen(pop)
                    except Exception:
                        pass

            pop.resizable(False, False)
            pop.minsize(330, 1)
            pop.maxsize(330, 99999)
            pop.transient(win)
            pop.grab_set()

            # Defer show: let Tk render all widgets so <Configure> fires on
            # _scroll_inner and _on_inner_resize sets the correct canvas height,
            # then _resize_pop fits the window — all before the user sees it.
            def _show_pop():
                pop.update_idletasks()
                _resize_pop()
                pop.focus_set()
                pop.deiconify()
            pop.after(0, _show_pop)



        # Configure button — MDL2 gear icon, ConfigIcon style
        _gemini_gear_frame = tk.Frame(af, width=32, height=28, bg=C["card"])
        _gemini_gear_frame.grid(row=0, column=2, padx=(6, 0), pady=3, sticky="e")
        _gemini_gear_frame.pack_propagate(False)
        _gemini_gear_frame.grid_propagate(False)
        _gemini_cfg_btn = ttk.Button(_gemini_gear_frame, text="\uE713",
                                     command=_open_gemini_popup,
                                     style="ConfigIcon.TButton")
        _gemini_cfg_btn.place(relx=0, rely=0, relwidth=1, relheight=1)


        tk.Frame(win, bg=C["border"], height=1).pack(fill="x")
        btn_row = ttk.Frame(win); btn_row.pack(fill="x", padx=22, pady=12)
        btn_row.columnconfigure(0, weight=1)
        btn_row.columnconfigure(1, weight=1)

        def _apply():
            if not any(v.get() for v in col_vars.values()):
                messagebox.showwarning("No columns selected",
                    "Please select at least one column.", parent=win); return
            prev_free  = self._settings.get("free_resize", True)
            prev_theme = self._settings.get("theme","Default")
            # Snapshot current column widths BEFORE applying (so they survive the apply)
            _current_widths = {}
            for cid, *_ in self.COLUMNS:
                try: _current_widths[cid] = self.tree.column(cid, "width")
                except Exception: pass
            for key, var in bool_vars.items(): self._settings[key] = var.get()
            for key, var in prov_vars.items(): self._settings[key] = var.get()
            self._settings.update({
                "free_resize": free_var.get(), "save_position": save_pos_var.get(), "row_height": rh_var.get(),
                "font_size": fs_var.get(), "oscom_api_key": oscom_var.get().strip(),
                "oscom_username": _oscom_username_var.get().strip(),
                "oscom_password": _oscom_password_var.get().strip(),
                "subdl_api_key": subdl_var.get().strip(),
                "gemini_api_keys": list(_gemini_keys_state),
                # Keep legacy key in sync with first key in list for backward compat
                "gemini_api_key": _gemini_keys_state[0] if _gemini_keys_state else "",
                "gemini_models": list(_gemini_models_state),
                "gemini_chunk_size": _gemini_chunk_state[0],
                "theme": theme_var.get(),
            })
            for key, var in col_vars.items(): self._settings[key] = var.get()
            self._settings["col_order"] = [key_to_cid[k] for k in check_order]
            # Restore column widths so Apply doesn't reset them
            self._settings["col_widths"] = _current_widths
            new_free = self._settings["free_resize"]
            if new_free and not prev_free:
                self.resizable(True, True)
                self.minsize(0, 0)
            elif not new_free and prev_free:
                # Lock to current size
                try:
                    geo = self.geometry()
                    m = _GEO_SIZE_RE.match(geo)
                    lock_w = int(m.group(1)) if m else DEFAULT_W
                    lock_h = int(m.group(2)) if m else DEFAULT_H
                except Exception:
                    lock_w, lock_h = DEFAULT_W, DEFAULT_H
                self._settings["win_geometry"] = "{}x{}".format(lock_w, lock_h)
                self.resizable(False, False)
                self.minsize(lock_w, lock_h)
            self._settings["settings_win_geometry"] = win.geometry()
            self._save_settings()
            if theme_var.get() != prev_theme:
                self._apply_theme()
            else:
                ttk.Style(self).configure("Treeview", rowheight=rh_var.get(),
                    font=(_FONT_UI, fs_var.get()))
                self._apply_settings_to_ui()
                # Always force a full row-value refresh so the [XX] language
                # indicator appears/disappears immediately when the Language
                # column is toggled — without this the fast sort path skips
                # _insert_sub and stale values remain on screen.
                self._tree_tags_dirty = True
                self._refresh_tree()
            win.destroy()

        ttk.Button(btn_row, text="Cancel", style="GeminiCancel.TButton",
                   command=_save_and_close).grid(row=0, column=0, sticky="ew", padx=(0, 4))
        ttk.Button(btn_row, text="Apply", style="GeminiSave.TButton", command=_apply).grid(row=0, column=1, sticky="ew", padx=(4, 0))

        # Restore last position (position only — not size, since settings window is non-resizable)
        _swin_geo = self._settings.get("settings_win_geometry", "")
        if _swin_geo:
            _m = re.search(r"([+-]\d+[+-]\d+)$", _swin_geo)
            if _m:
                win.update_idletasks()
                try:
                    win.geometry(_m.group(1))
                    self._clamp_window_to_screen(win)
                except Exception:
                    pass

    # ── search ─────────────────────────────────────────────────────────────────

    def _start_search(self):
        q = self.q_var.get().strip()
        if not q: messagebox.showwarning("Empty search","Please enter a title."); return
        if self._search_job and self._search_job.is_alive(): return
        # Collect all checked languages
        selected_langs = [LANGUAGES[name] for name, var in self._lang_checks.items() if var.get()]
        if not selected_langs:
            messagebox.showwarning("No language selected", "Please select at least one language.")
            return
        log_banner(self.video_path, q, ",".join(selected_langs))
        self._stop_event.clear()
        self._clear(keep_query=True)
        self.btn_search.config(state="disabled")
        self.btn_stop.config(state="normal")
        self.progress.start(10)
        self.status_var.set("Searching\u2026")
        self._search_job = threading.Thread(target=self._search_worker, args=(q, selected_langs), daemon=True, name="subfinder-search")
        self._search_job.start()

    def _stop_search(self):
        # Signal any search/translation thread to abort.
        # _search_job = search thread, _translate_job = translation thread.
        # Both share _stop_event which is polled between chunks/requests.
        if self._search_job and self._search_job.is_alive():
            self._stop_event.set()
            self.status_var.set("Stopping\u2026")
        if self._translate_job and self._translate_job.is_alive():
            self._stop_event.set()
            self.status_var.set("Stopping\u2026")
        # Kill all running sync subprocesses immediately (ffmpeg + sync tool).
        # _sync_procs is a set so there is no gap between ffmpeg extraction ending
        # and the sync tool starting — both are registered while alive.
        _procs = list(self._sync_procs)
        self._sync_procs.clear()
        for _sp in _procs:
            try:
                _sp.kill()
            except Exception:
                pass
        if _procs:
            self.status_var.set("Stopped")
        self.btn_stop.config(state="disabled")

    @staticmethod
    def _deduplicate(subs):
        seen = set(); unique = []
        for s in subs:
            key = (s.provider, str(s.sub_id))
            if key not in seen:
                seen.add(key); unique.append(s)
        unique.sort(key=lambda s: s.score, reverse=True)
        return unique

    def _search_worker(self, q, langs):
        # langs is a list of ISO-639-1 codes (e.g. ["en", "ar"])
        # Each provider is called ONCE with the full language list — no per-lang loop.
        all_subs      = []
        oscom_enabled = self._settings.get("provider_subliminal", False)
        lang_label    = ", ".join(langs)

        # ── OpenSubtitles.com DIRECT ──────────────────────────────────────────
        # Fires when an API key is configured AND the checkbox is enabled.
        # Unchecking the checkbox disables direct entirely — subliminal legacy
        # providers take over instead.  oscom_direct_ok tracks whether direct
        # actually returned results — used later for classification and to decide
        # whether subliminal should run at all.
        oscom_direct_ok = False
        if not self._stop_event.is_set() and oscom_enabled and _get_oscom_key():
            self.after(0, self.status_var.set,
                       "Searching OpenSubtitles.com ({})…".format(lang_label))
            try:
                subs = search_with_opensubtitlescom(
                    query=q, lang_code=langs, video_path=self.video_path,
                    release_hint=getattr(self, "_cd_filename", "") or "")
                all_subs.extend(subs)
                oscom_direct_ok = len(subs) > 0
            except Exception as exc:
                log.error("OS.com direct search crashed: %s\n%s",
                          exc, traceback.format_exc())

        # ── subliminal ────────────────────────────────────────────────────────
        # Runs when:
        #   • No API key configured (direct never attempted), OR
        #   • API key configured but direct returned 0 results (genuine failure),
        #     whether or not the OS.com checkbox is checked.
        # Provider selection:
        #   Key set (regardless of checkbox) → all providers incl. v3 (com first,
        #                                       v2 appended so v3 ranks higher)
        #   No key                           → legacy v2 only
        # The OS.com checkbox only gates the *direct* search — subliminal always
        # uses v3 providers when a key is available, so unchecking the box merely
        # disables the direct REST path without degrading subliminal results.
        if not self._stop_event.is_set() and not oscom_direct_ok and SUBLIMINAL_OK:
            if _get_oscom_key():
                # v3 providers first (higher quality), legacy v2 appended
                _v3 = [p for p in SUBLIMINAL_PROVIDERS_LIST
                       if p in ("opensubtitlescom",)]
                _v2 = [p for p in SUBLIMINAL_PROVIDERS_LIST
                       if p not in ("opensubtitlescom",)]
                subliminal_providers = _v3 + _v2 if (_v3 or _v2) else None
            else:
                subliminal_providers = [p for p in SUBLIMINAL_PROVIDERS_LIST
                                        if p not in ("opensubtitlescom",)]
            if subliminal_providers is None or subliminal_providers:
                self.after(0, self.status_var.set,
                           "Searching via subliminal ({})…".format(lang_label))
                _subliminal_failed = False
                try:
                    subs = search_with_subliminal(query=q, lang_code=langs,
                                                  video_path=self.video_path,
                                                  providers=subliminal_providers)
                    all_subs.extend(subs)
                except Exception as exc:
                    log.error("subliminal search crashed: %s\n%s",
                              exc, traceback.format_exc())
                    _subliminal_failed = True
                    self.after(0, self.status_var.set,
                               "subliminal search failed — check log for details")

        # ── SubDL ─────────────────────────────────────────────────────────────
        if not self._stop_event.is_set() and self._settings.get("provider_subdl", False):
            self.after(0, self.status_var.set, "Searching via SubDL ({})…".format(lang_label))
            try:
                subs = search_with_subdl(query=q, lang_code=langs, video_path=self.video_path)
                all_subs.extend(subs)
            except Exception as exc:
                log.error("SubDL search crashed: %s\n%s", exc, traceback.format_exc())

        was_stopped = self._stop_event.is_set()

        # ── Unified release-name scoring pass ─────────────────────────────────
        # Applies after ALL providers have returned results, so OS.com, SubDL,
        # and subliminal are treated equally.  Also fixes local files: for URLs
        # _cd_filename is set from Content-Disposition; for local files we derive
        # the same hint directly from the filename.
        if not was_stopped and all_subs:
            _vp = self.video_path or ""
            if _vp and not _URL_SCHEME_RE.match(_vp):
                # Local file — use clean filename as the release hint
                _release_hint = clean_filename(_vp)
            else:
                _release_hint = getattr(self, "_cd_filename", "") or ""
            if _release_hint:
                _hint_n = _norm_release_name(_release_hint)
                for _s in all_subs:
                    # Skip already AI/machine-translated subs (they carry their own penalty)
                    _rel_n = _norm_release_name(_s.release) if _s.release else ""
                    if _rel_n and _hint_n:
                        if _hint_n == _rel_n:
                            _s.score = min(_s.score + 0.15, 0.97)
                        elif _hint_n in _rel_n or _rel_n in _hint_n:
                            _s.score = min(_s.score + 0.07, 0.89)

        _d = self._deduplicate(all_subs)
        if not was_stopped:
            log.info("Total unique results: %d", len(_d))

        # ── Primary / secondary classification ────────────────────────────────
        # direct_ok=True  → only direct+SubDL results shown; subliminal results
        #                    dropped entirely (not even shown as secondary).
        # direct_ok=False → checkbox controls whether subliminal v3 providers
        #                    are primary or secondary.
        _primary = _primary_providers(oscom_enabled, direct_ok=oscom_direct_ok)
        if oscom_direct_ok:
            # Drop all subliminal results — direct worked, they are not needed
            _d = [s for s in _d if s.provider in _primary]
        # Promote v2 to primary when no v3 subliminal results are present
        # (i.e. no key — v3 never ran). This way v2 results appear in the
        # main list instead of the collapsed section.
        _has_v3 = any(s.provider == "opensubtitlescom" for s in _d)
        _effective_primary = _primary | ({"opensubtitles"} if not _has_v3 else set())
        primary_results   = [s for s in _d if s.provider in _effective_primary]
        secondary_results = [s for s in _d if s.provider not in _effective_primary]
        multi_lang = len(langs) > 1
        self.after(0, self._done_searching, True, was_stopped,
                   primary_results, secondary_results, multi_lang)

    def _done_searching(self, from_search: bool = True, was_stopped: bool = False,
                        primary_results=None, secondary_results=None, multi_lang=None):
        if from_search:
            self.progress.stop()
            self.btn_search.config(state="normal")
            self.btn_stop.config(state="disabled")
        # Apply results on the main thread — safe for Tkinter
        if primary_results is not None:
            self.results = primary_results
        if secondary_results is not None:
            self.secondary_results = secondary_results
        if multi_lang is not None:  # Fix: written here on main thread, not in background thread
            self._multi_lang_search = multi_lang
        self._secondary_expanded = False
        n, ns = len(self.results), len(self.secondary_results)
        total = n + ns
        if was_stopped:
            self.status_var.set("Search stopped — {} result{}".format(total, "s" if total != 1 else ""))
        else:
            self.status_var.set("{} subtitle{} found".format(total, "s" if total != 1 else ""))
        self.count_var.set("{} results  +  {} more".format(n,ns) if ns else "{} results".format(n))

        if self.video_path and self.video_path.strip() and (self.results or self.secondary_results):
            self._save_session_snapshot()

        self._refresh_tree()
        children = self.tree.get_children()
        if children:
            self.tree.focus(children[0])
            self.tree.selection_set(children[0])

    def _save_session_snapshot(self):
        """Persist the current results lists to the session cache.

        Extracted from _done_searching so that _add_sub_to_results (and any
        other code that mutates self.results outside of a search) can keep the
        on-disk cache in sync without duplicating the session-save logic.
        """
        if not (self.video_path and self.video_path.strip()):
            return
        if not (self.results or self.secondary_results):
            return
        try:
            sessions = _load_session_cache()
            _q  = self.q_var.get()
            _ck = _q.lower().strip() if _q and _q.strip() else _content_key(self.video_path)
            sessions.pop(_ck, None)
            sessions.pop(_content_key(self.video_path), None)
            sessions.pop(self.video_path, None)
            sessions[_ck] = {
                "video_path":            self.video_path,
                "query":                 self.q_var.get(),
                "lang":                  self.lang_var.get(),
                "multi_lang":            self._multi_lang_search,
                "results":               self.results,
                "secondary_results":     self.secondary_results,
                "mpv_primary_sub_id":    self._mpv_primary_sub_id,
                "mpv_secondary_sub_id":  self._mpv_secondary_sub_id,
                "mpv_primary_sids":      dict(self._mpv_primary_sids),
                "mpv_secondary_sids":    dict(self._mpv_secondary_sids),
            }
            _save_session_cache(sessions)
        except Exception as e:
            log.warning("Could not save session snapshot: %s", e)

    def _sort_key(self, sub):
        sort = self.sort_var.get()
        if sort == "Score":    return sub.score
        if sort == "Language": return sub.lang_display().lower()
        if sort == "Format":   return sub.fmt_display()
        if sort == "Provider": return sub.provider
        if sort == "Release":  return (sub.release or "").lower()
        return sub.score

    def _is_dup_downloaded(self, sub):
        """Return True if this sub's dl_url was already used for a *different* sub_id
        (e.g. same season-pack zip downloaded for another episode).
        Promoted from a nested function so _refresh_tree_by can also call it."""
        if not sub.dl_url: return False
        peer_id = self._last_dl_path.get("dlurl:" + sub.dl_url)
        if not peer_id: return False
        if peer_id == sub.sub_id: return False  # it's the primary downloaded entry
        peer_path = self._last_dl_path.get(peer_id, "")
        return bool(peer_path) and Path(peer_path).is_file()

    def _refresh_tree(self):
        reverse = (self._sort_direction == "desc")
        self._populate_tree(key_fn=self._sort_key, reverse=reverse)

    def _update_heading_arrows(self, active_col="", direction=""):
        arrow_map = {"asc": " \u25b2", "desc": " \u25bc", "": ""}
        arrow = arrow_map.get(direction, "")
        for cid, _, head, _, _anc in self.COLUMNS:
            try:
                self.tree.heading(cid, text=(head + arrow) if (cid == active_col and arrow) else head)
            except Exception:
                pass
        self._active_sort_col = active_col

    def _col_sort(self, col):
        sort_map = {
            "score":    "Score",
            "language": "Language",
            "fmt":      "Format",
            "provider": "Provider",
            "release":  "Release",
        }
        cur = self._col_sort_state.get(col, "none")
        if cur == "none":
            new_dir = "desc"
        elif cur == "desc":
            new_dir = "asc"
        else:
            new_dir = "none"
        self._col_sort_state[col] = new_dir

        if new_dir == "none":
            self._update_heading_arrows("", "")
            self._sort_direction = "desc"
            self.sort_var.set("Score")
            return

        self._sort_direction = new_dir
        self._update_heading_arrows(col, new_dir)

        sort_name = sort_map.get(col)
        if sort_name:
            self.sort_var.set(sort_name)
        else:
            self._refresh_tree_by(col, new_dir)

    def _refresh_tree_by(self, col, direction):
        """Sort tree by an arbitrary column not covered by sort_var."""
        _key_map = {
            "score":    lambda s: s.score,
            "release":  lambda s: (s.release or "").lower(),
            "language": lambda s: s.lang_display().lower(),
            "provider": lambda s: s.provider,
            "fmt":      lambda s: s.fmt_display(),
        }
        key_fn  = _key_map.get(col, lambda s: s.score)
        reverse = (direction == "desc")
        self._populate_tree(key_fn=key_fn, reverse=reverse)

    def _insert_sub(self, sub, existing_files: set = None):
        """Insert a single Sub row into the treeview with the correct colour tag.

        existing_files is a pre-built set of file path strings confirmed to exist
        on disk, built once per _populate_tree call to avoid a stat() syscall for
        every row on every refresh (which causes visible lag on slow filesystems).
        If not provided, falls back to the live is_file() check for safety.

        Each row is inserted with iid=sub.sub_id so that _sort_tree_inplace()
        can call tree.move(iid, "", index) to reorder without delete/re-insert.
        If the iid already exists (e.g. on a tag-only refresh) the existing item
        is updated in place rather than re-inserted.
        """
        pct = sub.score_pct()
        cached_path = self._last_dl_path.get(sub.sub_id, "")
        if sub.sub_id and sub.sub_id in (self._mpv_primary_sub_id, self._mpv_secondary_sub_id):
            tag = "mpv_loaded"
        elif cached_path and (
            cached_path in existing_files if existing_files is not None
            else Path(cached_path).is_file()
        ):
            tag = "downloaded"
        elif self._is_dup_downloaded(sub):
            tag = "dup_downloaded"
        else:
            tag = ("excellent" if pct >= 80 else "good" if pct >= 60
                   else "fair" if pct >= 40 else "poor")
        release_display = sub.release or "\u2014"
        lang_col_visible = self._settings.get("col_language", True)
        # Simple, consistent rule for every row and every provider:
        #   - Language column hidden → prepend [XX] to the release display.
        #   - Language column visible → release is shown clean; column handles it.
        # sub.release is always stored clean (no embedded prefix), so there is
        # no stripping or special-casing needed here.
        if not lang_col_visible and sub.language:
            _code = _lang_code_tag(sub.language)
            if _code:
                release_display = "[{}] {}".format(_code, release_display)
        vals = ("{}%".format(pct), release_display, sub.lang_display(),
                _provider_display(sub.provider), sub.fmt_display())
        # Use the sub_id as a stable iid so move()-based sorting works without
        # destroying and recreating rows.  If the item already exists (e.g. a
        # tag refresh after a download), update it in place instead.
        iid = sub.sub_id or ""
        if iid and self.tree.exists(iid):
            self.tree.item(iid, values=vals, tags=(tag,))
        else:
            try:
                self.tree.insert("", "end", iid=iid, values=vals, tags=(tag,))
            except tk.TclError:
                # Fallback: iid collision from a non-sub row — insert without iid
                self.tree.insert("", "end", values=vals, tags=(tag,))

    def _populate_tree(self, key_fn, reverse):
        """Clear the treeview and repopulate it sorted by key_fn.

        Strategy: always do a full rebuild on the first populate (or when the
        set of rows changes — new search, new result added, row deleted).
        On a pure sort-order change the set of rows is identical, so we call
        _sort_tree_inplace() instead, which uses tree.move() to reorder existing
        items without destroying and recreating them.  This eliminates the
        visible flash that occurs when every row is deleted and re-inserted on
        each sort interaction.
        """
        self._active_sort_key_fn = key_fn   # keep in sync so _selected() uses the same order
        def _sorted(lst): return sorted(lst, key=key_fn, reverse=reverse)

        # Build a set of file paths that are confirmed to exist on disk ONCE
        # before the insert loop.  Each _insert_sub call then does a fast set
        # lookup (O(1)) instead of a stat() syscall, eliminating N disk hits per
        # refresh on slow or network filesystems.
        # Only include genuine file-path entries (not dlurl:/pack:/direct_url:
        # metadata values, which are sub_ids or JSON strings, not paths).
        existing_files: set = set()
        for _k, _v in self._last_dl_path.items():
            if isinstance(_v, str) and not _k.startswith(("dlurl:", "pack:", "direct_url:")):
                try:
                    if Path(_v).is_file():
                        existing_files.add(_v)
                except Exception:
                    pass

        # Compute the full desired set of sub_ids in sorted order (primary +
        # optionally secondary).  Compare against what is currently in the tree.
        # If the sets match we can reorder in-place; otherwise do a full rebuild.
        desired_primary   = [s.sub_id for s in _sorted(self.results)]
        desired_secondary = ([s.sub_id for s in _sorted(self.secondary_results)]
                             if self._secondary_expanded else [])
        desired_ids = set(desired_primary + desired_secondary)

        current_children = self.tree.get_children()
        current_sub_ids  = {iid for iid in current_children
                            if "toggle_row" not in self.tree.item(iid, "tags")}

        # ── Fast path: same rows, different order — reorder in place ──────────
        if current_sub_ids == desired_ids and current_sub_ids:
            # Only re-push tags when something actually changed (download
            # completed, mpv sid updated).  Pure re-sorts skip the N
            # tree.item() calls entirely, saving the round-trips.
            if self._tree_tags_dirty:
                # Only iterate subs that are currently visible in the tree.
                # Iterating all of secondary_results when collapsed would call
                # _insert_sub on items not yet attached to root, causing
                # tree.insert() to add them there; set_children() then detaches
                # them, permanently orphaning those iids and breaking expand.
                visible_subs = self.results + (
                    self.secondary_results if self._secondary_expanded else [])
                for sub in visible_subs:
                    self._insert_sub(sub, existing_files)
                self._tree_tags_dirty = False
            self._sort_tree_inplace(desired_primary, desired_secondary)
            return

        # ── Slow path: row set changed — full rebuild ─────────────────────────
        # Using *-unpacking on get_children() passes every item ID as a separate
        # positional argument. With 500+ results (subs_per_page=500 per provider)
        # this generates a Tcl command string tens of kilobytes long, which can
        # freeze or crash Tk. A loop is O(n) Tcl calls but safe at any count.
        for _ch in current_children:
            self.tree.delete(_ch)
        # Also purge any orphaned iids that were detached from root by a prior
        # set_children() call (expand→collapse cycle) but are still registered in
        # the tree's internal item table.  They are invisible to get_children()
        # above, so the loop above misses them.  If left alive, _insert_sub will
        # see tree.exists(iid)=True for a new result whose sub_id collides with
        # an orphan and silently update-in-place instead of inserting — leaving
        # the new row detached and invisible.
        for _s in self.results + self.secondary_results:
            _iid = _s.sub_id or ""
            if _iid and self.tree.exists(_iid):
                try:
                    self.tree.delete(_iid)
                except tk.TclError:
                    pass
        for sub in _sorted(self.results):
            self._insert_sub(sub, existing_files)

        if self.secondary_results:
            ns  = len(self.secondary_results)
            lbl = ("\u25BC  {} more results \u2014 click to collapse" if self._secondary_expanded
                   else "\u25BA  {} more results \u2014 click to expand").format(ns)
            self.tree.insert("", "end", iid="__toggle__", values=("", lbl, "", "", ""), tags=("toggle_row",))
            if self._secondary_expanded:
                for sub in _sorted(self.secondary_results):
                    self._insert_sub(sub, existing_files)

    def _sort_tree_inplace(self, primary_ids: list, secondary_ids: list):
        """Reorder existing treeview rows using a single set_children() call.

        set_children("", *ordered_ids) replaces the root's child list in one
        atomic Tcl call — the widget updates its internal order and schedules a
        single deferred redraw.  This is strictly better than N sequential
        move() calls, each of which crosses the Python→Tcl bridge and can
        produce intermediate visible states on Windows.

        primary_ids and secondary_ids are lists of sub_ids in the desired
        display order.  The toggle row sits between the two groups.
        Translated rows sort by their own score (1.0 = 100%) and are NOT
        pinned after their parent — they float to the top naturally.
        """
        toggle_present = self.tree.exists("__toggle__")
        # Filter out rows that no longer exist in the tree (safety guard).
        def _existing(ids):
            return [iid for iid in ids if self.tree.exists(iid)]

        desired_order = (
            _existing(primary_ids)
            + (["__toggle__"] if toggle_present else [])
            + _existing(secondary_ids)
        )

        # Short-circuit: if the tree is already in the right order, do nothing.
        # get_children() is one Tcl round-trip; the tuple comparison is O(n) in
        # Python and avoids even a single set_children() call when the order is
        # already correct (e.g. repeated clicks on the same column heading).
        if self.tree.get_children() == tuple(desired_order):
            return

        # One Tcl call — atomically replaces the root child list.
        self.tree.set_children("", *desired_order)

    def _clear(self, keep_query=False):
        # Item 8: Preserve local, embedded, and translated rows that don't come
        # from search results — they should survive a new search for the same video.
        # Rows are only preserved when the same video is still playing.
        _vp = self.video_path or ""
        _is_local = _vp and not _URL_SCHEME_RE.match(_vp)
        _non_search_providers = {"local", "embedded", "translated"}
        if _is_local:
            _preserved = [s for s in self.results + self.secondary_results
                          if s.provider in _non_search_providers]
        else:
            _preserved = []
        # Explicitly delete any iids that are still known from the current result
        # sets before discarding the lists.  Items that were orphaned by a prior
        # expand+collapse cycle (detached from root by set_children but still
        # registered in the tree's internal item table) are invisible to
        # get_children() and would survive the loop below — leaving stale iids
        # that collide with new search results and cause _insert_sub to silently
        # update-in-place instead of inserting, making new rows invisible.
        _all_known = self.results + self.secondary_results
        for _s in _all_known:
            _iid = _s.sub_id or ""
            if _iid and self.tree.exists(_iid):
                try:
                    self.tree.delete(_iid)
                except tk.TclError:
                    pass
        self.results = list(_preserved); self.secondary_results = []; self._secondary_expanded = False
        self._active_sort_key_fn = None
        self._multi_lang_search = False
        # Delete all root-attached rows (the preserved subs are re-inserted by
        # _populate_tree on the next refresh).
        for _ch in list(self.tree.get_children()):
            self.tree.delete(_ch)
        self.count_var.set(""); self.btn_load.config(state="disabled")
        if not keep_query: self.q_var.set("")
        if self.detail_visible: self._toggle_detail()

    # ── selection ─────────────────────────────────────────────────────────────

    def _selected(self):
        sel = self.tree.selection()
        if not sel: return None
        item = sel[0]
        if "toggle_row" in self.tree.item(item, "tags"): return None
        # Fast path: iid IS the sub_id — look it up directly in both result lists.
        # This replaces the old positional-index approach and is immune to the
        # toggle-row offset calculation that was previously required.
        all_subs = self.results + self.secondary_results
        for sub in all_subs:
            if sub.sub_id == item:
                return sub
        # Fallback (handles any row inserted without a sub_id iid): positional lookup.
        all_items  = list(self.tree.get_children())
        idx        = all_items.index(item)
        toggle_pos = next((i for i, it in enumerate(all_items)
                           if "toggle_row" in self.tree.item(it, "tags")), None)
        reverse = (self._sort_direction == "desc")
        key_fn  = self._active_sort_key_fn if self._active_sort_key_fn is not None else self._sort_key
        ps = sorted(self.results,           key=key_fn, reverse=reverse)
        ss = sorted(self.secondary_results, key=key_fn, reverse=reverse)
        if toggle_pos is None or idx < toggle_pos:
            return ps[idx] if idx < len(ps) else None
        sec_idx = idx - toggle_pos - 1
        return ss[sec_idx] if 0 <= sec_idx < len(ss) else None

    def _on_select(self, _e=None):
        sub = self._selected()
        # Guard: set_children() fires <<TreeviewSelect>> even during a pure
        # reorder (same row still selected).  Calling btn_load.config() on every
        # such event triggers the native ttk theme's state-transition animation
        # on all toolbar buttons, producing the visible flash on sort/reorder.
        # Only update the button state when the selected iid actually changes.
        cur_iid = sub.sub_id if sub else ""
        if cur_iid != self._last_selected_iid:
            self._last_selected_iid = cur_iid
            self.btn_load.config(state="normal" if sub else "disabled")
        if sub and self.detail_visible:
            self._update_detail(sub)

    def _toggle_detail(self):
        if self.detail_visible:
            self.detail_frame.pack_forget()
            self.detail_visible = False
            if self._pre_detail_h:
                geo = self.geometry()
                m = _GEO_SIZE_RE.match(geo)
                if m:
                    self.geometry("{}x{}{}".format(m.group(1), self._pre_detail_h, m.group(3)))
        else:
            geo = self.geometry()
            m = _GEO_SIZE_RE.match(geo)
            if m:
                self._pre_detail_h = int(m.group(2))
            sub = self._selected()
            if sub:
                self._update_detail(sub)
            self.detail_frame.pack(fill="x", padx=22, pady=(0, 12), after=self._bottom_container)
            self.detail_visible = True
            self.update_idletasks()
            if m:
                extra = self.detail_frame.winfo_reqheight() + 16
                self.geometry("{}x{}{}".format(
                    m.group(1), int(m.group(2)) + extra, m.group(3)))

    def _update_detail(self, sub):
        info = ("Provider : {}\nRelease  : {}\n"
                "Format   : {}  |  Score : {}%\n"
                "URL      : {}").format(
            sub.provider, sub.release,
            sub.fmt_display(), sub.score_pct(), sub.dl_url)
        self.detail_text.config(state="normal")
        self.detail_text.delete("1.0","end")
        self.detail_text.insert("end", info)
        self.detail_text.config(state="disabled")

    # ── download & load ───────────────────────────────────────────────────────

    def _do_load(self, close_after=False, load_fn=None):
        sub = self._selected()
        if not sub: return
        # Check cache first
        cached = self._last_dl_path.get(sub.sub_id)
        if cached and Path(cached).is_file():
            # If the cached path is an archive (no subtitle was found last time),
            # re-trigger the "open with archive app" dialog instead of silently
            # reporting "From cache" for a result that contains no subtitles.
            if Path(cached).suffix.lower() not in _SUB_EXTENSIONS:
                log.info("cache hit is archive-only (no subtitle): %s", cached)
                self._dl_archive_only(cached, sub)
                return
            log.info("cache hit: %s", cached)
            self.status_var.set("\u2713 From cache: {}".format(Path(cached).name))
            self._dl_ok(cached, sub, close_after, from_cache=True, load_fn=load_fn)
            return
        self.btn_load.config(state="disabled")
        self.status_var.set("Downloading\u2026")
        self.progress.start(10)
        threading.Thread(target=self._dl_worker, args=(sub, close_after, load_fn), daemon=True, name="subfinder-download").start()

    def _do_load_secondary(self):
        self._do_load(close_after=False, load_fn=load_subtitle_into_mpv_secondary)

    def _dl_worker(self, sub, close_after=False, load_fn=None):
        log.info("download requested: provider=%s  release=%r", sub.provider, sub.release)
        # Compute the release-name stem for the final file before downloading.
        # Strip any subtitle extension that subliminal may include in the release name.
        raw_stem  = sub.release or sub.sub_id
        if Path(raw_stem).suffix.lower() in _SUB_EXTENSIONS:
            raw_stem = Path(raw_stem).stem
        safe_stem = re.sub(r'[\\/:*?"<>|]', "_", raw_stem).strip(" .")
        if not safe_stem:
            safe_stem = sub.sub_id
        dest_dir = Path(self.video_path).parent if (
            self.video_path and Path(self.video_path).is_file()) else TEMP_DIR
        # Download — the function writes to TEMP_DIR with its own naming.
        # We rename in place immediately after so only one file ever exists.
        # Pre-check: if a pack: entry already exists for this sub, the archive is
        # already on disk — this will be a cache extraction, not a network download.
        _pack_key = ("pack:" + hashlib.md5(sub.dl_url.encode("utf-8")).hexdigest()) if sub.dl_url else ""
        _from_pack_cache = bool(_pack_key and _load_cache_index().get(_pack_key))
        path = None
        try:
            if sub.provider == "subdl":
                path = download_with_subdl(sub)
            elif sub.provider == "opensubtitlescom_direct":
                path = download_with_opensubtitlescom(sub, video_path=self.video_path)
            else:
                path = download_with_subliminal(sub, video_path=self.video_path)
        except Exception as exc:
            log.error("Download crash: %s\n%s", exc, traceback.format_exc())
        # Archive downloaded but contains no subtitle files
        if isinstance(path, tuple) and len(path) == 2 and path[0] is _ARCHIVE_ONLY:
            self.after(0, self._dl_archive_only, path[1], sub)
            return
        if not path or not Path(path).is_file():
            self.after(0, self._dl_fail,
                "Download failed for:\n{}\n\nCheck the log for details:\n{}".format(sub.release, LOG_FILE))
            return
        # Now we have the real extension.
        ext = Path(path).suffix or ".srt"

                # Detect if this is a season pack by checking if it lacks a specific episode tag
        # (This matches the exact logic the script already uses to cache packs)
        _has_ep_tag = bool(_RE_EP_TAG.search(sub.release))
        is_season_pack = (sub.provider == "subdl" and sub.target_episode is not None and not _has_ep_tag)

        # Preserve the original extracted filename ONLY for season packs.
        # For individual episodes, use the release name.
        if is_season_pack:
            _raw_pack_stem = Path(path).stem
            safe_stem = re.sub(r'[\\/:*?"<>|]', "_", _raw_pack_stem).strip(" .")
            if not safe_stem:
                safe_stem = sub.sub_id  # fallback if stem is entirely reserved chars
            
        # Capture the stable TEMP_DIR path BEFORE any rename so _dl_ok can
        # index the original location (visible to cleanup) rather than the
        # video-adjacent copy (which _cleanup_temp_dir never sweeps).
        temp_path_stable = path
        dest = dest_dir / "{}{}".format(safe_stem, ext)
        _c = 1
        while dest.exists() and dest.resolve() != Path(path).resolve():
            dest = dest_dir / "{} ({}){}".format(safe_stem, _c, ext)
            _c += 1
        if dest.resolve() != Path(path).resolve():
            try:
                Path(path).rename(dest)
            except OSError:
                shutil.copy2(path, dest)
                Path(path).unlink(missing_ok=True)
        # Touch the file so its mtime reflects now, not the timestamp embedded
        # inside the archive it was extracted from.  Without this, the TTL check
        # in _load_cache_index sees an old mtime and evicts the file immediately.
        try:
            dest.touch()
        except Exception:
            pass
        final_path = str(dest)
        log.info("download complete: %s", final_path)
        # Pass temp_path_stable as the cache path.  If the file was renamed out of
        # TEMP_DIR, temp_path_stable no longer exists and _dl_ok's guard
        # (Path(temp_path).is_file()) falls back to final_path automatically.
        self.after(0, self._dl_ok, final_path, sub, close_after, _from_pack_cache, temp_path_stable, is_season_pack, load_fn)

    def _dl_ok(self, path, sub, close_after=False, from_cache=False, temp_path=None, is_season_pack=False, load_fn=None):
        self.progress.stop()
        self.btn_load.config(state="normal")
        if from_cache:
            # Direct cache hit: status already set by _do_load.
            # Season pack cache extraction: _do_load set 'Downloading…' so update it now.
            if self.status_var.get().startswith("Downloading"):
                self.status_var.set("\u2713 From cache: {}".format(Path(path).name))
        else:
            self.status_var.set("\u2713 Downloaded: {}".format(Path(path).name))
            # Silently re-encode to UTF-8 if the file isn't already.
            # This fixes garbled Arabic, Hebrew, CJK, and CP-1252 subtitles
            # without requiring any user action.
            if Path(path).suffix.lower() in _SUB_EXTENSIONS:
                threading.Thread(target=_ensure_utf8, args=(path,), daemon=True, name="subfinder-utf8-fix").start()

        # Persist to cache index.
        # For season packs, always index the final_path (the copy next to the video)
        # because temp_path_stable was renamed away during _dl_worker — it no longer
        # exists and must never be used.  Indexing the stale temp path is the root
        # cause of Strip HI / Translate / Auto sync all failing on season packs:
        # every action reads cached_path from _last_dl_path and operates on a file
        # that is gone, while mpv is playing the copy next to the video.
        # For normal downloads, keep the existing behaviour: prefer temp_path so the
        # cache survives if the user moves or renames the video file.
        if is_season_pack:
            cache_path = path   # final_path next to the video — the only copy that exists
        else:
            cache_path = temp_path if temp_path and Path(temp_path).is_file() else path
        with self._last_dl_path_lock:
            self._last_dl_path[sub.sub_id] = cache_path
            # Also store the final path actually passed to mpv (may differ from
            # cache_path when the file is renamed next to the video).  Used by
            # _remove_from_mpv's filename fallback to match mpv's external-filename.
            if path != cache_path:
                self._last_dl_path["loaded:" + sub.sub_id] = path
            if sub.dl_url:
                self._last_dl_path["dlurl:" + sub.dl_url] = sub.sub_id
        with _cache_index_lock:
            idx = _load_cache_index(autosave=False)
            idx[sub.sub_id] = cache_path
            if sub.dl_url:
                idx["dlurl:" + sub.dl_url] = sub.sub_id

            # If this was a SubDL season pack, store its metadata so we can surface it
            # for other episodes of the same season without a fresh API search.
            # is_season_pack is passed in from _dl_worker, which determined it from the
            # actual zip contents — more reliable than re-checking the release name here,
            # because range-tagged releases like "Show.S01E01-E13" would falsely match
            # _RE_EP_TAG and prevent the pack: entry from ever being written.
            if is_season_pack and sub.provider == "subdl" and sub.dl_url:
                zip_key  = hashlib.md5(sub.dl_url.encode("utf-8")).hexdigest()
                # Check for the archive in both .zip and .rar forms (RAR may have been renamed)
                zip_dest = _archive_dest_for(zip_key, ".rar", label=sub.release)
                if not (zip_dest.is_file() and zip_dest.stat().st_size >= 10):
                    zip_dest = _archive_dest_for(zip_key, ".zip", label=sub.release)
                if zip_dest.is_file() and zip_dest.stat().st_size >= 10:
                    zip_ext  = zip_dest.suffix  # ".zip" or ".rar"
                    pack_key = "pack:" + zip_key
                    # Strip the _ep{N} suffix to get the base sub_id so
                    # find_cached_season_packs reconstructs the exact same id
                    # that search_with_subdl produces — prevents duplicate rows.
                    _base_sub_id = re.sub(r"_ep\d+$", "", sub.sub_id)
                    idx[pack_key] = json.dumps({
                        "dl_url":      sub.dl_url,
                        "release":     sub.release,
                        "language":    sub.language,
                        "fmt":         sub.fmt,
                        "downloads":   sub.downloads,
                        "zip_key":     zip_key,
                        "zip_ext":     zip_ext,
                        "label":       sub.release,
                        "base_sub_id": _base_sub_id,
                    })

            _save_cache_index(idx)

        # Update the sub's format from the real downloaded file extension.
        # SubDL entries often have fmt="" (displayed as "?") until the file is known.
        real_ext = Path(path).suffix.lstrip(".").lower()
        if real_ext and real_ext in {"srt", "ass", "ssa", "vtt", "sub"}:
            sub.fmt = real_ext

        self._tree_tags_dirty = True
        self._refresh_tree()
        self._on_select()
        self._save_session_snapshot()

        # Snapshot track-list before loading so we can identify the new sid.
        _tl_before = _ipc_command(["get_property", "track-list"])
        _before_ids = set()
        if _tl_before is not None:
            for _t in (_tl_before.get("data") or []):
                if _t.get("type") == "sub":
                    _before_ids.add(_t["id"])

        loaded = (load_fn or load_subtitle_into_mpv)(path)

        if loaded:
            # Try to capture the mpv sid for the track we just added so we can
            # offer "Remove from mpv" in the right-click menu later.
            # Only attempt this when IPC is available (before_ids snapshot succeeded).
            # Skip when a custom load_fn was provided that is NOT one of the two
            # standard mpv loaders — custom load_fns (e.g. _strip_hi_after_dl) handle
            # their own sid capture internally, and running _try_capture_sid here would
            # race with that capture and corrupt _mpv_primary_sids/_mpv_primary_sub_id.
            _standard_loaders = (load_subtitle_into_mpv, load_subtitle_into_mpv_secondary)
            _load_fn_is_standard = load_fn is None or load_fn in _standard_loaders
            if _tl_before is not None and _load_fn_is_standard:
                def _try_capture_sid(attempt, before_ids=_before_ids,
                                     is_secondary=(load_fn is load_subtitle_into_mpv_secondary)):
                    """Non-blocking sid capture — polls via after() so the UI stays responsive."""
                    _tl_after = _ipc_command(["get_property", "track-list"])
                    _new_sid = None
                    if _tl_after is not None:
                        for _tr in (_tl_after.get("data") or []):
                            if _tr.get("type") == "sub" and _tr["id"] not in before_ids:
                                _new_sid = _tr["id"]
                                break
                    if _new_sid is not None:
                        if is_secondary:
                            self._mpv_secondary_sub_id = sub.sub_id
                            self._mpv_secondary_sids[sub.sub_id] = _new_sid
                        else:
                            self._mpv_primary_sub_id = sub.sub_id
                            self._mpv_primary_sids[sub.sub_id] = _new_sid
                        log.info("mpv sid captured: sub_id=%s sid=%s", sub.sub_id, _new_sid)
                        self._save_session_snapshot()
                        self._tree_tags_dirty = True
                        self._refresh_tree()
                        if close_after:
                            self.destroy()
                    elif attempt < 8:
                        self.after(200, _try_capture_sid, attempt + 1)
                    else:
                        # All attempts exhausted without finding a new sid — still
                        # honour close_after so the window closes if requested.
                        if close_after:
                            self.destroy()
                _try_capture_sid(0)
            else:
                if close_after:
                    self.destroy()
        else:
            if sys.platform == "win32":
                _ipc_hint = (
                    "  \u2022 Install pywin32 for auto-loading:\n"
                    "    pip install pywin32"
                )
            else:
                _ipc_hint = (
                    "  \u2022 Set input-ipc-server=/tmp/mpv-socket in mpv.conf\n"
                    "    for auto-loading next time."
                )
            messagebox.showinfo("Ready",
                "Subtitle saved as:\n{}\n\n"
                "To load it in mpv:\n"
                "  \u2022 Drag the .srt file into the mpv window, OR\n"
                "  \u2022 Use mpv\u2019s right-click menu \u2192 Subtitles \u2192 Load, OR\n"
                "{}".format(path, _ipc_hint))

    def _dl_fail(self, reason):
        self.progress.stop()
        self.btn_load.config(state="normal")
        self.status_var.set("Download failed")
        messagebox.showerror("Download Failed", reason)

    def _reload_current_sub_in_mpv(self):
        """Re-add the currently loaded primary subtitle to mpv after an in-place file edit
        (HI strip, sync).  No-op if no subtitle is loaded or the file is gone.
        """
        try:
            sid = self._mpv_primary_sub_id
            if not sid:
                return
            path = self._last_dl_path.get(sid, "")
            if not path or not Path(path).is_file():
                return
            mpv_sid = self._mpv_primary_sids.get(sid)

            if mpv_sid is not None:
                _ipc_command(["sub-remove", mpv_sid])
                # Wait for mpv to finish processing the remove before adding
                # the subtitle back — on Windows the IPC pipe can be slow and
                # a back-to-back sub-add arrives before sub-remove completes,
                # leaving mpv with no subtitle selected (-/10).
                deadline = _time_module.time() + 1.0
                while _time_module.time() < deadline:
                    try:
                        tl = _ipc_command(["get_property", "track-list"])
                        if tl is not None:
                            cur_ids = {t.get("id") for t in (tl.get("data") or []) if t.get("type") == "sub"}
                            if mpv_sid not in cur_ids:
                                break  # old sid is gone, safe to add
                    except Exception:
                        break
                    _time_module.sleep(0.05)

            # Snapshot track-list AFTER remove (not before) so that when mpv
            # reuses the same sid number for the re-added track, the diff still
            # catches it.  If we snapshot before the remove, the old sid is in
            # before_ids and the new (identical) sid never appears in the diff.
            before_ids: set = set()
            try:
                tl = _ipc_command(["get_property", "track-list"])
                if tl is not None:
                    before_ids = {t.get("id") for t in (tl.get("data") or []) if t.get("type") == "sub"}
            except Exception:
                pass

            ok = load_subtitle_into_mpv(path)
            if not ok:
                log.warning("_reload_current_sub_in_mpv: sub-add failed for %s", path)
                return

            log.info("_reload_current_sub_in_mpv: reloaded %s", path)

            # Capture the new mpv sid that was assigned to the re-added track.
            # Without this, _mpv_primary_sids[sid] stays stale and all subsequent
            # sub-remove / reload operations use a dead track id.
            def _capture_new_sid(attempt, _sid=sid, _before=before_ids):
                try:
                    tl = _ipc_command(["get_property", "track-list"])
                    if tl is not None:
                        new_ids = {t.get("id") for t in (tl.get("data") or []) if t.get("type") == "sub"}
                        diff = new_ids - _before
                        if diff:
                            new_mpv_sid = next(iter(diff))
                            self._mpv_primary_sids[_sid] = new_mpv_sid
                            log.info(
                                "_reload_current_sub_in_mpv: captured new sid=%s for %s",
                                new_mpv_sid, _sid,
                            )
                            return
                except Exception:
                    pass
                if attempt < 8:
                    self.after(200, _capture_new_sid, attempt + 1)
                else:
                    log.warning("_reload_current_sub_in_mpv: could not capture new sid after 8 polls")

            self.after(100, _capture_new_sid, 0)

        except Exception as _e:
            log.warning("_reload_current_sub_in_mpv: %s", _e)

    def _dl_archive_only(self, archive_path, sub):
        """Called when the archive downloaded fine but contained no subtitle files.
        Caches and highlights the archive as a downloaded file, then asks the user
        whether they want to open it themselves."""
        self.progress.stop()
        self.btn_load.config(state="normal")
        with self._last_dl_path_lock:
            self._last_dl_path[sub.sub_id] = archive_path
            if sub.dl_url:
                self._last_dl_path["dlurl:" + sub.dl_url] = sub.sub_id
        with _cache_index_lock:
            idx = _load_cache_index(autosave=False)
            idx[sub.sub_id] = archive_path
            if sub.dl_url:
                idx["dlurl:" + sub.dl_url] = sub.sub_id
            _save_cache_index(idx)
        self.status_var.set("\u26a0 No subtitles found in archive: {}".format(Path(archive_path).name))
        self._tree_tags_dirty = True
        self._refresh_tree()
        self._on_select()
        open_it = messagebox.askyesno(
            "No Subtitles Found",
            "No subtitle files were found in the archive:\n\n{}\n\n"
            "Open it to inspect manually?".format(Path(archive_path).name))
        if open_it:
            try:
                if sys.platform == "win32":
                    os.startfile(archive_path)
                elif sys.platform == "darwin":
                    subprocess.Popen(["open", str(archive_path)])
                else:
                    subprocess.Popen(["xdg-open", str(archive_path)])
            except Exception as e:
                log.warning("Could not open archive %s: %s", archive_path, e)
                messagebox.showerror("Error", "Could not open archive:\n{}".format(e))

    # ── embed / local subtitle injection ─────────────────────────────────────

    def _add_sub_to_results(self, path: str, provider: str = "local",
                             release: str = "", language: str = "en",
                             parent_sub_id: "str | None" = None):
        """Register a subtitle file as a result and cache it, then refresh the tree.

        Works identically to a downloaded subtitle — once added the user can
        load it into mpv, translate it, etc.
        parent_sub_id links a translated row to its source sub for positioning.
        """
        path = str(Path(path).resolve())
        sub_id = provider + "_" + hashlib.md5(path.encode("utf-8")).hexdigest()
        # Avoid duplicates
        existing_ids = {s.sub_id for s in self.results + self.secondary_results}
        if sub_id in existing_ids:
            self.status_var.set("\u2713 Already in results: {}".format(Path(path).name))
            return
        sub = Sub(
            provider=provider,
            language=language,
            release=release or Path(path).name,
            score=1.0,
            downloads=0,
            dl_url="",
            sub_id=sub_id,
            fmt=Path(path).suffix.lstrip(".").upper() or "SRT",
            parent_sub_id=parent_sub_id,
        )
        self.results.insert(0, sub)
        # Register in download cache so it loads immediately without a network fetch
        with self._last_dl_path_lock:
            self._last_dl_path[sub_id] = path
        with _cache_index_lock:
            idx = _load_cache_index(autosave=False)
            idx[sub_id] = path
            _save_cache_index(idx)

        # Persist to session cache so the entry survives a restart.
        # _done_searching is only called at the end of a network search, so
        # locally-added subs would otherwise be lost when the window closes.
        self._save_session_snapshot()

        self._tree_tags_dirty = True
        self._refresh_tree()
        # Auto-select the newly added row (iid == sub_id thanks to _insert_sub)
        if self.tree.exists(sub_id):
            self.tree.focus(sub_id)
            self.tree.selection_set(sub_id)
        else:
            children = self.tree.get_children()
            if children:
                self.tree.focus(children[0])
                self.tree.selection_set(children[0])
        self.status_var.set("\u2713 Added: {}".format(Path(path).name))

    def _extract_embedded_subtitles(self, mode="all"):
        """Extract embedded subtitle tracks from the current video.

        mode="all"     — extract every text subtitle track (original behaviour).
        mode="current" — extract only the track currently active in mpv, identified
                         via the IPC properties sid + track-list -> ff-index.
                         Falls back to "all" if IPC is not available.

        Routing:
        - HTTP/HTTPS sources: dump-cache (mpv IPC) then ffmpeg on the local dump.
        - Local files: ffmpeg directly (fast, no IPC needed).
        """
        vp = self.video_path
        if not vp:
            messagebox.showinfo("No Video", "No video is currently loaded.")
            return

        ffprobe_bin = _find_ffmpeg_binary("ffprobe")
        ffmpeg_bin  = _find_ffmpeg_binary("ffmpeg")

        _is_http = bool(_URL_SCHEME_RE.match(vp))

        if not ffprobe_bin or not ffmpeg_bin:
            if _is_http:
                messagebox.showerror(
                    "ffmpeg / ffprobe not found",
                    "Extracting embedded subtitles from a streaming URL requires ffmpeg.\n\n"
                    "SubFinder uses mpv's dump-cache command to save the already-buffered\n"
                    "stream data to a temporary local file, then runs ffmpeg on that file.\n"
                    "No full download is needed -- but ffmpeg must be installed.\n\n"
                    "Download from: https://ffmpeg.org/download.html"
                )
            else:
                messagebox.showerror(
                    "ffmpeg / ffprobe not found",
                    "ffprobe and ffmpeg must be installed and on your PATH to extract\n"
                    "embedded subtitles from local files.\n\n"
                    "Download from: https://ffmpeg.org/download.html"
                )
            return

        # ── Issue #3: resolve active stream index for mode="current" ──────────
        only_stream_idx = None  # None means extract all streams
        if mode == "current":
            sid_resp = _ipc_command(["get_property", "sid"])
            tl_resp  = _ipc_command(["get_property", "track-list"])
            if sid_resp is not None and tl_resp is not None:
                active_sid = sid_resp.get("data")
                track_list = tl_resp.get("data") or []
                for t in track_list:
                    if t.get("type") == "sub" and t.get("id") == active_sid:
                        # ff-index is the raw ffprobe stream index for ffmpeg -map.
                        # Do NOT fall back to demux-id — it is mpv's internal 1-based
                        # track ID which does not match ffprobe's global 0-based index.
                        ff_idx = t.get("ff-index")
                        if ff_idx is not None:
                            only_stream_idx = ff_idx
                        break
            if only_stream_idx is None:
                log.warning("extract_embedded: could not resolve current subtitle stream index "
                            "(sid=%s); falling back to all tracks",
                            sid_resp.get("data") if sid_resp else "N/A")
                mode = "all"  # graceful fallback

        label = "current subtitle" if mode == "current" else "subtitle tracks"
        self.status_var.set("Extracting embedded {}\u2026".format(label))
        self.progress.start(10)

        def _worker():
            if _is_http:
                # Issue #2: dump-cache writes whatever mpv has demuxed so far.
                # For streaming sources, mpv typically buffers only the currently
                # active subtitle track — other tracks may be absent from the dump.
                # Inform the user upfront when "Extract All" is used on HTTP so
                # they know to switch tracks in mpv and re-extract if needed.
                if mode == "all":
                    self.after(0, lambda: self.status_var.set(
                        "\u2139 HTTP stream: extracting buffered subtitle tracks \u2014 "
                        "switch tracks in mpv and re-extract to get others"))
                self._extract_embedded_http_via_dump_cache(
                    vp, ffprobe_bin, ffmpeg_bin, only_stream_idx=only_stream_idx)
            else:
                self._extract_embedded_local(
                    vp, ffprobe_bin, ffmpeg_bin, only_stream_idx=only_stream_idx)

        threading.Thread(target=_worker, daemon=True, name="subfinder-extract-embed").start()

    def _extract_embedded_http_via_dump_cache(self, vp, ffprobe_bin, ffmpeg_bin,
                                              only_stream_idx=None):
        """HTTP embedded extraction via mpv dump-cache IPC command.

        mpv has already buffered the stream's demuxer data (including all subtitle
        packets) as it plays.  We ask mpv to write that buffer to a temp MKV via
        the dump-cache IPC command, then run ffmpeg on that local file.

        only_stream_idx — when set (Issue #3), only that ffprobe stream index is
                          extracted rather than every text track.

        Issue #5 fix: if ffmpeg produces 0-byte output (subtitle packets not yet
        flushed by mpv's demuxer), we re-issue dump-cache and retry up to 2 times
        with a 1.5 s pause between attempts, then give up.
        """
        TEMP_DIR.mkdir(parents=True, exist_ok=True)
        dump_path = str(TEMP_DIR / "mpv_cache_dump.mkv")

        _MAX_DUMP_RETRIES = 2   # Issue #5: retry budget on 0-byte output

        for _attempt in range(1, _MAX_DUMP_RETRIES + 2):  # 1, 2, 3
            # ── Step 1: ask mpv to dump its demuxer cache ─────────────────────
            self.after(0, lambda a=_attempt: self.status_var.set(
                "Requesting mpv cache dump{}\u2026".format(
                    "" if a == 1 else " (retry {})".format(a - 1))))
            log.info("extract_embedded(http): sending dump-cache IPC to mpv -> %s "
                     "(attempt %d)", dump_path, _attempt)
            resp = _ipc_command(["dump-cache", 0, 9999999, dump_path])

            if resp is None:
                self.after(0, lambda: (
                    self.progress.stop(),
                    self.status_var.set("dump-cache failed: mpv IPC not available."),
                    messagebox.showerror(
                        "mpv IPC not available",
                        "Could not connect to mpv via IPC to request a cache dump.\n\n"
                        "Make sure the IPC server is enabled in mpv.conf:\n"
                        "  Windows:      input-ipc-server=\\\\.\\pipe\\mpvpipe\n"
                        "  Linux/macOS:  input-ipc-server=/tmp/mpv-socket\n\n"
                        "SubFinder uses mpv's dump-cache command to extract subtitles\n"
                        "from streaming URLs without downloading the entire file."
                    )
                ))
                return

            error_val = resp.get("error", "")
            if error_val != "success":
                msg = "mpv dump-cache returned error: {}".format(error_val)
                log.error("extract_embedded(http): %s", msg)
                self.after(0, lambda m=msg: (
                    self.progress.stop(),
                    self.status_var.set(m),
                    messagebox.showerror("dump-cache error", m)
                ))
                return

            log.info("extract_embedded(http): dump-cache succeeded -> %s", dump_path)

            # ── Step 2: verify the dump file exists and has content ────────────
            if not Path(dump_path).is_file() or Path(dump_path).stat().st_size == 0:
                msg = "dump-cache produced no output at {}".format(dump_path)
                log.error("extract_embedded(http): %s", msg)
                self.after(0, lambda m=msg: (
                    self.progress.stop(),
                    self.status_var.set("Cache dump empty -- playback may not have started yet."),
                    messagebox.showerror(
                        "Cache dump empty",
                        "mpv\'s dump-cache produced an empty file.\n\n"
                        "Make sure playback has started and at least a few seconds\n"
                        "of the video have buffered before extracting subtitles."
                    )
                ))
                return

            # ── Step 3: run ffprobe + ffmpeg on the local dump ────────────────
            self.after(0, lambda: self.status_var.set(
                "Analyzing subtitle tracks\u2026"))
            _http_stem = (re.sub(r'[/\\:*?"<>|]', "_",
                                  self.q_var.get().strip())
                          .strip("._") or "stream")
            _got_output = self._extract_embedded_local(
                dump_path, ffprobe_bin, ffmpeg_bin,
                stem_override=_http_stem, only_stream_idx=only_stream_idx,
                _return_zero_byte_flag=True)

            if _got_output is not False:
                # Extraction succeeded (or failed for a non-retryable reason)
                break

            # Issue #5: 0-byte output — subtitle packets not yet flushed.
            if _attempt <= _MAX_DUMP_RETRIES:
                log.warning("extract_embedded(http): 0-byte subtitle output on attempt %d; "
                            "waiting 1.5s before retry", _attempt)
                self.after(0, lambda a=_attempt: self.status_var.set(
                    "Subtitle track empty — retrying (attempt {}/{})\u2026".format(
                        a, _MAX_DUMP_RETRIES + 1)))
                _time_module.sleep(1.5)
            else:
                log.error("extract_embedded(http): all %d dump-cache attempts produced "
                          "0-byte subtitle output; giving up", _MAX_DUMP_RETRIES + 1)

            # Clean up the stale dump before retrying
            try:
                Path(dump_path).unlink(missing_ok=True)
            except Exception:
                pass

        # Clean up the dump file after the final extraction attempt
        try:
            Path(dump_path).unlink(missing_ok=True)
        except Exception:
            pass

    def _extract_embedded_local(self, vp, ffprobe_bin, ffmpeg_bin, stem_override=None,
                              only_stream_idx=None, _return_zero_byte_flag=False):
        """Run ffprobe + ffmpeg to extract subtitle tracks from a local file path.

        Also used for the dump-cache HTTP path: after dump-cache writes the
        buffered stream to a temp MKV we treat it as a local file here.

        only_stream_idx     — when set (Issue #3), only extract that ffprobe index.
        _return_zero_byte_flag — when True (Issue #5 retry path), returns False
                                 instead of None when all extracted tracks were
                                 0-byte (so the caller can retry the dump-cache).
        """
        # Step 1: probe all subtitle streams
        probe_cmd = [
            ffprobe_bin, "-v", "error",
            "-of", "json",
            "-show_entries", "stream=index,codec_name,codec_type:stream_tags=language,title",
            "-select_streams", "s", vp
        ]
        log.info("extract_embedded: ffprobe cmd: %s", " ".join(probe_cmd))
        try:
            probe = subprocess.run(probe_cmd, capture_output=True, text=True, timeout=30)
            if probe.returncode != 0:
                log.error("extract_embedded: ffprobe exited %d\nstderr:\n%s",
                          probe.returncode, probe.stderr)
            streams = json.loads(probe.stdout or "{}").get("streams", [])
        except Exception as exc:
            log.error("extract_embedded: ffprobe exception: %s\n%s", exc, traceback.format_exc())
            self.after(0, lambda: (
                self.progress.stop(),
                self.status_var.set("ffprobe error: {}".format(exc))
            ))
            return

        # Step 2: classify streams
        TEXT_TO_SRT  = {"subrip", "srt", "mov_text"}
        TEXT_TO_COPY = {"ass", "ssa", "webvtt"}
        ALL_TEXT     = TEXT_TO_SRT | TEXT_TO_COPY
        IMAGE_CODECS = {"hdmv_pgs_subtitle", "dvd_subtitle", "xsub",
                        "dvb_subtitle", "dvb_teletext"}

        text_streams  = [s for s in streams if s.get("codec_name", "").lower() in ALL_TEXT]
        image_streams = [s for s in streams if s.get("codec_name", "").lower() in IMAGE_CODECS]

        # Issue #3: filter to only the requested stream when mode="current"
        if only_stream_idx is not None:
            filtered = [s for s in text_streams if s.get("index") == only_stream_idx]
            if filtered:
                text_streams = filtered
            else:
                log.warning("extract_embedded: requested stream index %d not found in "
                            "text streams; extracting all instead", only_stream_idx)

        if not text_streams:
            msg = "No extractable subtitle tracks found in this file."
            if image_streams:
                codecs = ", ".join(s.get("codec_name", "?") for s in image_streams)
                msg = (
                    "No text-based subtitle tracks found.\n\n"
                    "This file contains image-based subtitles ({}) which "
                    "cannot be converted to SRT by ffmpeg.".format(codecs)
                )
                log.info("extract_embedded: only image-based streams: %s", codecs)
            self.after(0, lambda m=msg: (
                self.progress.stop(),
                self.status_var.set("No extractable subtitle tracks found.")
            ))
            if image_streams:
                self.after(0, lambda m=msg: messagebox.showinfo("Image-based subtitles only", m))
            return

        log.info("extract_embedded: found %d text stream(s), %d image stream(s)",
                 len(text_streams), len(image_streams))

        # Step 3: extract each stream individually
        stem = stem_override or (Path(vp).stem if not _URL_SCHEME_RE.match(vp) else "stream")
        TEMP_DIR.mkdir(parents=True, exist_ok=True)
        added  = 0
        failed = 0
        seen_labels: dict = {}  # label → count, for duplicate deduplication (#2)

        for s in text_streams:
            codec = s.get("codec_name", "").lower()
            _raw_lang = (s.get("tags", {}).get("language") or "").strip().lower()
            # Resolve ffprobe language tag to a known, certain language name.
            # Rules:
            #   - "und", empty, or anything we don't recognise → "" (no indicator).
            #     We must never show a language indicator we are not 100% sure of.
            #   - 3-letter ISO 639-2 code (e.g. "eng", "ara") → look up in ISO3_TO_LANG.
            #   - 2-letter ISO 639-1 code (e.g. "en", "ar")   → look up in CODE_TO_LANG.
            #   - Full name already in our LANGUAGES dict          → use as-is.
            if not _raw_lang or _raw_lang == "und":
                lang = ""   # unknown — never show a wrong indicator
            elif _raw_lang in ISO3_TO_LANG:
                lang = ISO3_TO_LANG[_raw_lang]          # e.g. "eng" → "English"
            elif _raw_lang in CODE_TO_LANG:
                lang = CODE_TO_LANG[_raw_lang]          # e.g. "en" → "English"
            elif _raw_lang.capitalize() in LANGUAGES:
                lang = _raw_lang.capitalize()           # already a full name
            else:
                lang = ""   # unrecognised tag — show nothing rather than wrong label
            title = (s.get("tags", {}).get("title") or "").strip()
            idx   = s["index"]

            if codec in TEXT_TO_COPY:
                out_ext   = "." + codec.replace("webvtt", "vtt")
                codec_arg = "copy"
            else:
                out_ext   = ".srt"
                codec_arg = "srt"

            safe_stem = re.sub(r"[^\w\-.]", "_", stem)
            out_path  = str(TEMP_DIR / "{}.embedded_{}_{}_{}{}" .format(
                safe_stem, lang, idx, codec, out_ext))

            ffmpeg_cmd = [
                ffmpeg_bin, "-y",
                "-i", vp,
                "-map", "0:{}".format(idx),
                "-c:s", codec_arg, out_path
            ]
            log.info("extract_embedded: stream %d (%s/%s) cmd: %s",
                     idx, codec, lang, " ".join(ffmpeg_cmd))

            try:
                proc = subprocess.run(ffmpeg_cmd, capture_output=True, timeout=120)
                if proc.returncode != 0:
                    stderr_text = proc.stderr.decode(errors="replace")
                    log.error(
                        "extract_embedded: ffmpeg failed for stream %d "
                        "(codec=%s lang=%s) exit=%d\nstderr:\n%s",
                        idx, codec, lang, proc.returncode, stderr_text
                    )
                    failed += 1
                    continue
            except subprocess.TimeoutExpired:
                log.error("extract_embedded: ffmpeg timed out for stream %d", idx)
                failed += 1
                continue
            except Exception as exc:
                log.error("extract_embedded: ffmpeg exception for stream %d: %s\n%s",
                          idx, exc, traceback.format_exc())
                failed += 1
                continue

            if not Path(out_path).is_file() or Path(out_path).stat().st_size == 0:
                log.warning("extract_embedded: stream %d produced no output at %s", idx, out_path)
                failed += 1
                # When _return_zero_byte_flag=True (the HTTP dump-cache retry path),
                # return False immediately so the caller retries the entire dump-cache.
                # This abandons any remaining streams unprocessed — acceptable because
                # the caller (_extract_embedded_http_via_dump_cache) will retry all
                # streams from scratch and manages its own progress/stop state.
                if _return_zero_byte_flag:
                    return False
                continue

            # Release label = actual extracted filename (what the user sees on disk).
            # This makes the Release/Title column match the real file being used.
            release = Path(out_path).name

            self.after(0, lambda p=out_path, l=lang, r=release:
                self._add_sub_to_results(p, provider="embedded", release=r, language=l))
            added += 1

        # Step 4: report outcome
        def _finish(n=added, f=failed):
            self.progress.stop()
            if n and f:
                self.status_var.set(
                    "\u2713 Extracted {} track{}; {} failed \u2014 see log for details.".format(
                        n, "s" if n != 1 else "", f))
            elif n:
                self.status_var.set(
                    "\u2713 Extracted {} embedded subtitle track{}.".format(
                        n, "s" if n != 1 else ""))
            else:
                self.status_var.set(
                    "Extraction failed for all {} track{} \u2014 see log for details.".format(
                        len(text_streams), "s" if len(text_streams) != 1 else ""))
        self.after(0, _finish)

    def _add_subtitle_file(self):
        """Open a file picker so the user can add a local subtitle file directly."""
        from tkinter import filedialog
        path = filedialog.askopenfilename(
            parent=self,
            title="Add Subtitle File",
            filetypes=[
                ("Subtitle files", "*.srt *.ass *.ssa *.vtt *.sub *.idx"),
                ("All files", "*.*"),
            ]
        )
        if not path:
            return
        # Language is unknown for user-picked local files — never guess.
        # Empty language means no [XX] indicator in release column, and the
        # language column will show '?' which is honest.
        self._add_sub_to_results(path, provider="local",
                                  release=Path(path).name, language="")

    # ── right-click context menu ──────────────────────────────────────────────

    def _on_tree_right_click(self, event):
        """Select the row under the cursor then show the appropriate context menu."""
        row = self.tree.identify_row(event.y)
        if not row:
            return
        # Don't show menu on the toggle/separator row
        if "toggle_row" in self.tree.item(row, "tags"):
            return
        self.tree.selection_set(row)
        self.tree.focus(row)
        sub = self._selected()
        if not sub:
            return

        cached_path   = self._last_dl_path.get(sub.sub_id, "")
        is_downloaded = bool(cached_path and Path(cached_path).is_file())
        is_primary    = bool(sub.sub_id and sub.sub_id == self._mpv_primary_sub_id)
        is_secondary  = bool(sub.sub_id and sub.sub_id == self._mpv_secondary_sub_id)
        is_mpv_loaded = is_primary or is_secondary
        # Local and embedded subtitles point directly to the user's own files.
        # "Delete from Cache" would remove those files from disk, which is never
        # what the user wants — so we suppress it for these providers entirely.
        is_user_file  = sub.provider in ("local", "embedded")

        menu = tk.Menu(self, tearoff=0,
                       bg=C["card"], fg=C["text"],
                       activebackground=C["sel_bg"], activeforeground=C["sel_fg"],
                       relief="flat", bd=1)

        def _copy(text):
            self.clipboard_clear()
            self.clipboard_append(text)
            self.status_var.set("Copied to clipboard")

        release_name = sub.release or ""
        dl_url       = sub.dl_url  or ""

        # ── Row-specific primary actions ──────────────────────────────────────
        # A subtitle can be loaded as both primary AND secondary simultaneously.
        # Show Remove options for whichever slots are active, and always offer
        # the slot(s) where it is NOT yet loaded.
        if is_primary:
            menu.add_command(
                label="Remove Primary from mpv",
                foreground=C["danger"],
                activeforeground=C["danger"],
                command=lambda: self._remove_from_mpv(sub))
        else:
            menu.add_command(
                label="Load as Primary Subtitle",
                command=lambda: self._do_load(close_after=False))

        if is_secondary:
            menu.add_command(
                label="Remove Secondary from mpv",
                foreground=C["danger"],
                activeforeground=C["danger"],
                command=lambda: self._remove_from_mpv_secondary(sub))
        else:
            menu.add_command(
                label="Load as Secondary Subtitle",
                command=self._do_load_secondary)

        menu.add_separator()

        # ── File / clipboard actions ──────────────────────────────────────────
        if is_downloaded:
            menu.add_command(
                label="Show in Explorer",
                command=self._open_dl_folder)
            menu.add_command(
                label="Copy File Path",
                command=lambda: _copy(cached_path))
            menu.add_separator()

        menu.add_command(
            label="Copy Release Name",
            state="normal" if release_name else "disabled",
            command=lambda: _copy(release_name))
        menu.add_command(
            label="Copy URL",
            state="normal" if dl_url else "disabled",
            command=lambda: _copy(dl_url))

        # ── Translate submenu (only for downloaded subtitles) ─────────────────
        # Clicking a language directly translates and loads as primary — no submenus.
        _gemini_keys_ctx = [k.strip() for k in self._settings.get("gemini_api_keys", []) if k.strip()]
        if not _gemini_keys_ctx:
            _legacy = self._settings.get("gemini_api_key", "").strip()
            if _legacy:
                _gemini_keys_ctx = [_legacy]
        # Gemini translation is gated solely on whether a key is configured.
        gemini_key = _gemini_keys_ctx[0] if _gemini_keys_ctx else ""
        _cached_ext = Path(cached_path).suffix.lower() if cached_path else ""
        _ext_ok = is_downloaded and (_cached_ext in _SUB_EXTENSIONS)
        translate_menu = tk.Menu(
            menu, tearoff=0,
            bg=C["card"], fg=C["text"],
            activebackground=C["sel_bg"], activeforeground=C["sel_fg"],
            relief="flat", bd=1,
        )
        if not gemini_key:
            translate_menu.add_command(
                label="Set up a Gemini key first",
                state="disabled",
                foreground=C.get("dim", "#888"),
            )
        elif is_downloaded and not _ext_ok:
            translate_menu.add_command(
                label="File format not supported",
                state="disabled",
                foreground=C.get("dim", "#888"),
            )
        else:
            # Each language is a direct command.
            # If the sub is already downloaded → translate immediately and load as primary.
            # If not yet downloaded → download first, then translate (load_slot=primary).
            for _lang_name in sorted(LANGUAGES.keys()):
                _lang_code = LANGUAGES[_lang_name]
                if is_downloaded:
                    translate_menu.add_command(
                        label=_lang_name,
                        command=lambda lc=_lang_code, ln=_lang_name, _pid=sub.sub_id:
                            self._translate_subtitle(cached_path, lc, ln, gemini_key,
                                                     parent_sub_id=_pid,
                                                     load_slot="primary"),
                    )
                else:
                    translate_menu.add_command(
                        label=_lang_name,
                        command=lambda lc=_lang_code, ln=_lang_name:
                            self._do_load_then_translate(sub, lc, ln, gemini_key),
                    )
        menu.add_separator()
        menu.add_cascade(
            label="Translate to",
            menu=translate_menu,
            foreground=C["text"],
            activeforeground=C["sel_fg"],
        )

        # ── HI/SDH strip ──────────────────────────────────────────────────────
        # Downloaded + HI detected → strip immediately.
        # Not yet downloaded + filename/release name signals HI → offer download-then-strip.
        # We cannot detect HI content before downloading; the name check is the gate.
        _release_name = sub.release or ""
        _cached_fname = Path(cached_path).name if cached_path else ""
        _name_says_hi = bool(
            _HI_NAME_RE.search(_release_name) or _HI_NAME_RE.search(_cached_fname)
        )
        if is_downloaded:
            if _detect_hi_content(cached_path) or _name_says_hi:
                def _strip_hi(_src=cached_path):
                    def _do_strip():
                        ok = _strip_hi_from_file(_src)
                        if ok:
                            self.after(0, lambda: self.status_var.set(
                                "\u2713 HI annotations stripped: {}".format(
                                    Path(_src).name)))
                            self.after(0, self._reload_current_sub_in_mpv)
                        else:
                            self.after(0, lambda: messagebox.showerror(
                                "Strip failed",
                                "Could not strip HI from:\n{}".format(_src),
                                parent=self))
                    threading.Thread(target=_do_strip, daemon=True, name="subfinder-hi-strip").start()
                menu.add_command(label="Strip HI / SDH annotations", command=_strip_hi)
        else:
            # Not yet downloaded — only offer strip when filename/release name
            # explicitly signals HI/SDH content; otherwise we have no way to know.
            if _name_says_hi:
                def _strip_hi_after_dl(_sub=sub):
                    def _after_dl(path: str) -> bool:
                        # Run strip in a background thread — _strip_hi_from_file
                        # is file I/O and must not block the main thread.
                        # Snapshot the track-list now (main thread) so the sid
                        # capture diff is accurate regardless of thread timing.
                        _tl_snap = _ipc_command(["get_property", "track-list"])
                        _before = set()
                        if _tl_snap is not None:
                            for _t in (_tl_snap.get("data") or []):
                                if _t.get("type") == "sub":
                                    _before.add(_t["id"])

                        def _do_strip_and_load():
                            ok = _strip_hi_from_file(path)
                            if not ok:
                                self.after(0, lambda: messagebox.showerror(
                                    "Strip failed",
                                    "Could not strip HI from:\n{}".format(path),
                                    parent=self))
                                return
                            # Load into mpv from the background thread —
                            # IPC is socket/pipe I/O, safe to call off-thread.
                            load_subtitle_into_mpv(path)
                            self.after(0, lambda: self.status_var.set(
                                "\u2713 HI stripped & loaded: {}".format(
                                    Path(path).name)))
                            # Capture the new mpv sid so "Remove from mpv" and
                            # session persistence work correctly after this load.
                            # Poll up to 8 times (200 ms apart) matching _try_capture_sid.
                            import time as _t_mod
                            _new_sid = None
                            for _attempt in range(8):
                                if _attempt > 0:
                                    _t_mod.sleep(0.2)
                                _tl_after = _ipc_command(["get_property", "track-list"])
                                if _tl_after is not None:
                                    for _tr in (_tl_after.get("data") or []):
                                        if _tr.get("type") == "sub" and _tr["id"] not in _before:
                                            _new_sid = _tr["id"]
                                            break
                                if _new_sid is not None:
                                    break
                            if _new_sid is not None:
                                def _apply_sid(_sid=_new_sid, _path=path,
                                               _sub_id=_sub.sub_id):
                                    self._mpv_primary_sub_id = _sub_id
                                    self._mpv_primary_sids[_sub_id] = _sid
                                    # Store the loaded path for the filename
                                    # fallback in _remove_from_mpv.
                                    with self._last_dl_path_lock:
                                        self._last_dl_path["loaded:" + _sub_id] = _path
                                    self._tree_tags_dirty = True
                                    self._refresh_tree()
                                    self._save_session_snapshot()
                                    log.info("HI strip+load: sid captured sub_id=%s sid=%s",
                                             _sub_id, _sid)
                                self.after(0, _apply_sid)
                            else:
                                log.warning("HI strip+load: could not capture mpv sid for %r",
                                            path)

                        threading.Thread(target=_do_strip_and_load, daemon=True,
                                         name="subfinder-hi-strip").start()
                        # Return True immediately — load is happening in the thread;
                        # _dl_ok must not show the "drag into mpv" fallback popup.
                        return True
                    self._do_load(close_after=False, load_fn=_after_dl)
                menu.add_command(label="Strip HI / SDH annotations", command=_strip_hi_after_dl)

        # ── Sync with video (ffsubsync / alass) ───────────────────────────────
        # Downloaded → sync immediately.
        # Not yet downloaded → download first, then sync.
        # Live streams and missing tools → omit entirely (no disabled ghost entries).
        _video_is_local        = bool(self.video_path and Path(self.video_path).is_file())
        _video_is_url          = bool(self.video_path and _URL_SCHEME_RE.match(self.video_path))
        _video_is_live         = bool(_video_is_url and _is_live_stream_url(self.video_path))
        _video_is_seekable_url = _video_is_url and not _video_is_live

        if not _video_is_live and (_video_is_local or _video_is_seekable_url):
            _sync_path, _sync_name = _find_sync_tool()
            _ffmpeg_bin = _find_ffmpeg_binary("ffmpeg")
            # Only show when the tool exists and (for URLs) ffmpeg is available.
            if _sync_path and (not _video_is_seekable_url or _ffmpeg_bin):

                def _run_sync(_src, _video, _is_url, _name=_sync_name, _tool=_sync_path):
                    """Core sync worker — runs in a daemon thread.

                    Always extracts audio via ffmpeg (both local files and URLs) so
                    the sync tool always gets a clean 16 kHz mono WAV reference.
                    Stop button kills all procs in self._sync_procs — there is intentionally no
                    communicate() timeout; every video is different.
                    """
                    _tmp_audio = None
                    try:
                        _ffmpeg = _find_ffmpeg_binary("ffmpeg")
                        if not _ffmpeg:
                            self.after(0, lambda: messagebox.showerror(
                                "ffmpeg not found",
                                "Auto sync requires ffmpeg on PATH.\n\n"
                                "Download from https://ffmpeg.org/download.html",
                                parent=self))
                            return

                        _tmp_audio = str(
                            TEMP_DIR / "syncref_{}.wav".format(
                                hashlib.md5(_video.encode()).hexdigest()[:8]))

                        # ── WAV cache: reuse if the file is less than 2 hours old ──
                        # For remote URLs (e.g. TorBox signed links) extracting 10
                        # minutes of audio can take several minutes because ffmpeg
                        # must range-request the MKV container index.  Caching the
                        # WAV avoids re-extraction on every subsequent sync of the
                        # same video.  The 2-hour TTL covers a typical viewing session
                        # while still letting the cache expire naturally.
                        _WAV_TTL_SECONDS = 7200  # 2 hours
                        _wav_path = Path(_tmp_audio)
                        _wav_fresh = (
                            _wav_path.is_file()
                            and _wav_path.stat().st_size >= 1000
                            and (_time_module.time() - _wav_path.stat().st_mtime) < _WAV_TTL_SECONDS
                        )
                        if _wav_fresh:
                            log.info("Sync: reusing cached WAV %s", _tmp_audio)
                        else:
                            self.after(0, lambda: self.status_var.set(
                                "Sync: extracting audio…"))

                            _si = None; _cf = 0
                            if sys.platform == "win32":
                                _si = subprocess.STARTUPINFO()
                                _si.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                                _si.wShowWindow = 0
                                _cf = 0x08000000  # CREATE_NO_WINDOW

                            # For HTTP/HTTPS URLs add reconnect flags so ffmpeg
                            # handles range-request back-and-forth (needed to read
                            # the MKV index) without stalling.  Also use -map 0:a:0
                            # to select the first audio stream directly, skipping the
                            # full-stream analysis pass that otherwise probes all tracks.
                            if _is_url:
                                _ep_cmd = [
                                    _ffmpeg,
                                    "-reconnect", "1",
                                    "-reconnect_streamed", "1",
                                    "-reconnect_delay_max", "5",
                                    "-y", "-i", _video,
                                    "-map", "0:a:0",
                                    "-vn", "-ac", "1", "-ar", "16000",
                                    "-t", "600",   # up to 10 min — stop button cancels
                                    "-loglevel", "error", _tmp_audio,
                                ]
                            else:
                                _ep_cmd = [
                                    _ffmpeg,
                                    "-y", "-i", _video,
                                    "-vn", "-ac", "1", "-ar", "16000",
                                    "-t", "600",   # up to 10 min — stop button cancels
                                    "-loglevel", "error", _tmp_audio,
                                ]
                            log.info("Sync: audio extraction cmd: %s",
                                     " ".join(str(c) for c in _ep_cmd))

                            _ep = subprocess.Popen(
                                _ep_cmd,
                                stdin=subprocess.DEVNULL,
                                stdout=subprocess.DEVNULL,
                                stderr=subprocess.PIPE,
                                startupinfo=_si, creationflags=_cf,
                            )
                            self._sync_procs.add(_ep)
                            _ep_err, _ = _ep.communicate()  # no timeout — stop button kills it
                            self._sync_procs.discard(_ep)

                            if _ep.returncode != 0:
                                if self._stop_event.is_set():
                                    return  # killed by stop button
                                err = (_ep_err or b"").decode(errors="replace").strip()
                                log.error(
                                    "Sync: audio extraction failed rc=%d\n"
                                    "  cmd : %s\n"
                                    "  stderr: %s",
                                    _ep.returncode,
                                    " ".join(str(c) for c in _ep_cmd),
                                    err[:800])
                                self.after(0, lambda e=err: messagebox.showerror(
                                    "Audio extraction failed",
                                    "ffmpeg exited with an error.\n\n"
                                    "stderr:\n{}".format(e[:600]),
                                    parent=self))
                                self.after(0, lambda: self.status_var.set(
                                    "Sync failed — audio extraction error"))
                                return

                            if not Path(_tmp_audio).is_file() or \
                                    Path(_tmp_audio).stat().st_size < 1000:
                                log.error(
                                    "Sync: audio extraction produced no usable output.\n"
                                    "  cmd: %s\n"
                                    "  file size: %s",
                                    " ".join(str(c) for c in _ep_cmd),
                                    Path(_tmp_audio).stat().st_size
                                    if Path(_tmp_audio).is_file() else "missing")
                                self.after(0, lambda: messagebox.showerror(
                                    "Audio extraction failed",
                                    "ffmpeg produced no usable audio output.\n\n"
                                    "Check the log for details.",
                                    parent=self))
                                return
                        # _wav_fresh path joins here — WAV is ready either way

                        reference = _tmp_audio
                        self.after(0, lambda: self.status_var.set(
                            "Sync: running {}…".format(_name)))

                        # ── Run the sync tool ─────────────────────────────────────────────────────
                        if _name == "ffsubsync":
                            cmd = [_tool, reference,
                                   "-i", _src, "-o", _src,
                                   "--reference-stream", "a:0"]
                        else:
                            cmd = [_tool, reference, _src, _src]

                        log.info("Sync: running cmd: %s", " ".join(str(c) for c in cmd))

                        _si2 = None; _cf2 = 0
                        if sys.platform == "win32":
                            _si2 = subprocess.STARTUPINFO()
                            _si2.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                            _si2.wShowWindow = 0
                            _cf2 = 0x08000000

                        _sp = subprocess.Popen(
                            cmd,
                            stdin=subprocess.DEVNULL,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE,
                            startupinfo=_si2, creationflags=_cf2,
                        )
                        self._sync_procs.add(_sp)
                        _out, _err = _sp.communicate()  # no timeout — stop button kills it
                        self._sync_procs.discard(_sp)
                        _rc = _sp.returncode

                        # Log all output — filter progress spam but keep everything useful.
                        for _line in (_out + _err).decode(errors="replace").splitlines():
                            _ls = _line.strip()
                            if _ls and any(k in _ls for k in (
                                    "offset", "score", "framerate", "writing output",
                                    "ERROR", "error", "failed", "Skipped",
                                    "Warning", "warning")):
                                log.info("Sync %s: %s", _name, _ls)

                        if _rc == 0:
                            self.after(0, self._reload_current_sub_in_mpv)
                            self.after(0, lambda: self.status_var.set(
                                "\u2713 Synced: {}".format(Path(_src).name)))
                            if _winsound:
                                try:
                                    _winsound.MessageBeep(_winsound.MB_ICONASTERISK)
                                except Exception:
                                    pass
                        elif not self._stop_event.is_set():
                            # Only surface an error if stop was NOT clicked —
                            # kill() causes a non-zero returncode that is not an error.
                            err = ((_err or b"") + (_out or b"")).decode(
                                errors="replace").strip() or "unknown error"
                            log.error(
                                "Sync: %s exited %d\n"
                                "  cmd: %s\n"
                                "  output: %s",
                                _name, _rc,
                                " ".join(str(c) for c in cmd),
                                err[:800])
                            self.after(0, lambda e=err: messagebox.showerror(
                                "Sync failed",
                                "{} exited with code {}.\n\n"
                                "Output:\n{}".format(_name, _rc, e[:600]),
                                parent=self))
                            self.after(0, lambda: self.status_var.set("Sync failed"))

                    except Exception as _se:
                        log.error("Sync: unexpected error: %s\n%s",
                                  _se, traceback.format_exc())
                        self.after(0, lambda e=_se: messagebox.showerror(
                            "Sync error", str(e), parent=self))
                    finally:
                        # Do NOT delete _tmp_audio — it is kept as a cache so the
                        # next sync of the same video skips the expensive extraction
                        # step.  _cleanup_temp_dir() expires it after 2 hours via
                        # the normal temp-file TTL sweep.
                        self.after(0, lambda: self.btn_stop.config(state="disabled"))
                        self.after(0, lambda: self.progress.stop())

                if is_downloaded:
                    def _do_sync(_src=cached_path, _video=self.video_path,
                                 _is_url=_video_is_seekable_url):
                        _tool, _name = _find_sync_tool()
                        if not _tool:
                            messagebox.showerror(
                                "Sync tool not found",
                                "Neither ffsubsync nor alass is on PATH.\n\n"
                                "Install ffsubsync:  pip install ffsubsync\n"
                                "Or download alass:  github.com/kaegi/alass/releases",
                                parent=self)
                            return
                        self.status_var.set("Syncing subtitle\u2026")
                        self.progress.start(10)
                        self.btn_stop.config(state="normal")
                        threading.Thread(
                            target=_run_sync,
                            args=(_src, _video, _is_url),
                            daemon=True,
                            name="subfinder-sync",
                        ).start()
                else:
                    def _do_sync(_sub=sub, _video=self.video_path,
                                 _is_url=_video_is_seekable_url):
                        def _after_dl(path: str) -> bool:
                            # Do NOT load into mpv here — the sequence is:
                            #   download -> sync (rewrites file in place) -> load.
                            # Set _mpv_primary_sub_id and _last_dl_path now so
                            # _reload_current_sub_in_mpv (called on sync success)
                            # knows which file to add.  Its sub-remove is a no-op
                            # because no track has been loaded yet; sub-add is the
                            # one and only load.
                            self._mpv_primary_sub_id = _sub.sub_id
                            with self._last_dl_path_lock:
                                self._last_dl_path[_sub.sub_id] = path
                            self.after(0, lambda: self.status_var.set(
                                "Syncing subtitle…"))
                            self.after(0, lambda: self.progress.start(10))
                            self.after(0, lambda: self.btn_stop.config(state="normal"))
                            threading.Thread(
                                target=_run_sync,
                                args=(path, _video, _is_url),
                                daemon=True,
                                name="subfinder-sync",
                            ).start()
                            return True  # suppress _dl_ok's "load manually" dialog
                        self._do_load(close_after=False, load_fn=_after_dl)

                menu.add_command(
                    label="Auto sync ({})".format(_sync_name),
                    command=_do_sync)

        # ── Destructive action — last ──────────────────────────────────────────
        # Remote downloaded subs: Delete from Cache (removes file from disk).
        # Embedded subs: Delete from Cache (removes the extracted temp file).
        # Translated subs: Delete from Cache + remove from mpv if loaded.
        # Local subs: Remove from List only (never touch the user's file on disk).
        if sub.provider == "translated" and is_downloaded:
            menu.add_separator()
            menu.add_command(
                label="Delete from Cache",
                foreground=C["danger"],
                activeforeground=C["danger"],
                command=lambda: self._ctx_delete_cache(sub, remove_from_results=True,
                                                       remove_from_mpv=True))
        elif is_downloaded and not is_user_file:
            menu.add_separator()
            menu.add_command(
                label="Delete from Cache",
                foreground=C["danger"],
                activeforeground=C["danger"],
                command=lambda: self._ctx_delete_cache(sub))
        elif sub.provider == "embedded" and is_downloaded:
            menu.add_separator()
            menu.add_command(
                label="Delete from Cache",
                foreground=C["danger"],
                activeforeground=C["danger"],
                command=lambda: self._ctx_delete_cache(sub, remove_from_results=True))
        elif sub.provider == "local":
            menu.add_separator()
            menu.add_command(
                label="Remove from List",
                foreground=C["danger"],
                activeforeground=C["danger"],
                command=lambda: self._ctx_remove_from_list(sub))

        menu.tk_popup(event.x_root, event.y_root)

    def _on_tree_empty_right_click(self, event):
        """Show a minimal context menu when right-clicking on the empty results area."""
        # Only fire when no row is under the cursor
        row = self.tree.identify_row(event.y)
        if row:
            return
        self._show_file_action_menu(event.x_root, event.y_root)

    def _on_window_right_click(self, event):
        """Show the file-action menu when right-clicking anywhere in the main window
        that is not the treeview itself.  Ignores events from popup/Toplevel windows."""
        # Ignore the treeview — it has its own dedicated right-click handlers.
        if event.widget is self.tree:
            return
        # Ignore events from any Toplevel other than this root window (settings,
        # help, log viewer, etc.) so their own widgets are not polluted by this menu.
        try:
            toplevel = event.widget.winfo_toplevel()
            if toplevel is not self:
                return
        except Exception:
            return
        self._show_file_action_menu(event.x_root, event.y_root)

    def _show_file_action_menu(self, x_root, y_root):
        """Build and display the file-action context menu.

        Issue #3: two separate items for current-subtitle vs all-subtitles extraction.
        Extract items are shown only when a local file (not a URL) is playing.
        """
        menu = tk.Menu(self, tearoff=0,
                       bg=C["card"], fg=C["text"],
                       activebackground=C["sel_bg"], activeforeground=C["sel_fg"],
                       relief="flat", bd=1)
        menu.add_command(
            label="Add Subtitle File\u2026",
            command=self._add_subtitle_file,
        )
        # Extraction only makes sense for local files — not for streaming URLs.
        _vp = self.video_path or ""
        _is_local_video = bool(_vp) and not _URL_SCHEME_RE.match(_vp)
        if _is_local_video:
            menu.add_separator()
            menu.add_command(
                label="Extract Current Subtitle",
                command=lambda: self._extract_embedded_subtitles(mode="current"),
            )
            menu.add_command(
                label="Extract All Subtitles",
                command=lambda: self._extract_embedded_subtitles(mode="all"),
            )
        menu.tk_popup(x_root, y_root)

    # ── subtitle translation ──────────────────────────────────────────────────

    def _translate_subtitle(self, srt_path: str, lang_code: str,
                            lang_name: str, api_key: str,
                            parent_sub_id: "str | None" = None,
                            load_slot: str = ""):
        """Kick off a background translation of *srt_path* → *lang_code*.

        load_slot — if "primary" or "secondary", also load the result into that
                    mpv slot immediately after adding the row.  Empty = row only.
        """
        if not Path(srt_path).is_file():
            messagebox.showerror("File Not Found",
                                 "Source subtitle file not found:\n{}".format(srt_path))
            return

        # ── Non-SRT format handling ───────────────────────────────────────────
        # If the file is ASS/SSA/VTT and pysubs2 is available, convert it to a
        # temporary SRT so translation can proceed.  The temp file is cleaned up
        # automatically by _translate_worker when it finishes.
        _orig_ext = Path(srt_path).suffix.lower()
        _converted_tmp = None
        if _orig_ext not in (".srt",):
            if _PYSUBS2_OK:
                try:
                    _fd, _tmp_srt_str = tempfile.mkstemp(suffix=".srt", dir=str(TEMP_DIR))
                    os.close(_fd)  # close the fd — pysubs2 will open the path itself
                    _tmp_srt = Path(_tmp_srt_str)
                    _pysubs2.load(srt_path).save(str(_tmp_srt), format_="srt")
                    srt_path = str(_tmp_srt)
                    _converted_tmp = _tmp_srt
                    log.info("translation: converted %s to temp SRT", _orig_ext)
                except Exception as _conv_e:
                    messagebox.showerror(
                        "Conversion Failed",
                        "Could not convert {} to SRT for translation:\n{}".format(
                            _orig_ext.upper(), _conv_e))
                    return
            else:
                messagebox.showerror(
                    "Unsupported Format",
                    "Translation of {} files requires pysubs2.\n"
                    "Install it with:  pip install pysubs2".format(_orig_ext.upper()))
                return

        # ── Cache check — use shared helper so this path stays in sync with
        #    the write path in translate_srt_with_gemini (Quality fix #45).
        cached_translation = _translation_output_path(srt_path, lang_code)

        if cached_translation.is_file():
            fname = cached_translation.name
            log.info("translation cache hit: %s", cached_translation)
            self.status_var.set("\u2713 From cache: {}".format(fname))
            # release = clean filename stem; language = full lang name.
            # The [XX] indicator is added by _insert_sub when the lang col is hidden.
            # Wrap in try/finally to ensure any temp conversion file is cleaned up
            # even on this early-return cache-hit path (Issue 40).
            try:
                self._add_sub_to_results(
                    str(cached_translation),
                    provider="translated",
                    release=cached_translation.stem,
                    language=lang_name,
                    parent_sub_id=parent_sub_id,
                )
                if load_slot in ("primary", "secondary"):
                    self._load_translated_into_slot(str(cached_translation), load_slot)
            finally:
                if _converted_tmp and Path(_converted_tmp).is_file():
                    try:
                        Path(_converted_tmp).unlink()
                    except OSError:
                        pass
            return

        # ── No cache — start translation thread ───────────────────────────────
        # Build model chain from settings
        model_chain = [m.strip() for m in self._settings.get("gemini_models", []) if m.strip()]
        if not model_chain:
            model_chain = ["gemini-2.5-flash-lite", "gemini-2.5-flash", "gemini-2.5-pro"]

        self.status_var.set("Translating to {}…".format(lang_name))
        self.progress.start(10)
        self.btn_load.config(state="disabled")
        # Enable the stop button so the user can cancel mid-translation.
        # Clear the event first in case a previous search set it.
        self._stop_event.clear()
        self.btn_stop.config(state="normal")

        try:
            t = threading.Thread(
                target=self._translate_worker,
                args=(srt_path, lang_code, lang_name, api_key, model_chain,
                      parent_sub_id, load_slot, _converted_tmp),
                daemon=True,
                name="subfinder-translate",
            )
            # Store in self._translate_job so _stop_search can signal cancellation
            # without conflating search-thread and translation-thread lifetimes.
            self._translate_job = t
            t.start()
        except Exception:
            # Thread construction or start failed — clean up temp file here
            # since _translate_worker's finally block will never run.
            if _converted_tmp and Path(_converted_tmp).is_file():
                try:
                    Path(_converted_tmp).unlink()
                except OSError:
                    pass
            raise

    def _do_load_then_translate(self, sub, lang_code: str, lang_name: str, api_key: str):
        """Download *sub* (if not already cached) then immediately translate it.

        Uses the existing _do_load machinery with a custom load_fn that suppresses
        the normal mpv-load step so only the file is fetched.  Once _dl_ok fires
        the real on-disk path is known and we chain straight into _translate_subtitle.
        """
        _parent_sub_id = sub.sub_id
        # If the subtitle was downloaded between menu-open and menu-select, just translate.
        cached_path = self._last_dl_path.get(sub.sub_id, "")
        if cached_path and Path(cached_path).is_file():
            self._translate_subtitle(cached_path, lang_code, lang_name, api_key,
                                     parent_sub_id=_parent_sub_id)
            return

        # Intercept the normal load so we can chain translation afterwards.
        # load_fn receives the path that _dl_ok resolved; return True so _dl_ok
        # doesn't pop the "load manually" dialog (it checks the return value).
        def _download_only_then_translate(path: str) -> bool:
            # Schedule the translation on the main thread after _dl_ok finishes.
            # load_slot="primary" so the translated result auto-loads into mpv.
            self.after(0, self._translate_subtitle, path, lang_code, lang_name, api_key,
                       _parent_sub_id, "primary")
            return True  # tell _dl_ok: load succeeded (suppresses the manual-load dialog)

        self._do_load(close_after=False, load_fn=_download_only_then_translate)

    def _translate_worker(self, srt_path: str, lang_code: str,
                          lang_name: str, api_key: str, model_chain: list,
                          parent_sub_id: "str | None" = None, load_slot: str = "",
                          converted_tmp: "Path | None" = None):
        """Background thread: call translate_srt_with_gemini(), post results to main thread."""
        total_chunks = [1]  # mutable cell — updated once we know chunk count

        def _progress(idx, total):
            total_chunks[0] = total
            self.after(0, self.status_var.set,
                       "Translating to {} — chunk {}/{}…".format(
                           lang_name, idx + 1, total))

        def _warn(msg: str):
            """Post a non-blocking warning dialog to the main thread."""
            self.after(0, lambda m=msg: messagebox.showwarning(
                "Translation Warning", m, parent=self))

        # Collect all configured Gemini keys for key rotation on 429.
        _api_keys = _get_gemini_keys()
        _chunk_size = self._settings.get("gemini_chunk_size", _GEMINI_CHUNK_SIZE)

        try:
            out_path, dropped, total_blocks = translate_srt_with_gemini(
                srt_path=srt_path,
                target_lang_code=lang_code,
                api_key=api_key,      # legacy compat: first key from the UI click
                model_chain=model_chain,
                progress_cb=_progress,
                stop_event=self._stop_event,
                warn_cb=_warn,
                chunk_size=_chunk_size,
                api_keys=_api_keys,   # full rotation list (preferred; supersedes api_key)
            )

            # Gate on translation quality.  If Gemini dropped more than half the
            # blocks (i.e. the file is mostly the original untranslated text), the
            # result is unusable.  Delete the bad file, remove it from the
            # translation output-path cache so _translate_subtitle doesn't serve
            # it on next open, and surface a real error to the user.
            #
            # Threshold: >50% dropped is a hard failure; 10–50% is a warning but
            # still considered a usable partial translation.
            if total_blocks > 0 and dropped > total_blocks // 2:
                log.error(
                    "Translation quality failure: only %d/%d blocks translated "
                    "(%.0f%% dropped) — deleting output and surfacing error",
                    total_blocks - dropped, total_blocks,
                    100.0 * dropped / total_blocks,
                )
                try:
                    Path(out_path).unlink(missing_ok=True)
                except Exception:
                    pass
                self.after(0, self._translate_fail,
                           "Translation failed: only {}/{} blocks were translated "
                           "({:.0f}% dropped).\n\n"
                           "This usually means the model hit its output token limit. "
                           "Try switching to a larger model in Settings → Models "
                           "(e.g. gemini-2.5-flash or gemini-2.5-pro).".format(
                               total_blocks - dropped, total_blocks,
                               100.0 * dropped / total_blocks))
                return

            if dropped and total_blocks > 0:
                log.warning(
                    "Translation partial: %d/%d blocks dropped (%.0f%%) — "
                    "original text kept as fallback for missing blocks",
                    dropped, total_blocks, 100.0 * dropped / total_blocks,
                )

            self.after(0, self._translate_ok, out_path, lang_name, dropped, total_blocks,
                       parent_sub_id, load_slot)
        except TranslationCancelledError:
            log.info("Translation cancelled by user")
            self.after(0, self._translate_cancelled)
        except Exception as exc:
            log.error("Translation failed: %s\n%s", exc, traceback.format_exc())
            self.after(0, self._translate_fail, str(exc))
        finally:
            # Remove the temporary SRT if we converted from ASS/SSA/VTT
            if converted_tmp is not None:
                try:
                    Path(converted_tmp).unlink(missing_ok=True)
                except Exception:
                    pass

    def _copy_translation_next_to_video(self, out_path: str, parent_sub_id: str):
        """Item 7: Copy a translated subtitle next to the currently playing local video.

        Only runs when:
        - A local video (not a URL) is playing.
        - The source subtitle (parent_sub_id) is a local or embedded file.
        - The translated file isn't already in the same folder as the video.
        The copy is a best-effort operation; any failure is logged but not surfaced.
        """
        try:
            vp = self.video_path or ""
            if not vp or bool(_URL_SCHEME_RE.match(vp)):
                return  # Not a local video
            video_dir = Path(vp).parent
            # Check that the parent sub is a local/embedded file
            parent_sub = next(
                (s for s in self.results + self.secondary_results
                 if s.sub_id == parent_sub_id),
                None,
            )
            if parent_sub is None or parent_sub.provider not in ("local", "embedded"):
                return  # Source is a downloaded sub — don't copy
            src = Path(out_path)
            dest = video_dir / src.name
            if dest.resolve() == src.resolve():
                return  # Already in the right place
            if not dest.exists():
                shutil.copy2(str(src), str(dest))
                log.info("_copy_translation_next_to_video: copied %s → %s", src.name, dest)
        except Exception as _e:
            log.warning("_copy_translation_next_to_video: non-fatal error: %s", _e)

    def _translate_ok(self, out_path: str, lang_name: str,
                      dropped: int = 0, total_blocks: int = 0,
                      parent_sub_id: "str | None" = None, load_slot: str = ""):
        self.progress.stop()
        self.btn_load.config(state="normal")
        self.btn_stop.config(state="disabled")
        fname = Path(out_path).name

        # Partial translation warning (10–50% dropped): surface to user but
        # still load the file — it has enough translated content to be useful.
        if total_blocks > 0 and dropped > 0:
            pct_ok = 100.0 * (total_blocks - dropped) / total_blocks
            self.status_var.set(
                "⚠ Translated ({:.0f}%): {}".format(pct_ok, fname))
            log.warning("_translate_ok: partial result — %.0f%% translated, loading anyway", pct_ok)
        else:
            self.status_var.set("✓ Translated: {}".format(fname))

        if _winsound:
            try:
                _winsound.MessageBeep(_winsound.MB_ICONASTERISK)
            except Exception:
                pass

        # Add translated file as a new result row so the user can load it
        # themselves via the normal UI (Load / Load as Secondary).
        # release = clean filename stem; language = full lang name.
        # The [XX] indicator is added dynamically by _insert_sub based on
        # whether the language column is visible — never baked into the release.
        self._add_sub_to_results(
            out_path,
            provider="translated",
            release=Path(out_path).stem,
            language=lang_name,
            parent_sub_id=parent_sub_id,
        )

        # Item 7: For local-video + local-source subtitle, also save the
        # translated file next to the video so it persists outside the cache.
        self._copy_translation_next_to_video(out_path, parent_sub_id)

        # If the user chose "Translate and Load as Primary/Secondary" from the
        # context menu, immediately load the result into the requested slot.
        if load_slot in ("primary", "secondary"):
            self._load_translated_into_slot(out_path, load_slot)

    def _translate_cancelled(self):
        self.progress.stop()
        self.btn_load.config(state="normal")
        self.btn_stop.config(state="disabled")
        self.status_var.set("Translation cancelled")
        log.info("_translate_cancelled: UI reset complete")

    def _translate_fail(self, reason: str):
        self.progress.stop()
        self.btn_load.config(state="normal")
        self.btn_stop.config(state="disabled")
        self.status_var.set("Translation failed")
        messagebox.showerror(
            "Translation Failed",
            "Could not translate subtitle:\n\n{}\n\n"
            "Check your Gemini API key in Settings and try again.\n"
            "See the log for details:\n{}".format(reason[:400], LOG_FILE))

    def _load_translated_into_slot(self, out_path: str, slot: str):
        """Load a translated subtitle file into mpv's primary or secondary slot.

        Called by _translate_ok / cache-hit path when the user chose
        "Translate and Load as Primary/Secondary" from the context menu.
        Mirrors the capture logic in _dl_ok so _mpv_primary/secondary_sub_id
        and _mpv_primary/secondary_sids stay in sync.
        """
        # Find the Sub entry we just added so we can update tracking fields.
        # IMPORTANT: this formula must match _add_sub_to_results(provider="translated"):
        #   sub_id = provider + "_" + md5(resolved_path) = "translated_" + md5(...)
        # If _add_sub_to_results is ever called with a different provider for translated
        # files the ID match will break and _mpv_primary_sub_id will track a phantom ID.
        sub_id = "translated_" + hashlib.md5(
            str(Path(out_path).resolve()).encode("utf-8")
        ).hexdigest()

        ok = False   # will be set by whichever load branch runs
        if slot == "primary":
            ok = load_subtitle_into_mpv(out_path)
            if ok:
                self._mpv_primary_sub_id = sub_id
        else:
            ok = load_subtitle_into_mpv_secondary(out_path)
            if ok:
                self._mpv_secondary_sub_id = sub_id

        if ok:
            log.info("_load_translated_into_slot: loaded %s as %s", out_path, slot)
            self._save_session_snapshot()
            self._tree_tags_dirty = True
            self._refresh_tree()
            self._on_select()
        else:
            log.warning("_load_translated_into_slot: mpv load failed for %s", out_path)

    def _remove_from_mpv_secondary(self, sub):
        """Remove a subtitle specifically from mpv's secondary slot.

        Used when the same subtitle is loaded as both primary and secondary —
        we need to remove only the secondary track without touching the primary.

        NOTE: Uses _mpv_secondary_sids so removing secondary never destroys
        the primary sid, even when the same subtitle is loaded in both slots.
        """
        if self._mpv_secondary_sub_id != sub.sub_id:
            return  # Nothing to do
        self._mpv_secondary_sub_id = ""
        sid_to_remove = self._mpv_secondary_sids.pop(sub.sub_id, None)
        tl = _ipc_command(["get_property", "track-list"])
        if tl is not None:
            live_sub_ids = {t["id"] for t in (tl.get("data") or []) if t.get("type") == "sub"}
            if sid_to_remove not in live_sub_ids:
                path = self._last_dl_path.get(sub.sub_id, "")
                sid_to_remove = None
                if path:
                    for t in (tl.get("data") or []):
                        if t.get("type") == "sub" and t.get("external-filename", "") == path:
                            sid_to_remove = t["id"]
                            break
        if sid_to_remove is not None:
            resp = _ipc_command(["sub-remove", sid_to_remove])
            log.info("mpv IPC: sub-remove (secondary-only) sid=%s resp=%s", sid_to_remove, resp)
        else:
            log.warning("mpv IPC: sub-remove secondary: no sid found for %r", sub.release)
        self._tree_tags_dirty = True
        self._refresh_tree()
        self._on_select()

    def _remove_from_mpv(self, sub):
        """Remove a subtitle track from mpv via IPC and clear its tracking slot."""
        # Determine which slot this sub occupies and what sid to remove.
        if self._mpv_primary_sub_id == sub.sub_id:
            slot = "primary"
            self._mpv_primary_sub_id = ""
        elif self._mpv_secondary_sub_id == sub.sub_id:
            slot = "secondary"
            self._mpv_secondary_sub_id = ""
        else:
            slot = ""
        # Use the sid captured at load time. Verify it still exists in the
        # live track-list first (user may have removed it manually via mpv UI).
        # Fall back to external-filename matching if the stored sid is gone.
        sid_to_remove = (self._mpv_primary_sids.pop(sub.sub_id, None)
                         if slot == "primary"
                         else self._mpv_secondary_sids.pop(sub.sub_id, None))
        tl = _ipc_command(["get_property", "track-list"])
        if tl is not None:
            live_sub_ids = {t["id"] for t in (tl.get("data") or []) if t.get("type") == "sub"}
            if sid_to_remove not in live_sub_ids:
                # Stored sid is stale — try matching by filename
                path = self._last_dl_path.get(sub.sub_id, "")
                sid_to_remove = None
                if path:
                    for t in (tl.get("data") or []):
                        if t.get("type") == "sub" and t.get("external-filename", "") == path:
                            sid_to_remove = t["id"]
                            break
                log.info("mpv IPC: sub-remove stale sid, fallback by filename -> sid=%s", sid_to_remove)
        if sid_to_remove is not None:
            resp = _ipc_command(["sub-remove", sid_to_remove])
            log.info("mpv IPC: sub-remove slot=%s sid=%s resp=%s", slot, sid_to_remove, resp)
        else:
            # Last-resort: try the "loaded:" path (the actual path passed to sub-add,
            # which may differ from the cached TEMP_DIR path when the file was renamed
            # next to the video).  This recovers the case where sids were not persisted
            # across a reopen and the cache_path / external-filename mismatch prevents
            # the normal filename fallback from finding the track.
            _loaded_path = self._last_dl_path.get("loaded:" + sub.sub_id, "")
            if _loaded_path and tl is not None:
                for t in (tl.get("data") or []):
                    if t.get("type") == "sub" and t.get("external-filename", "") == _loaded_path:
                        sid_to_remove = t["id"]
                        break
            if sid_to_remove is not None:
                resp = _ipc_command(["sub-remove", sid_to_remove])
                log.info("mpv IPC: sub-remove (loaded-path fallback) slot=%s sid=%s resp=%s",
                         slot, sid_to_remove, resp)
            else:
                log.warning("mpv IPC: sub-remove no sid found for %r (slot=%s)", sub.release, slot)
        self._tree_tags_dirty = True
        self._refresh_tree()
        self._on_select()

    def _ctx_delete_cache(self, sub, remove_from_results: bool = False,
                          remove_from_mpv: bool = False):
        """Remove a downloaded subtitle and all related cache entries from disk.

        remove_from_results=True additionally purges the sub from self.results /
        self.secondary_results so the row disappears entirely (used for embedded
        and translated subtitles whose file won't exist again after deletion).

        remove_from_mpv=True additionally removes the subtitle from mpv via IPC
        if it is currently loaded as the primary or secondary track (used for
        translated subtitles, which are loaded directly and must be ejected when
        deleted from cache).  _remove_from_mpv already calls _refresh_tree and
        _on_select, so the final calls below are skipped when it runs.
        """
        path = self._last_dl_path.get(sub.sub_id, "")
        if not path:
            return

        # 1. Delete the extracted subtitle file
        try:
            p = Path(path)
            if p.is_file():
                p.unlink(missing_ok=True)
                log.info("ctx_delete_cache: removed subtitle file %s", p)
        except Exception as e:
            log.warning("Could not delete cached file %s: %s", path, e)

        # 2. Load the index and remove all related entries
        self._last_dl_path.pop(sub.sub_id, None)
        with _cache_index_lock:
            idx = _load_cache_index(autosave=False)
            idx.pop(sub.sub_id, None)

            # Remove dlurl: reverse-lookup entry.
            # For season-pack subtitles all sibling episodes share the same dl_url, so
            # a single pop() here removes the reverse-lookup for the entire pack — the
            # sibling cleanup loop below does not need to pop it again.
            if sub.dl_url:
                idx.pop("dlurl:" + sub.dl_url, None)
                self._last_dl_path.pop("dlurl:" + sub.dl_url, None)

            # Remove direct_url: entry (subliminal cached download link)
            idx.pop("direct_url:" + sub.sub_id, None)

            # 3. If this came from a SubDL season pack, delete the archive and pack: entry.
            #    The pack zip key is derived from MD5 of the download URL — same formula as _dl_ok.
            if sub.provider == "subdl" and sub.dl_url:
                zip_key  = hashlib.md5(sub.dl_url.encode("utf-8")).hexdigest()
                pack_key = "pack:" + zip_key
                pack_meta_raw = idx.get(pack_key, "")
                zip_ext = ".zip"
                base_sub_id = ""
                if pack_meta_raw:
                    try:
                        _pack_meta = json.loads(pack_meta_raw)
                        zip_ext     = _pack_meta.get("zip_ext", ".zip")
                        base_sub_id = _pack_meta.get("base_sub_id", "")
                    except Exception:
                        pass
                idx.pop(pack_key, None)
                # Delete whichever archive format exists (.zip or .rar)
                for _ext in (zip_ext, ".rar", ".zip"):
                    archive = _archive_dest_for(zip_key, _ext, label=sub.release)
                    if archive.is_file():
                        try:
                            archive.unlink(missing_ok=True)
                            log.info("ctx_delete_cache: removed season pack archive %s", archive)
                        except Exception as e:
                            log.warning("Could not delete season pack archive %s: %s", archive, e)
                        break  # only delete once

                # 4. Delete all other episode .srt files previously extracted from this
                #    same season pack. Their sub_ids share the same base (e.g. "subdl_XXXX_ep1",
                #    "subdl_XXXX_ep3", etc.) and they are now orphaned since the archive is gone.
                if not base_sub_id:
                    # Fall back to stripping the _epN suffix from the current sub_id
                    base_sub_id = re.sub(r"_ep\d+$", "", sub.sub_id)
                if base_sub_id and base_sub_id != sub.sub_id:
                    ep_prefix = base_sub_id + "_ep"
                    sibling_keys = [k for k in list(idx.keys())
                                    if k.startswith(ep_prefix) and k != sub.sub_id]
                    for sib_key in sibling_keys:
                        sib_path = idx.get(sib_key, "")
                        if sib_path:
                            try:
                                sp = Path(sib_path)
                                if sp.is_file():
                                    sp.unlink(missing_ok=True)
                                    log.info("ctx_delete_cache: removed sibling episode file %s", sp)
                            except Exception as e:
                                log.warning("Could not delete sibling episode file %s: %s", sib_path, e)
                            idx.pop(sib_key, None)
                            self._last_dl_path.pop(sib_key, None)

            _save_cache_index(idx)

        self.status_var.set("Deleted from cache: {}".format(Path(path).name))
        log.info("ctx_delete_cache: removed %s", path)
        if remove_from_results:
            self.results           = [s for s in self.results           if s.sub_id != sub.sub_id]
            self.secondary_results = [s for s in self.secondary_results if s.sub_id != sub.sub_id]
            log.info("ctx_delete_cache: also removed %s from results list", sub.sub_id)
        # Remove from mpv if the sub is currently loaded as primary or secondary.
        # _remove_from_mpv sets _tree_tags_dirty and calls _refresh_tree/_on_select
        # itself, so we skip the fallback calls when it runs.
        _is_loaded_in_mpv = sub.sub_id in (self._mpv_primary_sub_id,
                                            self._mpv_secondary_sub_id)
        if remove_from_mpv and _is_loaded_in_mpv:
            self._remove_from_mpv(sub)
        else:
            self._tree_tags_dirty = True
            self._refresh_tree()
            self._on_select()

    def _ctx_remove_from_list(self, sub):
        """Remove a locally-added subtitle from the results list only.

        Does NOT delete the file from disk or from the cache index — the user's
        own file is never touched.  The entry is simply removed from self.results
        and self.secondary_results so it disappears from the tree.
        """
        self.results          = [s for s in self.results          if s.sub_id != sub.sub_id]
        self.secondary_results = [s for s in self.secondary_results if s.sub_id != sub.sub_id]
        # Also remove from the in-memory download path map so stale entries
        # don't linger, but leave the cache index file untouched.
        self._last_dl_path.pop(sub.sub_id, None)
        self.status_var.set("Removed from list: {}".format(sub.release or sub.sub_id))
        log.info("ctx_remove_from_list: removed %s from results list", sub.sub_id)
        self._tree_tags_dirty = True
        self._refresh_tree()
        self._on_select()
        self._save_session_snapshot()

    def _open_dl_folder(self):
        sub = self._selected()
        if not sub:
            return
        path = self._last_dl_path.get(sub.sub_id)
        if not path or not Path(path).exists():
            messagebox.showwarning("Not found", "File no longer exists:\n{}".format(path))
            return

        if sys.platform == "win32":
            _opened = False

            # ── Attempt 1: SHOpenFolderAndSelectItems via ctypes ───────────────
            try:
                import ctypes
                shell32 = ctypes.windll.shell32

                # Set correct restypes/argtypes — without restype=c_void_p the
                # returned PIDL pointer is truncated to 32 bits on 64-bit Python.
                shell32.ILCreateFromPathW.restype  = ctypes.c_void_p
                shell32.ILCreateFromPathW.argtypes = [ctypes.c_wchar_p]
                shell32.ILFree.argtypes            = [ctypes.c_void_p]
                shell32.SHOpenFolderAndSelectItems.restype  = ctypes.c_long  # HRESULT
                shell32.SHOpenFolderAndSelectItems.argtypes = [
                    ctypes.c_void_p,                    # pidlFolder (PCIDLIST_ABSOLUTE)
                    ctypes.c_uint,                      # cidl       (UINT)
                    ctypes.POINTER(ctypes.c_void_p),    # apidl      (void** array of child PIDLs)
                    ctypes.c_uint,                      # dwFlags    (DWORD)
                ]

                folder_pidl = shell32.ILCreateFromPathW(str(Path(path).parent))
                file_pidl   = shell32.ILCreateFromPathW(path)

                if folder_pidl and file_pidl:
                    ItemArray = ctypes.c_void_p * 1
                    items = ItemArray(file_pidl)
                    hr = shell32.SHOpenFolderAndSelectItems(folder_pidl, 1, items, 0)
                    _opened = (hr == 0)
                    log.debug("SHOpenFolderAndSelectItems hr=0x%x", hr & 0xFFFFFFFF)

                if folder_pidl:
                    shell32.ILFree(folder_pidl)
                if file_pidl:
                    shell32.ILFree(file_pidl)

            except Exception as _e:
                log.debug("SHOpenFolderAndSelectItems failed: %s", _e)

            # ── Attempt 2: explorer /select, ───────────────────────────────────
            # 0x08000000 = CREATE_NO_WINDOW
            if not _opened:
                try:
                    subprocess.Popen(
                        ["explorer", "/select,{}".format(path)],
                        creationflags=0x08000000,
                    )
                    _opened = True
                except Exception as _e:
                    log.debug("explorer /select failed: %s", _e)

            # ── Attempt 3: os.startfile on the folder (last resort) ────────────
            if not _opened:
                try:
                    os.startfile(str(Path(path).parent))
                except Exception as _e:
                    log.warning("os.startfile fallback failed: %s", _e)
                    messagebox.showerror("Error", "Could not open Explorer:\n{}".format(_e))

        elif sys.platform == "darwin":
            try:
                subprocess.Popen(["open", "-R", path])
            except Exception as _e:
                log.warning("open -R failed: %s", _e)
                try:
                    subprocess.Popen(["open", str(Path(path).parent)])
                except Exception as _e2:
                    messagebox.showerror("Error", "Could not open Finder:\n{}".format(_e2))

        else:  # Linux
            # Try specific file managers first (they support --select to highlight the
            # file).  If none are installed, xdg-open on the parent directory is the
            # guaranteed fallback — it always opens the correct file manager for the
            # current DE, though it won't pre-select the file.
            for cmd in (["nautilus", "--select", path],
                        ["dolphin", "--select", path],
                        ["nemo", "--select", path],
                        ["thunar", path],
                        ["caja", "--select", path],
                        ["pcmanfm", "--select", path],
                        ["xdg-open", str(Path(path).parent)]):
                try:
                    subprocess.Popen(cmd)
                    break
                except FileNotFoundError:
                    continue

# ─────────────────────────────────────────────────────────────────────────────
# ENTRY POINT
# ─────────────────────────────────────────────────────────────────────────────

def main():
    if sys.version_info < (3, 8):
        sys.exit(
            "SubFinder requires Python 3.8 or newer. "
            "You are running Python {}.{}.{}.".format(*sys.version_info[:3])
        )
    if "--test" in sys.argv:
        import importlib.util as _ilu
        _ok = "\u2713"
        _fail = "\u2717"
        def _chk(label, condition, note=""):
            sym = _ok if condition else _fail
            msg = "  [{}] {}".format(sym, label)
            if note:
                msg += "  ({})".format(note)
            print(msg)
            return condition

        print("\nSubFinder {} — self-test\n".format(__version__))

        # Directories
        _chk("Config dir writable", os.access(str(CONFIG_DIR), os.W_OK), str(CONFIG_DIR))
        _chk("Cache dir writable",  os.access(str(CACHE_DIR),  os.W_OK), str(CACHE_DIR))
        _chk("Log dir writable",    os.access(str(LOG_DIR),    os.W_OK), str(LOG_DIR))

        # API keys (read from settings file directly — no App instance needed)
        _s = _get_settings_cached()
        _chk("OpenSubtitles API key configured",
             bool(_s.get("oscom_api_key", "").strip()),
             "get a free key at opensubtitles.com")
        _chk("SubDL API key configured",
             bool(_s.get("subdl_api_key", "").strip()),
             "get a free key at subdl.com")
        _gemini_ok = bool(_s.get("gemini_api_key", "").strip()
                          or _s.get("gemini_api_keys", []))
        _chk("Gemini API key configured", _gemini_ok,
             "get a free key at aistudio.google.com")

        # Optional Python packages
        _chk("subliminal installed",        bool(_ilu.find_spec("subliminal")),
             "pip install subliminal babelfish dogpile.cache")
        _chk("pysubs2 installed",           bool(_ilu.find_spec("pysubs2")),
             "pip install pysubs2")
        _chk("charset_normalizer installed", bool(_ilu.find_spec("charset_normalizer")),
             "pip install charset-normalizer")
        _chk("pywin32 installed",           bool(_ilu.find_spec("win32file")),
             "pip install pywin32  (Windows — needed for IPC)")

        # External tools
        _chk("ffmpeg found",  bool(_find_ffmpeg_binary("ffmpeg")))
        _chk("ffprobe found", bool(_find_ffmpeg_binary("ffprobe")))
        _rar_path, _rar_kind = _find_rar_tool()
        _chk("UnRAR / 7-Zip found",
             bool(_rar_path),
             "{} at {}".format(_rar_kind, _rar_path) if _rar_path
             else "install WinRAR or 7-Zip")
        # Use _find_sync_tool() rather than _find_pip_binary() so that standalone
        # alass binaries on PATH (the common distribution method) are also detected.
        _sync_p, _sync_n = _find_sync_tool()
        _chk("sync tool found (ffsubsync or alass)",
             bool(_sync_p),
             "pip install ffsubsync  OR  download alass from github.com/kaegi/alass/releases")

        # Port availability
        _port_free = False
        try:
            _ts = _socket.socket(_socket.AF_INET, _socket.SOCK_STREAM)
            _ts.bind(("127.0.0.1", _INSTANCE_LOCK_PORT))
            _ts.close()
            _port_free = True
        except OSError:
            pass
        _chk("Lock port {} available".format(_INSTANCE_LOCK_PORT), _port_free,
             "another instance may already be running" if not _port_free else "")

        print()
        sys.exit(0)

    # ── Single-instance enforcement ───────────────────────────────────────────
    # Bind exactly ONE port. If it is already taken, another instance is running.
    # Using a range of ports would let rapid Ctrl+S presses each claim a different
    # port and open multiple windows — that was the original bug.
    #
    # On Windows, SO_REUSEADDR=0 alone is not sufficient: the OS still allows a
    # second process running as the same user to bind the same port unless
    # SO_EXCLUSIVEADDRUSE is set.  We set it unconditionally on Windows.
    _lock_sock = _socket.socket(_socket.AF_INET, _socket.SOCK_STREAM)
    _lock_sock.setsockopt(_socket.SOL_SOCKET, _socket.SO_REUSEADDR, 0)
    if sys.platform == "win32":
        # SO_EXCLUSIVEADDRUSE = 12 on Windows — prevents same-user rebind
        try:
            _lock_sock.setsockopt(_socket.SOL_SOCKET, 12, 1)
        except Exception:
            pass  # older Python builds may not expose the constant; best-effort
    _bound = False
    try:
        _lock_sock.bind(("127.0.0.1", _INSTANCE_LOCK_PORT))
        _bound = True
    except OSError:
        pass
    if not _bound:
        log.warning(
            "SubFinder: port %d already in use — another instance is running. Exiting.",
            _INSTANCE_LOCK_PORT,
        )
        sys.exit(0)
    # Keep _lock_sock alive for the lifetime of the process (never closed).

    log.info(
        "subfinder.py starting  subliminal_ok=%s  oscom_key_ok=%s  subdl_key_ok=%s  python=%s",
        SUBLIMINAL_OK, bool(_get_oscom_key()), bool(_get_subdl_key()),
        sys.version.split()[0]
    )
    # Run cache cleanup in a background thread so the window appears immediately.
    # _cleanup_temp_dir is thread-safe (only touches files and the cache index
    # via atomic writes).  Non-daemon so in-progress index writes are not
    # killed when the main thread exits (daemon=True caused corrupt .writing files).
    _cleanup_thread = threading.Thread(target=_cleanup_temp_dir, daemon=False, name="subfinder-cleanup")
    _cleanup_thread.start()
    App(video_path=get_playing_video()).mainloop()
    # The cleanup thread is non-daemon, so the Python interpreter implicitly waits
    # for it to finish before exiting.  No explicit join() is needed here.

if __name__ == "__main__":
    main()

# mpv-subfinder

Press **Ctrl+S** while something is playing in mpv. A window opens, results come in, click one, subtitle loads. That's it.

Searches [OpenSubtitles.com](https://www.opensubtitles.com) and [SubDL](https://subdl.com) simultaneously. Works on local files and stream URLs. No browser, no copy-pasting filenames.

![demo](.github/demo.gif)

---

## Requirements

- **mpv** (any recent build)
- **Python 3.8+** — 3.11.9 recommended, must be on your PATH
- **subliminal** *(highly recommended)* — no API key, no account. Install it and you have a working subtitle source immediately, no configuration required. `pip install subliminal babelfish dogpile.cache`
- **pywin32** *(highly recommended, Windows only)* — the primary way SubFinder talks to mpv. Handles path reading and subtitle injection directly into the player. `pip install pywin32`

---

## API Keys

SubFinder has three subtitle sources. Configure them in **Settings** after first launch — not in any config file.

**OpenSubtitles.com** — free API key required  
Get one at [opensubtitles.com/en/consumers](https://www.opensubtitles.com/en/consumers). Free accounts get 20 subtitle downloads per day. Enter your OS.com username and password in the Settings gear (⚙) for a higher daily quota. When this provider is enabled, the direct REST API is the primary search path, including moviehash matching against your local file for best sync accuracy.

**SubDL** — free API key required  
Get one at [subdl.com/account/api](https://subdl.com/account/api). Runs independently alongside OpenSubtitles.com.

**subliminal** — no API key needed  
Install the `subliminal` package and SubFinder gains access to the legacy OpenSubtitles provider, which works with no credentials at all. It is used as a fallback when the direct OS.com API returns no results — and it works entirely on its own if you have no API keys configured. See [Optional packages](#optional-packages).

**Gemini** — only needed for subtitle translation  
Used exclusively for the right-click Translate to… feature. Has nothing to do with search or download. Get a free key at [aistudio.google.com](https://aistudio.google.com).

---

## Installation

### 1. Copy the scripts

**Windows** — `%APPDATA%\mpv\scripts\`
```
subfinder.py
subfinder_loader.lua
```

**Linux / macOS** — `~/.config/mpv/scripts/`
```
subfinder.py
subfinder_loader.lua
```

### 2. Enable the IPC server in mpv.conf

SubFinder reads the currently playing file path from mpv over IPC. Without this, path detection falls back to the command-line argument passed at launch, which works for most local files but is less reliable for streams.

**Windows** — add to `%APPDATA%\mpv\mpv.conf`:
```
input-ipc-server=\\.\pipe\mpvpipe
```

**Linux / macOS** — add to `~/.config/mpv/mpv.conf`:
```
input-ipc-server=/tmp/mpv-socket
```

Restart mpv after editing.

### 3. Done

Start mpv, open any video, press **Ctrl+S**. On first launch SubFinder creates its data folder next to the script and opens with a blank settings page. Enter your API keys and run a search.

---

## Windows — pywin32

```
pip install pywin32
```

On Windows, pywin32 is what SubFinder uses to communicate with mpv over named pipes for path reading and subtitle injection. Without it, auto-loading a subtitle directly into mpv is disabled — SubFinder downloads the file and shows you its path in a dialog instead. You can then drag it into mpv or use mpv's own subtitle menu.

---

## The Ctrl+S override

`subfinder_loader.lua` uses `add_forced_key_binding`, which replaces mpv's built-in **Ctrl+S screenshot** shortcut. To restore it, add to `input.conf`:

```
s        screenshot
S        screenshot-window
```

---

## Optional packages

```
# Legacy OpenSubtitles provider — works with no API key at all
pip install subliminal babelfish dogpile.cache

# Format conversion: lets you translate ASS/SSA/VTT files and strip HI/SDH from non-SRT formats
pip install pysubs2

# Encoding detection: fixes garbled characters in non-UTF-8 subtitle files
pip install charset-normalizer

# Subtitle/audio sync (resource-intensive — use sparingly)
pip install ffsubsync
```

Or install everything at once:
```
pip install -r requirements-optional.txt
```

**External tools** (not pip):
- **ffmpeg** — needed for embedded subtitle extraction and auto sync. Download from [ffmpeg.org](https://ffmpeg.org). SubFinder searches common install paths and the system PATH automatically.
- **WinRAR or 7-Zip** — needed to extract `.rar` subtitle packs from SubDL. ZIP packs work without either.

---

## Verify your setup

Run this in a terminal to check Python, API keys, optional packages, ffmpeg, and sync tools all at once:

```
python subfinder.py --test
```

---

## Features

**Search**
- Results from OpenSubtitles.com (direct REST API with moviehash matching for best sync), SubDL, and optionally the legacy subliminal provider — all in one search
- Score column shows match quality 0–100%. 99% means a byte-exact hash match against your file — sync is guaranteed. Lower scores are query-matched
- Search multiple languages in a single pass
- Sort by Score, Language, Format, Provider, or Release; drag column headers to reorder
- Pre-fills the search query automatically from the video filename, stream URL, or mpv media title
- Secondary / fallback results appear below a collapsed toggle row

**Loading**
- Double-click or press Enter to load a subtitle as the primary track
- Right-click → Load as Secondary Subtitle to load a second track simultaneously
- Downloaded subtitles are cached — cached rows load instantly with no re-download

**Season packs**
- When SubDL returns a full-season archive, SubFinder extracts the subtitle for the current episode and keeps the archive on disk so every other episode in the season loads instantly from cache
- ZIP packs work out of the box. RAR packs require WinRAR or 7-Zip

**Right-click menu (on a result row)**
- Load as Primary / Secondary Subtitle
- Remove Primary / Secondary from mpv
- Show in Explorer / Finder
- Copy file path, URL, or release name
- Translate to… — translates the subtitle into any supported language via Gemini. Downloads first if needed. Result is cached; clicking again is instant
- Strip HI/SDH annotations — removes speaker labels, `[sound effects]`, and ♪ music lines in-place, then reloads in mpv. Shown when HI/SDH content is detected in the subtitle or inferred from the release name
- Auto sync — corrects subtitle timing against the video audio using ffsubsync or alass. Works for local files and direct HTTP/HTTPS URLs. Audio is extracted by ffmpeg and cached for 2 hours so subsequent syncs of the same video start near-instantly. Live streams (HLS/DASH) are not supported
- Delete from Cache / Remove from List

**Right-click on empty area**
- Add Subtitle File… — browse for any subtitle file on disk and add it to the results list
- Extract Current Subtitle / Extract All Subtitles — pulls subtitle tracks from the local video file using ffmpeg. Image-based tracks (PGS, DVD) are not supported

**Settings**
- 20+ built-in colour themes
- Row height and font size scaling
- Toggle Score, Release, Language, Provider, Format columns
- Auto-search on open, double-click-to-close, lock window size, remember window position
- Gemini configuration: multiple API keys (each runs as a parallel translation worker), configurable model chain and chunk size

---

## What's stored on disk

SubFinder creates a `SubFinder/` folder next to the script:

| Path | Contents |
|------|----------|
| `config/subfinder_settings.json` | Settings and API keys |
| `cache/` | Search result cache, subtitle index, trigger file |
| `logs/subfinder.log` | Debug log (rotated at 2 MB, 3 backups kept) |

Downloaded subtitle files go to the system temp directory under `mpv_subs/`. The cache is capped at 200 MB and cleaned automatically.

**API keys are stored in plaintext** in `subfinder_settings.json`. Don't commit that folder or sync it to untrusted cloud storage.

---

## subfinder_title.lua (optional)

A companion script that sets a clean window title in mpv every time a file loads — no subtitle searching involved. Useful for streams and files with messy names.

Copy to your scripts folder alongside `subfinder.py`:
```
subfinder_title.lua
```

It reads SubFinder's session cache, so titles SubFinder has already resolved appear instantly.

> **Note:** Session cache and cd_cache lookups in `subfinder_title.lua` are currently Windows-only. On Linux and macOS the script still runs and applies title cleaning — cached lookups are just silently skipped.

---

## Troubleshooting

**Window never opens when I press Ctrl+S**  
Run `python subfinder.py --test` in a terminal to verify Python is reachable. On Windows, make sure Python was installed with "Add to PATH" checked. If not, find the full path to `python.exe` — you can hardcode it in `subfinder_loader.lua` at the `command_sets` block near the top of the file.

**Ctrl+S does nothing and there are no errors**  
Open mpv's console with `` ` `` and look for `SubFinder loaded — Ctrl+S ready` in the output. If absent, the script isn't being loaded — check the filename and folder path.

**Subtitle doesn't appear in mpv after clicking a result (Windows)**  
Install pywin32: `pip install pywin32`. Without it SubFinder cannot inject the subtitle directly and shows a dialog with the file path instead.

**Pre-filled search query is wrong or empty**  
Enable the IPC server in `mpv.conf` as described above, and install pywin32 on Windows.

**No results**  
First, make sure `subliminal` is installed — it requires no API key and works on its own as a reliable fallback, so it's the easiest way to guarantee you always get results. If you haven't: `pip install subliminal babelfish dogpile.cache`. Beyond that, confirm at least one API key is entered in Settings and the corresponding provider is enabled. Try simplifying the query — remove the year, resolution, and release tags. Run `python subfinder.py --test` to confirm keys are detected.

**RAR pack fails to extract**  
Install WinRAR or 7-Zip. SubFinder checks the Windows registry and common install paths automatically.

The in-app **Help** button covers everything in more detail, including file locations and the full right-click menu reference.

---

## License

MIT — see [LICENSE](LICENSE).

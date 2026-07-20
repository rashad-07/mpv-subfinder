<img src=".github/icon.png" alt="SubFinder" width="40" align="left">

# mpv-subfinder

<br clear="right"/>

![Python](https://img.shields.io/badge/python-3.10+-3776AB?logo=python&logoColor=fff&labelColor=555555) ![License](https://img.shields.io/badge/license-MIT-brightgreen?labelColor=555555) ![Platform](https://img.shields.io/badge/platform-Windows%20%7C%20Linux%20%7C%20macOS-c0392b?labelColor=555555)

Press **Ctrl+S** while something is playing in mpv. A window opens, results come in, click one, subtitle loads. That's it.

Searches OpenSubtitles.com and SubDL at once, with subliminal as a no-key fallback if you'd rather not sign up for anything. Works on local files and stream URLs — no browser, no copy-pasting filenames.

<p align="center">
  <img src=".github/demo.gif" alt="demo">
</p>

---

> **Note:** Built with AI assistance — I'm not a professional developer. The tool works well in practice, but ongoing maintenance may be limited. Contributions and bug reports are [welcome](https://github.com/rashad-07/mpv-subfinder/issues). Tested and confirmed working on **Windows**. Linux and macOS support is included in the code but untested — use at your own risk.

---

## Contents

- [Requirements](#requirements)
- [API Keys](#api-keys)
- [Installation](#installation)
- [The Ctrl+S override](#the-ctrls-override)
- [Optional packages](#optional-packages)
- [Verify your setup](#verify-your-setup)
- [Features](#features)
- [What's stored on disk](#whats-stored-on-disk)
- [subfinder_title.lua](#subfinder_titlelua-optional)
- [Troubleshooting](#troubleshooting)
- [License](#license)

---

## Requirements

- **mpv** (any recent build)
- **Python 3.10+** — 3.11.9 recommended, must be on your PATH
- **subliminal** *(highly recommended)* — no API key, no account. Install it and you have a working subtitle source immediately, no configuration required. `pip install subliminal babelfish dogpile.cache`
- **pywin32** *(highly recommended, Windows only)* — the primary way SubFinder talks to mpv. Handles path reading and subtitle injection directly into the player. `pip install pywin32`

---

## API Keys

SubFinder has three subtitle sources. Configure them in **Settings** after first launch — not in any config file.

**OpenSubtitles.com** — free API key required  
Get one at [opensubtitles.com/en/consumers](https://www.opensubtitles.com/en/consumers). Enter your OS.com username and password in the Settings gear (⚙) for a higher daily quota. When this provider is enabled, the direct REST API is the primary search path, including moviehash matching against your local file for best sync accuracy.

**SubDL** — free API key required  
Get one at [subdl.com/account/api](https://subdl.com/account/api). Runs independently alongside OpenSubtitles.com.

**subliminal** — no API key needed  
Install the `subliminal` package and SubFinder gains access to the legacy OpenSubtitles provider, which works with no credentials at all. It also kicks in when OS.com's direct returns 0 results. See [Optional packages](#optional-packages).

**Gemini** — only needed for subtitle translation  
Used exclusively for the right-click Translate to feature. Get a free key at [aistudio.google.com](https://aistudio.google.com).

---

## Installation

### 1. Copy the scripts

**Windows** — `%APPDATA%\mpv\scripts\` (or `%APPDATA%\mpv.net\scripts\` if you use mpv.net)
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

## The Ctrl+S override

`subfinder_loader.lua` uses `add_forced_key_binding`, which replaces mpv's built-in **Ctrl+S screenshot** shortcut. To restore it, add to `input.conf`:

```
s        screenshot
S        screenshot-window
```

---

## Optional packages

**Windows — named pipe IPC** *(highly recommended on Windows)*
```
pip install pywin32
```

**Legacy subtitle provider — no API key needed** *(highly recommended)*
```
pip install subliminal babelfish dogpile.cache
```

**Subtitle format conversion** — required for translating ASS/SSA/VTT/.sub (MicroDVD) files, for ffsubsync to sync .sub files, and for stripping SDH from non-SRT formats
```
pip install pysubs2
```

**Encoding detection** — fixes garbled characters in non-UTF-8 subtitle files
```
pip install charset-normalizer
```

**Subtitle/audio sync** — resource-intensive, use sparingly
```
pip install ffsubsync
```

Or install everything at once:
```
pip install -r requirements-optional.txt
```

**External tools** (not pip):

**ffmpeg** — needed for embedded subtitle extraction and auto sync. SubFinder finds it automatically if it's on your PATH.
```
winget install -e --id Gyan.FFmpeg
```

**7-Zip** — needed to extract `.rar` subtitle packs from SubDL. ZIP packs work without it.
```
winget install -e --id 7zip.7zip
```

Or WinRAR:
```
winget install -e --id RARLab.WinRAR
```

Or **bsdtar** — pre-installed on macOS (it is the system `tar`) and on Windows 10 1803+ (`tar.exe`). On Linux, install via `apt install libarchive-tools` or `pacman -S bsdtar`. SubFinder detects it automatically.

---

## Verify your setup

Run this in a terminal to check mpv connectivity, API keys, optional packages, ffmpeg, and sync tools all at once:

```
python subfinder.py --test
```

---

## Features

Search hits OpenSubtitles.com and SubDL at the same time, plus subliminal as a no-key fallback if you don't want to bother with accounts. Moviehash matching gets you a 93–99% score when your file matches exactly — basically a guaranteed sync.

Full season packs from SubDL get auto-matched to whatever episode you're watching, and the rest of the season loads instantly from cache after that.

Translation goes through Gemini, and you can run multiple keys in parallel for speed. If it gets interrupted, it resumes from where it left off instead of re-translating everything, and it keeps character names consistent even across chunks handled by different keys.

Auto Sync fixes drifted timing against the video's own audio. Rescale FPS and Offset Subtitle handle the more specific cases — frame-rate mismatches and fixed time shifts — and both can be undone independently. Strip SDH annotations pulls out speaker labels, sound effects, and music-note lines in one click.

There's also embedded subtitle extraction straight from a video file, 20+ colour themes, and the usual row height / font / column settings.

Everything above — every setting, every right-click action, every edge case — is covered in full by the in-app **Help** (the **?** button, top-right of the main window). This README is just enough to get you installed.

---

## What's stored on disk

SubFinder creates a `SubFinder/` folder next to the script:

| Path | Contents |
|------|----------|
| `config/subfinder_settings.json` | Settings and API keys |
| `cache/` | Search result cache, subtitle index, trigger file |
| `logs/subfinder.log` | Debug log (rotated at 2 MB, 3 backups kept) |

Downloaded subtitle files go to the system temp directory under `mpv_subs/`. The cache is capped at 200 MB and cleaned automatically.

**API keys are stored in plaintext** in `subfinder_settings.json`. Don't commit that folder or sync it to untrusted cloud storage. API keys for every provider are automatically redacted from the log file.

---

## subfinder_title.lua (optional)

A small companion script — resolves a clean window title for URL streams with opaque or messy URLs. No subtitle searching involved. Copy `subfinder_title.lua` into your scripts folder alongside `subfinder.py`; it reads SubFinder's session cache, so titles SubFinder has already resolved appear instantly. Session-cache lookups are currently Windows-only — it still runs and applies title cleaning on Linux/macOS, cached lookups are just silently skipped there.

---

## Troubleshooting

**Window never opens when I press Ctrl+S**  
Run `python subfinder.py --test` in a terminal to verify Python is reachable. On Windows, make sure Python was installed with "Add to PATH" checked. If not, find the full path to `python.exe` — you can hardcode it in `subfinder_loader.lua` at the `command_sets` block, near the end of the file, inside the Ctrl+S key binding.

**Ctrl+S does nothing and there are no errors**  
Open mpv's console with `` ` `` and look for `SubFinder loaded — Ctrl+S ready` in the output. If absent, the script isn't being loaded — check the filename and folder path.

**Remove Subtitle from mpv doesn't work (Windows)**  
Install pywin32: `pip install pywin32`. Without it, many features that rely on direct communication with mpv may not work or behave inconsistently. Installing pywin32 is strongly recommended on Windows.

**Pre-filled search query is wrong or empty**  
Enable the IPC server in `mpv.conf` as described above, and install pywin32 on Windows.

**No results**  
First, make sure `subliminal` is installed — it requires no API key and works on its own as a reliable fallback, so it's the easiest way to guarantee you always get results. If you haven't: `pip install subliminal babelfish dogpile.cache`. Beyond that, confirm at least one API key is entered in Settings and the corresponding provider is enabled. Try simplifying the query — remove the year, resolution, and release tags. Run `python subfinder.py --test` to confirm keys are detected.

**RAR pack fails to extract**  
Install WinRAR, 7-Zip, or bsdtar (pre-installed on macOS; on Linux: `apt install libarchive-tools`; on Windows 10+: `tar.exe` is already on your PATH). SubFinder checks the Windows registry and common install paths automatically.

**Something's acting up and you're not sure why**  
Settings → Clear All Caches flushes everything — downloads, search session, index, log, and subliminal's own cache. You'll need to re-enter your OS.com auth afterward if you were using it.

The in-app **Help** button (top-right of the main window) covers everything in more detail, including file locations and the full right-click menu reference.

---

## License

MIT — see [LICENSE](LICENSE).

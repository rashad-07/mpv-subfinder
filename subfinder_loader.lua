-- subfinder_loader.lua
-- Shortcut: Ctrl+S
-- NOTE: Ctrl+S is a forced binding that overrides mpv's default screenshot shortcut.

-- ─── Platform detection ───────────────────────────────────────────────────────
-- Detection strategy (most-reliable first):
--   1. OS == "Windows_NT"  — set by the Windows kernel, never present on Linux/macOS
--   2. APPDATA starts with a drive letter (C:\...)  — eliminates WSL bleed-through
--      where Windows env vars leak into the Linux process but the mpv binary is
--      a native Linux/ELF executable.  On genuine Windows, APPDATA always starts
--      with a drive letter.  On WSL with env bleed-through, OS is absent so only
--      this second guard triggers — which we now require to include a drive letter.
--
-- This makes the check immune to WSL2 environment variable bleed-through.

local _appdata_raw        = os.getenv("APPDATA") or ""
local _appdata_is_windows = (#_appdata_raw >= 3 and
                              _appdata_raw:match("^[A-Za-z]:[/\\]") ~= nil)
local _os_env             = os.getenv("OS") or ""   -- nil → "" so comparisons are safe

local _IS_WINDOWS = (_os_env == "Windows_NT") or
                    (_appdata_is_windows and _os_env ~= "")

-- ─── Path resolution ──────────────────────────────────────────────────────────
-- Both platforms try mp.get_script_directory() first — it returns the directory
-- that contains THIS script file, so it works for any install layout (mpv.net,
-- plain mpv on Windows, portable installs, custom XDG paths, etc.).
--
-- Windows fallback (if mp.get_script_directory() is unavailable):
--   %APPDATA%\mpv.net\scripts\   — mpv.net layout
--   %APPDATA%\mpv\scripts\       — plain mpv layout
--   Both are tried in order; whichever contains subfinder.py wins.
--
-- Unix fallback:
--   $XDG_CONFIG_HOME/mpv/scripts  (or ~/.config/mpv/scripts)
--
-- NOTE: mp.get_script_directory() may return a path with or without a trailing
-- separator depending on the mpv version / fork, so we always strip any trailing
-- slash/backslash before appending our own separator.

local SEP = _IS_WINDOWS and "\\" or "/"

local SCRIPT_DIR

-- Helper — strip one trailing separator (if any)
local function _strip_trailing_sep(p)
    if p and #p > 1 and (p:sub(-1) == "/" or p:sub(-1) == "\\") then
        return p:sub(1, -2)
    end
    return p
end

-- Try mp.get_script_directory() on all platforms first.
local _script_dir_via_api = nil
local _ok, _result = pcall(mp.get_script_directory)
if _ok then _script_dir_via_api = _result end

if _script_dir_via_api and _script_dir_via_api ~= "" then
    -- Reliable — use it regardless of platform.
    SCRIPT_DIR = _strip_trailing_sep(_script_dir_via_api) .. SEP
    mp.msg.verbose("SubFinder: script dir resolved via mp.get_script_directory(): " .. SCRIPT_DIR)
elseif _IS_WINDOWS then
    -- Fallback for older Windows mpv builds that don't expose the API.
    -- Try known script locations in order; whichever contains subfinder.py wins.
    local app_data = os.getenv("APPDATA")
    if not app_data or app_data == "" then
        local user_profile = os.getenv("USERPROFILE")
        if user_profile and user_profile ~= "" then
            app_data = user_profile .. "\\AppData\\Roaming"
        else
            mp.msg.error("SubFinder: Cannot resolve APPDATA or USERPROFILE — aborting load.")
            app_data = nil
        end
    end
    if not app_data then
        error("SubFinder: unresolvable APPDATA on Windows — loader disabled.")
    end

    -- Probe both candidate locations; use whichever one actually contains subfinder.py.
    -- If neither exists yet (first run), default to the first candidate path.
    local _candidates = {
        app_data .. "\\mpv.net\\scripts\\",
        app_data .. "\\mpv\\scripts\\",   -- plain mpv on Windows
    }
    SCRIPT_DIR = _candidates[1]  -- default
    for _, candidate in ipairs(_candidates) do
        local f = io.open(candidate .. "subfinder.py", "r")
        if f then
            f:close()
            SCRIPT_DIR = candidate
            mp.msg.verbose("SubFinder: Windows APPDATA fallback matched layout: " .. SCRIPT_DIR)
            break
        end
    end
else
    -- Unix fallback (mp.get_script_directory() unavailable — very old mpv builds).
    local xdg_config = os.getenv("XDG_CONFIG_HOME")
    if not xdg_config or xdg_config == "" then
        local home = os.getenv("HOME")
        if not home or home == "" then
            mp.msg.error("SubFinder: Cannot resolve HOME — aborting load.")
            error("SubFinder: unresolvable HOME on Unix — loader disabled.")
        end
        xdg_config = home .. "/.config"
    end
    SCRIPT_DIR = xdg_config .. "/mpv/scripts/"
    mp.msg.verbose("SubFinder: Unix XDG fallback: " .. SCRIPT_DIR)
end

local SCRIPT_PATH  = SCRIPT_DIR .. "subfinder.py"
-- Python writes the trigger into a SubFinder/ subdirectory inside the scripts folder.
-- Must match: scripts/SubFinder/cache/subtitle_trigger.txt
local TRIGGER_FILE = SCRIPT_DIR .. "SubFinder" .. SEP .. "cache" .. SEP .. "subtitle_trigger.txt"

-- How often to poll while waiting for Python (ms), and how long before giving up
local POLL_INTERVAL = 500
local POLL_TIMEOUT  = 900000  -- 15 minutes — resets on each subtitle activity

local function read_file(path)
    local f, err = io.open(path, "r")
    if not f then
        -- Log unexpected errors (permission denied, path too long, etc.) so they
        -- are visible in the mpv log rather than silently swallowed.
        mp.msg.verbose('SubFinder: readFile failed for "' .. path .. '": ' .. tostring(err))
        return nil
    end
    local content = f:read("*a")
    f:close()
    return (content and content ~= "") and content or nil
end

local function delete_trigger()
    -- Use platform-appropriate deletion.
    -- On Windows: cmd /c del   (handles spaces; the path is passed as a plain arg)
    -- On Unix:    rm -f        (POSIX, works on all Linux/macOS mpv forks)
    local args = _IS_WINDOWS
        and {"cmd", "/c", "del", "/f", "/q", TRIGGER_FILE}
        or  {"rm", "-f", TRIGGER_FILE}
    mp.command_native({
        name          = "subprocess",
        args          = args,
        playback_only = false,
    })
end

-- ─── Startup stale-trigger cleanup ───────────────────────────────────────────
-- Clear stale trigger files on startup (one-time, no polling).
-- Only delete if the timestamp embedded in the file is more than 30 seconds old,
-- so a valid trigger written by a Python GUI that was already running before mpv
-- restarted is preserved rather than silently discarded.
do
    local raw = read_file(TRIGGER_FILE)
    if raw then
        raw = raw:match("^%s*(.-)%s*$")  -- trim
        local pipe   = raw:find("|", 1, true)
        local ts     = pipe and tonumber(raw:sub(1, pipe - 1)) or nil
        local now_ms = os.time() * 1000
        -- Delete if malformed, or older than 30 seconds at startup time.
        if ts == nil or (now_ms - ts) > 30000 then
            mp.msg.verbose("SubFinder: removing stale trigger file (age " ..
                (ts == nil and "unknown" or tostring(math.floor((now_ms - ts) / 1000)) .. "s") .. ")")
            delete_trigger()
        else
            mp.msg.verbose("SubFinder: keeping recent trigger file written " ..
                tostring(math.floor((now_ms - ts) / 1000)) .. "s ago")
        end
    end
end

-- ─── On-demand poller ────────────────────────────────────────────────────────
-- _poll_timer is non-nil only while we're actively waiting for Python to respond.
-- During normal playback it is always nil, so there is zero disk I/O.

local _poll_timer       = nil
local _poll_start       = 0
local _last_loaded_path = ""
local _launch_ts        = 0   -- timestamp of the most recent Ctrl+S press (ms)

local function stop_polling()
    if _poll_timer ~= nil then
        _poll_timer:kill()
        _poll_timer = nil
        mp.msg.info("SubFinder: poller stopped")
    end
end

local function start_polling()
    -- Always restart so _poll_start and _launch_ts are fresh for the new session.
    stop_polling()
    _poll_start = os.time() * 1000
    mp.msg.info("SubFinder: poller started")

    _poll_timer = mp.add_periodic_timer(POLL_INTERVAL / 1000, function()

        -- Timeout: Python GUI was probably closed without selecting a sub
        local now_ms = os.time() * 1000
        if now_ms - _poll_start > POLL_TIMEOUT then
            mp.msg.info("SubFinder: poller timed out")
            stop_polling()
            return
        end

        local raw = read_file(TRIGGER_FILE)
        if not raw then return end
        raw = raw:match("^%s*(.-)%s*$")  -- trim
        if raw == "" then return end

        -- Format written by Python: "<timestamp_ms>|<path>"  (primary)
        --                        or "<timestamp_ms>|secondary|<path>"  (secondary)
        local pipe = raw:find("|", 1, true)
        if not pipe then return end  -- malformed — ignore

        local ts   = tonumber(raw:sub(1, pipe - 1))
        local rest = raw:sub(pipe + 1):match("^%s*(.-)%s*$")  -- trim

        local is_secondary = false
        local sub_path
        if rest:sub(1, 10) == "secondary|" then
            is_secondary = true
            sub_path = rest:sub(11):match("^%s*(.-)%s*$")  -- trim
        else
            sub_path = rest:match("^%s*(.-)%s*$")  -- trim
        end

        -- Reject malformed timestamps (tonumber returns nil for non-numeric input).
        -- nil comparisons always return false, so without this guard a corrupt
        -- trigger file would bypass the staleness check below.
        if ts == nil then
            mp.msg.warn("SubFinder: trigger file has non-numeric timestamp — ignoring.")
            return
        end

        -- Ignore trigger files written before the most recent Ctrl+S press
        -- (stale files from a previous session or an earlier search this session).
        -- 5-second grace window for minor clock differences.
        if ts < _launch_ts - 5000 then return end

        -- Any fresh trigger file = user is actively using the GUI — reset the timeout.
        _poll_start = os.time() * 1000

        -- Ignore if we already loaded this exact path
        if sub_path == _last_loaded_path then return end

        if #sub_path > 3 then
            mp.msg.info("Subtitle trigger: " .. sub_path)
            delete_trigger()
            -- Do NOT stop polling here — the Python GUI may still be open and the
            -- user may load another subtitle. The poller will naturally expire after
            -- POLL_TIMEOUT if nothing more arrives. Stopping here was the root cause
            -- of "second subtitle never loads without reopening the window".

            -- Attempt to load the subtitle.
            local add_err = nil
            local ok_add, err_add = pcall(function()
                if is_secondary then
                    -- Snapshot existing subtitle track IDs before adding the new one.
                    -- We diff the track-list after sub-add to find the freshly added
                    -- track's integer ID, then assign it to secondary-sid explicitly.
                    -- Setting secondary-sid="auto" is NOT a valid value and does not
                    -- actually assign the secondary slot.
                    local tracks_before = {}
                    local ok_tl, tlist = pcall(function()
                        return mp.get_property_native("track-list")
                    end)
                    if ok_tl and tlist then
                        for _, t in ipairs(tlist) do
                            if t.type == "sub" then
                                tracks_before[t.id] = true
                            end
                        end
                    end
                    -- non-fatal — fall back to best-effort below

                    mp.commandv("sub-add", sub_path, "auto")

                    -- Find the new track ID by diffing the track-list.
                    local new_track_id = nil
                    local ok_tl2, tlist_after = pcall(function()
                        return mp.get_property_native("track-list")
                    end)
                    if ok_tl2 and tlist_after then
                        for _, t in ipairs(tlist_after) do
                            if t.type == "sub" and not tracks_before[t.id] then
                                new_track_id = t.id
                                break
                            end
                        end
                    end
                    -- non-fatal

                    if new_track_id ~= nil then
                        mp.set_property_number("secondary-sid", new_track_id)
                        mp.msg.info("SubFinder: secondary-sid set to track " .. tostring(new_track_id))
                    else
                        -- Track-list diff failed (e.g. very old mpv build); fall back to
                        -- cycling secondary-sid to the last subtitle track.
                        mp.msg.warn("SubFinder: could not determine new track ID — secondary-sid unchanged.")
                    end
                else
                    mp.commandv("sub-add", sub_path, "select")
                end
            end)

            if not ok_add then
                add_err = err_add
            end

            if add_err then
                mp.msg.error('SubFinder: sub-add failed for "' .. sub_path .. '": ' .. tostring(add_err))
                mp.osd_message("Subtitle load failed — check the log.", 4)
                -- Do NOT update _last_loaded_path so the user can retry the same file.
            else
                -- Mark as loaded so re-appearing trigger files for this exact path
                -- are ignored, but the poller keeps running for different paths.
                _last_loaded_path = sub_path
                mp.osd_message(is_secondary and "Secondary subtitle loaded!" or "Subtitle loaded successfully!", 3)
            end
        end
    end)
end

-- ─── Key binding ─────────────────────────────────────────────────────────────
-- NOTE: mp.add_forced_key_binding overrides mpv's built-in ctrl+s (screenshot).
-- If you rely on the screenshot shortcut, remap it in input.conf.

mp.add_forced_key_binding("ctrl+s", "open-subfinder", function()
    local video_path = mp.get_property("path")

    -- mp.get_property("path") is synchronous — a second identical call in the
    -- same Lua coroutine cannot return a different value. If path is still absent,
    -- we pass an empty string and let the Python script handle the no-file case.
    if not video_path or video_path:match("^%s*$") then
        video_path = ""
        mp.msg.info("SubFinder: no media path available — launching with empty path.")
    end

    _launch_ts        = os.time() * 1000  -- mark when this search started
    _last_loaded_path = ""                -- reset so a retry always goes through
    delete_trigger()

    -- Stop any previous poll cycle and start a fresh one
    stop_polling()

    local launched = false

    -- Build the command list depending on the platform.
    -- Windows: prefer pythonw (no console window) → python → py -3
    -- Unix:    python3 → python  (pythonw and py -3 don't exist on Linux/macOS)
    local command_sets
    if _IS_WINDOWS then
        command_sets = {
            {"pythonw", SCRIPT_PATH, video_path},
            {"python",  SCRIPT_PATH, video_path},
            {"py", "-3", SCRIPT_PATH, video_path},
        }
    else
        command_sets = {
            {"python3", SCRIPT_PATH, video_path},
            {"python",  SCRIPT_PATH, video_path},
        }
    end

    for i, cmd in ipairs(command_sets) do
        local res = mp.command_native({
            name          = "subprocess",
            args          = cmd,
            detach        = true,
            playback_only = false,
        })

        -- With detach:true mpv may return {} (no error_string) even for a missing
        -- executable because the OS-level error occurs after detach. We treat any
        -- result without an error_string as a successful launch and rely on the
        -- poller timeout to recover if Python never actually writes the trigger.
        if not res or (res.error_string and res.error_string ~= "") then
            mp.msg.error(
                "SubFinder launch attempt " .. tostring(i) .. " of " .. tostring(#command_sets) ..
                ' ("' .. cmd[1] .. '") failed: ' ..
                (res and res.error_string and res.error_string ~= "" and res.error_string or "null result")
            )
        else
            launched = true
            mp.msg.info('SubFinder: launched via "' .. cmd[1] .. '"')
            break
        end
    end

    if not launched then
        mp.osd_message("Error: Could not launch SubFinder", 5)
        return
    end

    start_polling()  -- ← only starts polling now that Python is running
    mp.osd_message("SubFinder opening...", 3)
end)

mp.msg.info("SubFinder loaded — Ctrl+S ready")

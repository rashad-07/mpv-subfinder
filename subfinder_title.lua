--[[
  subfinder_title.lua — standalone mpv script
  =====================================================
  Automatically sets mpv's window title to a clean, human-readable show name
  every time a file or URL starts playing — without opening SubFinder at all.

  HOW IT WORKS
  ─────────────
  1. Session cache  — last_session.json (exact match to what SubFinder resolved)
  2. cd_cache.json  — Content-Disposition filenames cached by SubFinder
  3. HEAD request   — fetches Content-Disposition header via PowerShell (async,
                      Windows only; falls back silently on Linux/macOS)
  4. clean_path()   — URL segment heuristic (same logic as SubFinder)
  5. media-title    — cleaned mpv property
  6. Polling        — for opaque CDN URLs where nothing else works

  INSTALLATION
  ─────────────
  Copy this file to the same folder as SubFinder.py:
    %APPDATA%\mpv.net\scripts\subfinder_title.lua   (mpv.net)
    %APPDATA%\mpv\scripts\subfinder_title.lua        (mpv)

  OPTIONAL CONFIG  (create script-opts/subfinder_title.conf)
  ──────────────────────────────────────────────────────────
    enabled=yes
    use_session_cache=yes
    use_cd_cache=yes
    use_head_request=yes
    skip_youtube=yes
--]]

local opts = {
    enabled           = "yes",
    use_session_cache = "yes",
    use_cd_cache      = "yes",
    use_head_request  = "yes",
    skip_youtube      = "yes",
}
(require "mp.options").read_options(opts, "subfinder_title")

if opts.enabled ~= "yes" then return end

-- ── helpers ───────────────────────────────────────────────────────────────────

local function trim(s)
    return (s:gsub("^%s+", ""):gsub("%s+$", ""))
end

local function is_url(path)
    return path and path:match("^[a-zA-Z][a-zA-Z0-9+%.%-]*://") ~= nil
end

local function is_youtube(path)
    if not path then return false end
    return path:match("youtube%.com") ~= nil
        or path:match("youtu%.be") ~= nil
        or path:match("music%.youtube%.com") ~= nil
end

local function url_decode(s)
    s = s:gsub("+", " ")
    s = s:gsub("%%(%x%x)", function(hex)
        return string.char(tonumber(hex, 16))
    end)
    return s
end

local function parse_qs(qs)
    local t = {}
    if not qs then return t end
    for k, v in qs:gmatch("([^&=]+)=([^&]*)") do
        if not t[k] then t[k] = url_decode(v) end
    end
    return t
end

-- Exact port of SubFinder's _RE_VEXT strip
local function strip_vext(s)
    -- case-insensitive suffix strip, same extensions as Python _RE_VEXT
    return (s:gsub("%.[Mm][Pp]4$",""):gsub("%.[Mm][Kk][Vv]$","")
             :gsub("%.[Aa][Vv][Ii]$",""):gsub("%.[Mm][Oo][Vv]$","")
             :gsub("%.[Ww][Mm][Vv]$",""):gsub("%.[Tt][Ss]$","")
             :gsub("%.[Mm]4[Vv]$",""):gsub("%.[Ww][Ee][Bb][Mm]$","")
             :gsub("%.[Ff][Ll][Vv]$",""):gsub("%.[Mm]3[Uu]8$","")
             :gsub("%.[Mm][Pp][Dd]$",""))
end

-- Exact port of SubFinder's _score_url_segment(seg)
-- Python: strip vext → UUID/hash → generic → sc=1 + SxEx+10 + year+5 + len>=5+2 - pure-digit-3
local function score_segment(seg)
    if not seg or seg == "" then return -1 end
    local s = strip_vext(seg)
    if s == "" then return -1 end
    -- UUID: 8-4-4-4-12 hex
    if s:match("^[0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F]%"
             .."-[0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F]%"
             .."-[0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F]%"
             .."-[0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F]%"
             .."-[0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F]$") then
        return -1
    end
    -- hex hash: 16+ pure hex chars
    if #s >= 16 and s:match("^[0-9a-fA-F]+$") then return -1 end
    -- generic segment names (exact Python _RE_GENERIC list)
    local lower = s:lower()
    local generic = {
        index=1,play=1,watch=1,stream=1,video=1,episode=1,
        media=1,content=1,file=1,files=1,download=1,hls=1,
        dash=1,manifest=1,chunk=1,seg=1,playlist=1,master=1,
        cdn=1,static=1,assets=1,dld=1,
    }
    if generic[lower] then return 0 end
    if lower:match("^v%d+$") then return 0 end  -- v1, v2, v123 etc.
    local sc = 1
    -- +10 for SxxExx (exact _RE_SXEX: optional separator between S and E)
    if s:match("[Ss]%d%d?[%.%-%_ ]?[Ee][Pp]?%d%d?") then sc = sc + 10 end
    -- +5 for year (19xx or 20xx) — Python _RE_YEAR
    if s:match("(^|[%.%-%_ %(])(19%d%d|20%d%d)([%.%-%_ %)]|$)") or
       s:match("^(19%d%d|20%d%d)$") then sc = sc + 5 end
    -- +2 for length >= 5
    if #s >= 5 then sc = sc + 2 end
    -- -3 for pure digits
    if s:match("^%d+$") then sc = sc - 3 end
    return sc
end

-- Exact port of SubFinder's _RE_TAGS regex as a Lua function.
-- Python regex: [.\-\_\s](BluRay|BRRip|...|STEPonee)([.\-\_\s].*)?$  case-insensitive
-- Cuts the string at the first separator + tag word, same as Python's sub("", name).
local function strip_tags(s)
    -- All tokens from Python _RE_TAGS, lowercased. Dot-variants handled below.
    local tags = {
        "bluray","brrip","bdrip","webrip","webdl","web%-dl","web%.dl",
        "hdtv","dvdrip","hdrip","remux","bdremux","imax",
        "2160p","1080p","720p","480p","4k","uhd",
        "x264","x265","hevc","avc","h%.264","h%.265","h264","h265","xvid","divx",
        "hdr10","hdr","sdr","dovi","dolby%.vision",
        "aac","ac3","dts","mp3","dd5","truehd","atmos",
        "repack","proper","extended","theatrical","unrated","dc",
        "nf","amzn","hulu","dsnp","atvp","max","pcok",
        "yts","yify","rarbg","fgt","galaxyrg","sparks","mvo","steponee",
    }
    -- Find the earliest separator+tag position in the string
    local earliest = nil
    for _, tag in ipairs(tags) do
        -- Match [.\-_\s] + tag (case-insensitive via lower comparison)
        local pat = "[%.%-%_%s]" .. tag .. "([%.%-%_%s].*)?$"
        local pos = s:lower():find(pat)
        if pos and (earliest == nil or pos < earliest) then
            earliest = pos
        end
    end
    if earliest then
        return trim(s:sub(1, earliest - 1))
    end
    return s
end

local function looks_like_filename(s)
    if not s or s == "" then return false end
    if not s:match("%a") then return false end
    if #s >= 32 and s:match("^[0-9a-fA-F]+$") then return false end
    if #s >= 20 and not s:match("[%s%.]") then
        local b64_chars = s:gsub("[A-Za-z0-9+/=]", "")
        local ratio = 1 - (#b64_chars / #s)
        if ratio >= 0.80 then return false end
    end
    return true
end

-- SE pattern: exact port of Python _RE_SE_INLINE = _RE_SE_PATTERNS[0]
-- r"[Ss](\d{1,2})[.\-_ ]?[Ee][Pp]?(\d{1,2})(?!\d)"
-- Returns start_pos, s_num, e_num  or  nil
local function find_sxex(name)
    -- Allow optional single separator char between S-part and E-part
    local pat = "()[Ss](%d%d?)[%.%-%_ ]?[Ee][Pp]?(%d%d?)()"
    local pos, s_num, e_num, after = name:match(pat)
    if not pos then return nil end
    -- (?!\d) — next char after the match must not be a digit
    local next_char = name:sub(after, after)
    if next_char:match("%d") then return nil end
    return pos, s_num, e_num
end

-- Mirrors SubFinder's clean_filename() exactly
local function clean_path(raw)
    if not raw or raw == "" then return "" end
    local name = ""
    local is_yt = is_youtube(raw)

    if is_url(raw) then
        local scheme_end = raw:find("://")
        local rest = scheme_end and raw:sub(scheme_end + 3) or raw
        local host_path, qs = rest:match("^([^?#]*)%??(.-)$")
        host_path = host_path or rest
        qs = qs or ""

        -- 1. Query param extraction (skipped for YouTube)
        if not is_yt then
            local params = parse_qs(qs)
            for _, key in ipairs({"filename","file","name","title","video"}) do
                local v = params[key]
                if v and v ~= "" then
                    name = v; break
                end
            end
        end

        -- 2. Path segment scoring (exact Python logic)
        if name == "" then
            local path_part = host_path:match("/(.*)$") or ""
            local segs = {}
            for seg in path_part:gmatch("[^/]+") do
                table.insert(segs, url_decode(seg))
            end
            -- Find highest-scored segment (Python uses sorted(..., reverse=True)[0])
            local best_seg, best_score, best_idx = "", -999, 0
            for i, seg in ipairs(segs) do
                local sc = score_segment(seg)
                if sc > best_score then
                    best_score, best_seg, best_idx = sc, seg, i
                end
            end
            if best_score >= 1 then
                if best_seg:match("[Ss]%d%d?[%.%-%_ ]?[Ee][Pp]?%d%d?") and best_idx > 1 then
                    -- Look backwards for a show-name prefix segment (Python reversed loop)
                    local found_prefix = false
                    for pi = best_idx - 1, 1, -1 do
                        local p = strip_vext(segs[pi])
                        local p_lower = p:lower()
                        local is_uuid = p:match("^[0-9a-fA-F%-]+$") and #p >= 32
                        local is_hash = #p >= 16 and p:match("^[0-9a-fA-F]+$")
                        local is_generic = ({index=1,play=1,watch=1,stream=1,video=1,
                            episode=1,media=1,content=1,file=1,files=1,download=1,
                            hls=1,dash=1,manifest=1,chunk=1,seg=1,playlist=1,
                            master=1,cdn=1,static=1,assets=1,dld=1})[p_lower]
                        local has_sxex = p:match("[Ss]%d%d?[%.%-%_ ]?[Ee][Pp]?%d%d?")
                        if p ~= "" and not is_uuid and not is_hash and not is_generic
                                and not has_sxex and #p >= 3 then
                            name = p .. " " .. best_seg
                            found_prefix = true
                            break
                        end
                    end
                    if not found_prefix then name = best_seg end
                else
                    name = best_seg
                end
            end
        end

        -- 3. Last-resort: unquote the full raw URL (Python: if not name and not _is_yt)
        if name == "" and not is_yt then
            name = url_decode(raw)
        end

        name = strip_vext(name)
    else
        -- Local file: Path(raw).stem equivalent
        local basename = raw:match("([^/\\]+)$") or raw
        name = basename:match("^(.+)%.[^%.]+$") or basename
    end

    if name == "" then return "" end

    -- SE formatting (exact Python _RE_SE_INLINE + _RE_TAGS logic)
    local se_pos, s_num, e_num = find_sxex(name)
    local nc = strip_tags(name)
    if se_pos then
        local tp = trim(name:sub(1, se_pos - 1):gsub("[%._%- ]+$", ""))
        tp = tp:gsub("[%._%-]+", " ")
        tp = trim(tp)
        local ep = string.format("S%02dE%02d", tonumber(s_num), tonumber(e_num))
        return trim(tp .. " " .. ep)
    end
    nc = nc:gsub("%[.-%]", "")
    nc = nc:gsub("%((%d%d%d%d)%)", "\0YEAR\0%1\0")
    nc = nc:gsub("%([^%)]+%)", "")
    nc = nc:gsub("\0YEAR\0(%d%d%d%d)\0", "(%1)")
    nc = nc:gsub("[%._%-]+", " ")
    nc = nc:gsub("%s%s+", " ")
    return trim(nc)
end

-- Mirrors SubFinder's clean_title() exactly
local function clean_media_title(raw)
    if not raw or raw == "" then return "" end
    local name = trim(raw)
    if is_url(name) then return "" end

    local se_pos, s_num, e_num = find_sxex(name)
    local nc = strip_tags(name)
    -- Drop " - Subtitle" suffixes and trailing " -"
    nc = nc:gsub("%s+%-%s+%S.*$", "")
    nc = nc:gsub("%s+%-$", "")
    if se_pos then
        local tp = trim(name:sub(1, se_pos - 1):gsub("[%._%- ]+$", ""))
        tp = tp:gsub("[%._%-]+", " ")
        tp = trim(tp)
        local ep = string.format("S%02dE%02d", tonumber(s_num), tonumber(e_num))
        return trim(tp .. " " .. ep)
    end
    nc = nc:gsub("%[.-%]", "")
    nc = nc:gsub("%((%d%d%d%d)%)", "\0YEAR\0%1\0")
    nc = nc:gsub("%([^%)]+%)", "")
    nc = nc:gsub("\0YEAR\0(%d%d%d%d)\0", "(%1)")
    -- Python: re.sub(r"(?<=\w)[._](?=\w)", " ", nc) — dot/underscore between word chars
    nc = nc:gsub("(%w)[%._](%w)", "%1 %2")
    nc = nc:gsub("%s%s+", " ")
    return trim(nc)
end

-- ── Content-Disposition filename extractor ───────────────────────────────────
-- Mirrors SubFinder's get_filename_from_headers() + clean_filename() pipeline.
-- Parses both plain filename= and RFC 5987 filename*=UTF-8''... forms.

local function parse_content_disposition(cd_header)
    if not cd_header or cd_header == "" then return "" end
    -- RFC 5987 extended form first: filename*=UTF-8''url-encoded-name
    local name = cd_header:match("[Ff]ilename%*%s*=%s*[Uu][Tt][Ff]%-8''([^;%s\"']+)")
    if name then
        return url_decode(name:match("^[\"']?(.-)[\"']?$"))
    end
    -- Plain form: filename="name" or filename=name
    name = cd_header:match('[Ff]ilename%s*=%s*"([^"]+)"')
    if not name then
        name = cd_header:match("[Ff]ilename%s*=%s*'([^']+)'")
    end
    if not name then
        name = cd_header:match("[Ff]ilename%s*=%s*([^;%s\"']+)")
    end
    if name then
        return url_decode(trim(name))
    end
    return ""
end

-- ── Cache folder resolution ───────────────────────────────────────────────────

local function get_cache_dir()
    local appdata = os.getenv("APPDATA") or ""
    if appdata == "" then return nil end
    -- Try known Windows mpv script locations in order
    local candidates = {
        appdata .. "\\mpv.net\\scripts\\SubFinder\\cache",
        appdata .. "\\mpv\\scripts\\SubFinder\\cache",
        appdata .. "\\mpv\\scripts\\SubFinder\\cache",
    }
    for _, dir in ipairs(candidates) do
        local f = io.open(dir .. "\\last_session.json", "r")
        if f then f:close(); return dir end
        -- Also accept if cd_cache.json exists there
        f = io.open(dir .. "\\cd_cache.json", "r")
        if f then f:close(); return dir end
    end
    -- Return the first candidate as the default for writing
    return candidates[1]
end

-- ── cd_cache.json reader/writer ───────────────────────────────────────────────
-- SubFinder keys cd_cache.json by a "content key" = clean_filename(url).lower()
-- For opaque CDN URLs (all blobs, no recognisable segments) the raw URL is used
-- as key — so we try both.

local function norm_content_key(video_path)
    -- Best-effort: try clean_path, fall back to raw URL (truncated)
    local k = clean_path(video_path)
    if k and k ~= "" then
        return k:lower()
    end
    return video_path:sub(1, 512)
end

local function read_cd_cache(video_path)
    if opts.use_cd_cache ~= "yes" then return nil end
    local cache_dir = get_cache_dir()
    if not cache_dir then return nil end

    local f = io.open(cache_dir .. "\\cd_cache.json", "r")
    if not f then return nil end
    local raw = f:read("*a")
    f:close()
    if not raw or raw == "" then return nil end

    -- Try content key first, then raw URL
    local ck = norm_content_key(video_path)
    -- Simple JSON string lookup: find "key":"value"
    local function find_val(key)
        -- Escape special pattern chars in the key
        local escaped = key:gsub('([%.%+%-%*%?%[%]%^%$%(%)%%])', '%%%1')
        local v = raw:match('"' .. escaped .. '"%s*:%s*"(.-[^\\])"')
        if v then return (v:gsub('\\"', '"')) end
        if raw:match('"' .. escaped .. '"%s*:%s*""') then return "" end
        return nil
    end

    local v = find_val(ck)
    if v and v ~= "" then return v end
    -- Also try raw URL as key (SubFinder falls back to this for opaque URLs)
    v = find_val(video_path:sub(1, 512))
    if v and v ~= "" then return v end
    return nil
end

local function write_cd_cache(video_path, filename)
    local cache_dir = get_cache_dir()
    if not cache_dir then return end

    local path = cache_dir .. "\\cd_cache.json"
    local data = {}

    -- Read existing entries
    local f = io.open(path, "r")
    if f then
        local raw = f:read("*a")
        f:close()
        -- Parse all "key":"value" pairs from the flat JSON object
        for k, v in raw:gmatch('"(.-[^\\])"%s*:%s*"(.-[^\\])"') do
            data[k] = v
        end
    end

    -- Add new entry under the content key
    local ck = norm_content_key(video_path)
    data[ck] = filename

    -- Serialise back to JSON (simple flat object, no nesting needed)
    local parts = {"{"}
    local first = true
    for k, v in pairs(data) do
        if not first then parts[#parts+1] = "," end
        -- Escape quotes in key/value
        k = k:gsub('"', '\\"')
        v = v:gsub('"', '\\"')
        parts[#parts+1] = string.format('  "%s": "%s"', k, v)
        first = false
    end
    parts[#parts+1] = "}"
    local json_str = table.concat(parts, "\n")

    -- Atomic write via .tmp + rename (mirrors SubFinder's pattern)
    local tmp = path .. ".tmp"
    local fw = io.open(tmp, "w")
    if not fw then return end
    fw:write(json_str)
    fw:close()
    os.rename(tmp, path)
end

-- ── HEAD request via PowerShell (Windows async subprocess) ───────────────────
-- Fires a non-blocking mp.command_native_async subprocess call.
-- On success, parses Content-Disposition, cleans it, updates the title,
-- and persists the result to cd_cache.json for future instant lookups.

local function fetch_content_disposition_async(video_path, on_result)
    if opts.use_head_request ~= "yes" then
        on_result(nil)
        return
    end

    -- PowerShell one-liner: HEAD request, print Content-Disposition header value only.
    -- Uses [System.Net.HttpWebRequest] for compatibility with PS 2–5 and PS 6+.
    -- Timeout = 8 s.  Outputs only the header value (or empty string on failure).
    local ps_script = string.format([[
$url = '%s'
try {
    $req = [System.Net.HttpWebRequest]::Create($url)
    $req.Method = 'HEAD'
    $req.Timeout = 8000
    $req.UserAgent = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
    $req.AllowAutoRedirect = $true
    $res = $req.GetResponse()
    $cd = $res.Headers['Content-Disposition']
    $res.Close()
    if ($cd) { Write-Output $cd } else { Write-Output '' }
} catch { Write-Output '' }
]], video_path:gsub("'", "''"))  -- escape single quotes for PS

    mp.command_native_async({
        name = "subprocess",
        args = {
            "powershell",
            "-NoProfile",
            "-NonInteractive",
            "-WindowStyle", "Hidden",
            "-Command", ps_script,
        },
        capture_stdout = true,
        capture_stderr = false,
        playback_only  = false,
    }, function(success, result, _error)
        if not success or not result then
            on_result(nil)
            return
        end
        local cd_value = trim(result.stdout or "")
        if cd_value == "" then
            on_result(nil)
            return
        end
        local filename = parse_content_disposition(cd_value)
        on_result(filename ~= "" and filename or nil)
    end)
end

-- ── session cache reader ──────────────────────────────────────────────────────

local function json_unescape(s)
    return (s:gsub('\\"', '"')
              :gsub('\\\\', '\1')
              :gsub('\\/', '/')
              :gsub('\\n', '\n')
              :gsub('\\r', '')
              :gsub('\\t', '\t')
              :gsub('\1', '\\'))
end

local function json_get_str(snippet, key)
    local v = snippet:match('"' .. key .. '"%s*:%s*"(.-[^\\])"')
    if v then return json_unescape(v) end
    if snippet:match('"' .. key .. '"%s*:%s*""') then return "" end
    return nil
end

local function norm_path(p)
    return (p or ""):lower():gsub("\\", "/"):gsub("//+", "/"):gsub("/$", "")
end

local function read_session_cache(video_path)
    if opts.use_session_cache ~= "yes" then return nil end

    local cache_dir = get_cache_dir()
    if not cache_dir then return nil end

    local f = io.open(cache_dir .. "\\last_session.json", "r")
    if not f then return nil end
    local raw = f:read("*a")
    f:close()
    if not raw or raw == "" then return nil end

    local target = norm_path(video_path)
    local pos = 1

    while true do
        local vp_pos = raw:find('"video_path"', pos)
        if not vp_pos then break end

        local win_start = math.max(1, vp_pos - 3000)
        local win_end   = math.min(#raw, vp_pos + 4000)
        local window    = raw:sub(win_start, win_end)

        local local_vp = window:find('"video_path"', vp_pos - win_start + 1)
        if local_vp then
            local vp_snip = window:sub(local_vp, local_vp + 2048)
            local vp_val  = json_get_str(vp_snip, "video_path") or ""

            if norm_path(vp_val) == target then
                local q = json_get_str(window, "query")
                if q and trim(q) ~= "" then
                    return trim(q)
                end
            end
        end

        pos = vp_pos + 1
    end

    return nil
end

-- ── apply title ───────────────────────────────────────────────────────────────

-- Detect the player suffix once at startup so we can reconstruct the window
-- title correctly.  Some mpv builds/forks append a suffix like "mpv" or a
-- fork name after " - "; others use no suffix at all.
-- We read the raw title property before any file loads to capture the suffix.
local _title_suffix = ""
do
    local raw = mp.get_property("title") or ""
    -- The suffix is everything after the last " - " in the initial idle title.
    -- If nothing is set yet, default to "mpv".
    local s = raw:match(" %- ([^%-]+)%s*$")
    _title_suffix = s and trim(s) or "mpv"
end

local function apply_title(title, source)
    if title and trim(title) ~= "" then
        -- force-media-title: controls OSD / bottom bar display name
        mp.set_property("force-media-title", title)
        -- title: directly sets the OS window title bar string.
        -- Some builds/forks render their own window title from a template that may have
        -- been frozen at the raw URL before our script ran — overwrite it now.
        mp.set_property("title", title)
        mp.msg.info("subfinder_title: [" .. source .. "] → " .. title)
        return true
    end
    return false
end

-- Poll media-title until mpv resolves something real, then clean and apply.
local function poll_media_title(raw_path, attempts_left, interval_ms)
    mp.add_timeout(interval_ms / 1000, function()
        local mt = mp.get_property("media-title") or ""
        if mt ~= "" and mt ~= raw_path and not is_url(mt) then
            local cleaned = clean_media_title(mt)
            if apply_title(cleaned, "poll") then return end
        end
        if attempts_left > 1 then
            poll_media_title(raw_path, attempts_left - 1, interval_ms)
        else
            mp.msg.debug("subfinder_title: polling exhausted, giving up")
        end
    end)
end

-- ── main ─────────────────────────────────────────────────────────────────────

mp.register_event("file-loaded", function()
    local path = mp.get_property("path")
    if not path or path == "" then return end
    if opts.skip_youtube == "yes" and is_youtube(path) then return end

    -- 1. Session cache (best: exact match to what SubFinder resolved)
    if apply_title(read_session_cache(path), "session cache") then return end

    -- 2. cd_cache.json — Content-Disposition cached by SubFinder or a prior
    --    run of this script
    local cd_cached = read_cd_cache(path)
    if cd_cached and cd_cached ~= "" then
        local cleaned = clean_path(cd_cached) ~= "" and clean_path(cd_cached)
                        or clean_media_title(cd_cached)
        if apply_title(cleaned ~= "" and cleaned or cd_cached, "cd_cache") then
            return
        end
    end

    -- 3. Try URL heuristic immediately (free / instant)
    local heuristic = is_url(path) and clean_path(path) or nil
    -- (applied only as fallback after async step)

    -- For local files: filename is definitive
    if not is_url(path) then
        if apply_title(clean_path(path), "clean_path") then return end
        local mt = mp.get_property("media-title") or ""
        if mt ~= "" and mt ~= path and not is_url(mt) then
            apply_title(clean_media_title(mt), "media-title")
        end
        return
    end

    -- 4. Async HEAD request to get Content-Disposition (for URLs only)
    --    This is the key step SubFinder uses for opaque CDN URLs.
    fetch_content_disposition_async(path, function(cd_filename)
        if cd_filename and cd_filename ~= "" then
            -- Clean it the same way SubFinder does
            local cleaned = clean_path(cd_filename) ~= "" and clean_path(cd_filename)
                            or clean_media_title(cd_filename)
                            or cd_filename
            if apply_title(cleaned, "Content-Disposition") then
                -- Persist to cd_cache.json so next load is instant
                write_cd_cache(path, cd_filename)
                return
            end
        end

        -- 5. URL path heuristic fallback
        if apply_title(heuristic, "clean_path") then return end

        -- 6. Current media-title
        local mt = mp.get_property("media-title") or ""
        if mt ~= "" and mt ~= path and not is_url(mt) then
            if apply_title(clean_media_title(mt), "media-title") then return end
        end

        -- 7. Opaque URL: poll media-title for up to 5s
        mp.msg.debug("subfinder_title: no title resolved yet, polling media-title")
        poll_media_title(path, 10, 500)
    end)

    -- While the HEAD request is in-flight, apply the heuristic immediately
    -- so the title isn't blank. The async callback will overwrite it if
    -- Content-Disposition gives something better.
    if heuristic and heuristic ~= "" then
        apply_title(heuristic, "clean_path (interim)")
    end
end)

-- CheraxDoom.lua
-- A WAD file reader, map-geometry parser and flat-shaded BSP renderer for
-- DOOM / DOOM2 style .wad files, built to run inside the Cherax Lua overlay.
-- PHASE 1 loads a .wad from disk as raw bytes (via FileMgr), parses the 12-byte
-- header and the lump directory, and decodes a level's geometry lumps
-- (VERTEXES, LINEDEFS, SIDEDEFS, SECTORS, THINGS, and when present SEGS,
-- SSECTORS, NODES) into plain Lua tables. PHASE 2 sits on top of that data
-- layer: a BSP front-to-back wall renderer (flat-shaded, no textures) with
-- player spawn from the THING type-1 start, floor-follow, and radius-based
-- free-walk collision. All of it draws inside one fullscreen overlay window.
--
-- Everything lives on the single upvalue table W so the main chunk stays well
-- under Lua's 200 local limit and so a second script cannot collide with it.
-- Binary parsing uses string.unpack with little-endian ('<') formats. All WAD
-- indices are 0-based as stored on disk; add 1 when indexing a Lua array. The
-- value 0xFFFF (65535) is the "no sidedef" sentinel; the 0x8000 bit on a node
-- child marks a subsector reference.

local W = {}
local FEATURE_HASH = (Utils and Utils.Joaat) and Utils.Joaat("LUA_DoomWad_MainToggle") or 0
-- Host-launch mode: the host script (bladscript) prepends a `BladscriptLoaded=true`
-- line ahead of this chunk before ExecuteScript'ing it. In that mode we auto-run
-- (no manual toggle), fetch the shareware IWAD on the first frame, and register a
-- hidden shutdown feature the host can OnClick() from the shared registry to
-- unload us. Run standalone the global is nil and none of this engages: the user
-- enables the DOOM WAD toggle by hand and supplies their own .wad.
local BLAD_MODE = rawget(_G, "BladscriptLoaded") == true
local SHUTDOWN_HASH = (Utils and Utils.Joaat) and Utils.Joaat("CheraxDoom_Shutdown") or 0
local WAD_URL = "https://raw.githubusercontent.com/nneonneo/universal-doom/main/DOOM1.WAD"
-- The only file the downloader will ever accept: DOOM1.WAD shareware 1.9
-- (canonical release, MD5 f0cefca49926d00903cf57551d901abe). Both download
-- sources serve this byte-identical file. One of them is plain HTTP (see
-- ensureWadDownload for why it must stay), so the body is unauthenticated in
-- transit; anything that does not match the exact size AND this SHA-256 -
-- mirror rot, a captive portal, a tampered response - is rejected before it
-- is written to disk or fed to the parser.
local WAD_SIZE = 4196020
local WAD_SHA256 = "1d7d43be501e67d927e415e0b8f3e29c3bf33075e859721816f652a526cac771"
local floor = math.floor

-- math aliases + tiny helpers (file scope; keep the main-chunk local count low)
local ceil, abs, sqrt = math.ceil, math.abs, math.sqrt
local sin, cos, atan, pi = math.sin, math.cos, math.atan, math.pi
local tan = math.tan
local min, max = math.min, math.max
local TWO_PI = pi * 2

local function clamp(v, lo, hi)
    if v < lo then return lo elseif v > hi then return hi else return v end
end
local function ci(v) -- clamp to a color byte 0..255
    v = floor(v + 0.5)
    if v < 0 then return 0 elseif v > 255 then return 255 else return v end
end
local function angNorm(a)
    while a <= -pi do a = a + TWO_PI end
    while a > pi do a = a - TWO_PI end
    return a
end
local function now()
    local ok, t = pcall(ImGui.GetTime)
    return (ok and t) or 0
end
local function kdown(vk)
    local ok, r = pcall(Utils.IsKeyDown, vk)
    return ok and r
end
local function kpressed(vk) -- rising edge, valid only for tracked keys
    return W.curKey[vk] and not W.prevKey[vk]
end
local function rectf(x0, y0, x1, y1, r, g, b, a)
    ImGui.AddRectFilled(x0, y0, x1, y1, ci(r), ci(g), ci(b), a or 255)
end
-- squared distance from point (px,py) to segment (x1,y1)-(x2,y2)
local function segDist2(px, py, x1, y1, x2, y2)
    local vx, vy = x2 - x1, y2 - y1
    local wx, wy = px - x1, py - y1
    local L = vx * vx + vy * vy
    local t = (L > 0) and ((wx * vx + wy * vy) / L) or 0
    if t < 0 then t = 0 elseif t > 1 then t = 1 end
    local cx, cy = x1 + t * vx, y1 + t * vy
    local ex, ey = px - cx, py - cy
    return ex * ex + ey * ey
end

----------------------------------------------------------------------
-- lump-name helpers
----------------------------------------------------------------------
-- A WAD name is an 8-byte field. It is either a full 8 characters with no
-- terminator, or a shorter name NUL-terminated with trailing garbage. Cut at
-- the first NUL and upper-case before any comparison.
local function trimName(raw)
    if type(raw) ~= "string" then return "" end
    local z = string.find(raw, "\0", 1, true)
    if z then raw = string.sub(raw, 1, z - 1) end
    return string.upper(raw)
end

-- Texture-name field: "-" means "no texture" -> nil.
local function texName(raw)
    local nm = trimName(raw)
    if nm == "" or nm == "-" then return nil end
    return nm
end

local NONE = 0xFFFF        -- "no sidedef" sentinel
local SUBSECTOR_BIT = 0x8000

-- Lumps that belong to a map, consumed in directory order after the marker.
W.MAP_LUMPS = {
    THINGS = true, LINEDEFS = true, SIDEDEFS = true, VERTEXES = true,
    SEGS = true, SSECTORS = true, NODES = true, SECTORS = true,
    REJECT = true, BLOCKMAP = true,
}

-- DOOM2 uses MAPxx markers whose music lump name is NOT derivable from the map
-- name (ExMy maps use D_ExMy). This lookup maps each DOOM2 slot to its lump.
W.MUS_DOOM2 = {
    MAP01 = "D_RUNNIN", MAP02 = "D_STALKS", MAP03 = "D_COUNTD", MAP04 = "D_BETWEE",
    MAP05 = "D_DOOM",   MAP06 = "D_THE_DA", MAP07 = "D_SHAWN",  MAP08 = "D_DDTBLU",
    MAP09 = "D_IN_CIT", MAP10 = "D_DEAD",   MAP11 = "D_STLKS2", MAP12 = "D_THEDA2",
    MAP13 = "D_DOOM2",  MAP14 = "D_DDTBL2", MAP15 = "D_RUNNI2", MAP16 = "D_DEAD2",
    MAP17 = "D_STLKS3", MAP18 = "D_ROMERO", MAP19 = "D_SHAWN2", MAP20 = "D_MESSAG",
    MAP21 = "D_COUNT2", MAP22 = "D_DDTBL3", MAP23 = "D_AMPIE",  MAP24 = "D_THEDA3",
    MAP25 = "D_ADRIAN", MAP26 = "D_MESSG2", MAP27 = "D_ROMER2", MAP28 = "D_TENSE",
    MAP29 = "D_SHAWN3", MAP30 = "D_OPENIN", MAP31 = "D_EVIL",   MAP32 = "D_ULTIMA",
}

-- Verbatim DOOM strings (d_englsh.h / dstrings.c) so the front-end prompts read
-- exactly like the game instead of paraphrases. \n = line break.
W.STR = {
    NIGHTMARE  = "are you sure? this skill level\nisn't even remotely fair.\n\npress y or n.",
    DOSY       = "(press y to quit)",
    PD_BLUEK   = "You need a blue key to open this door",
    PD_YELLOWK = "You need a yellow key to open this door",
    PD_REDK    = "You need a red key to open this door",
}
-- Quit taunts (endmsg[], DOOM1 set); one is picked per quit-screen open.
W.QUITMSGS = {
    "are you sure you want to\nquit this great game?",
    "please don't leave, there's more\ndemons to toast!",
    "let's beat it -- this is turning\ninto a bloodbath!",
    "i wouldn't leave if i were you.\ndos is much worse.",
    "you're trying to say you like dos\nbetter than me, right?",
    "don't leave yet -- there's a\ndemon around that corner!",
    "ya know, next time you come in here\ni'm gonna toast ya.",
    "go ahead and leave. see if i care.",
}

----------------------------------------------------------------------
-- SECTION A: WAD container
----------------------------------------------------------------------
function W.reset()
    -- Stop any playing music before dropping wad state (openWad -> reset runs on
    -- every wad change). Guarded: reset can be reached before the audio section
    -- is defined at load, so only call once the function exists.
    if W.stopMusic then W.stopMusic() end
    W.musPlaying = false
    W.musTrack = nil
    W.musStart = 0
    W.musLen = 0
    W.wad = nil
    W.wadId = nil
    W.numLumps = 0
    W.lumps = nil       -- ordered array: { { name=, pos=, size= }, ... }
    W.lumpIndex = nil   -- NAME -> { ordinal, ordinal, ... } (dups are legal)
    W.map = nil
    W.status = ""
    -- Phase-3 graphics state is per-wad: drop it so a new wad reparses cleanly.
    W.gfxTried = false
    W.texturesOk = false
    W.pal = nil         -- [0..255] = {r,g,b} from PLAYPAL palette 0
    W.pnames = nil      -- [0..count-1] = "NAME"
    W.texDefs = nil     -- NAME -> { w=, h=, patches={ {originX,originY,pnameIdx}, } }
    W.flatLump = nil    -- NAME -> ordinal (inside a flats namespace)
    W.patchLump = nil   -- NAME -> ordinal (inside a patches namespace)
    W.spriteLump = nil  -- NAME -> ordinal (inside a sprites namespace)
    W.spriteFrames = nil -- PREFIX -> frame/rotation index (built from spriteLump)
    W.spriteMeta = nil  -- lumpName -> {w,h,xoff,yoff} header cache (or false)
    W.texRGBA = nil     -- KEY -> raw RGBA byte string (composited, cached)
    W.texW = nil        -- KEY -> source width
    W.texH = nil        -- KEY -> source height
    W.texCache = nil    -- KEY -> { id, tex, w, h, state } async GPU load state
    -- The DISK cache is per-wad too: drop the resolved dir + fingerprint so the
    -- next wad recomputes them (stale = it would serve the old wad's baked PNGs).
    W.cacheDir = nil
    W.wadFp = nil
end

-- Return the raw bytes of lump at 1-based ordinal i, bounds-checked. Missing,
-- empty, or out-of-range lumps return "" so no parse ever indexes past the file.
function W.lumpBytes(i)
    if not i then return "" end
    local L = W.lumps and W.lumps[i]
    if not L then return "" end
    local pos, size = L.pos, L.size
    if not size or size <= 0 then return "" end
    if not pos or pos < 0 or pos + size > #W.wad then return "" end
    return string.sub(W.wad, pos + 1, pos + size)
end

-- Parse the 12-byte header + 16-byte directory. Raises on any structural
-- violation; the caller wraps this in pcall.
function W.parseDirectory()
    local data = W.wad
    if #data < 12 then error("file smaller than header", 0) end
    local id, numLumps, dirOfs = string.unpack("<c4i4i4", data, 1)
    if id ~= "IWAD" and id ~= "PWAD" then error("bad wad id '" .. tostring(id) .. "'", 0) end
    if numLumps < 0 then error("negative lump count", 0) end
    if dirOfs < 12 then error("directory offset inside header", 0) end
    if dirOfs + numLumps * 16 > #data then error("directory out of bounds", 0) end

    W.wadId = id
    W.numLumps = numLumps
    W.lumps = {}
    W.lumpIndex = {}
    for k = 0, numLumps - 1 do
        local base = dirOfs + k * 16 + 1
        local pos, size, rawName = string.unpack("<i4i4c8", data, base)
        local nm = trimName(rawName)
        W.lumps[k + 1] = { name = nm, pos = pos, size = size }
        local list = W.lumpIndex[nm]
        if not list then list = {}; W.lumpIndex[nm] = list end
        list[#list + 1] = k + 1
    end
end

-- Fingerprint a wad for the on-disk cache: "<size>-<crc32 hex>" over the header,
-- the whole lump directory, and up to ~64 evenly spaced 256-byte content samples.
-- Cached assets (baked PNGs, converted MIDs/WAVs) are keyed by LUMP NAME, and
-- different wads reuse the same names (DOOM1 vs FreeDoom vs any PWAD), so each
-- wad must get its own cache subdirectory or a wad switch silently serves the
-- previous wad's art and audio. The directory covers name/pos/size of every
-- lump; the sparse content samples additionally catch in-place lump edits that
-- leave the directory byte-identical. Called only after parseDirectory accepted
-- the header, so the unpack and directory slice below are already validated.
function W.wadFingerprint(data)
    W.initCRC()
    local _, numLumps, dirOfs = string.unpack("<c4i4i4", data, 1)
    local parts = { string.sub(data, 1, 12),
                    string.sub(data, dirOfs + 1, dirOfs + numLumps * 16) }
    local n = #data
    local step = floor(n / 64)
    if step < 4096 then step = 4096 end
    local i = 1
    while i <= n do
        parts[#parts + 1] = string.sub(data, i, min(i + 255, n))
        i = i + step
    end
    return string.format("%d-%08x", n, W.crc32(table.concat(parts)))
end

-- Read a file as RAW BYTES. A WAD is binary and full of NUL / 0x1A / CRLF bytes,
-- so it must be read in binary mode. FileMgr.ReadFileContent is text-mode on this
-- build (it truncates/mangles binary), so use io.open(path, "rb") first and only
-- fall back to FileMgr if the Lua io library is unavailable.
function W.readFileBytes(path)
    local ook, f = pcall(io.open, path, "rb")
    if ook and f then
        local rok, data = pcall(f.read, f, "*a")
        pcall(f.close, f)
        if rok and type(data) == "string" and #data > 0 then return data end
    end
    local fok, fdata = pcall(FileMgr.ReadFileContent, path)
    if fok and type(fdata) == "string" then return fdata end
    return nil
end

-- Read a .wad from disk and parse its header + directory. Returns true on
-- success, or false plus an error string. Never throws.
function W.openWad(path)
    W.reset()
    W.wadPath = path
    local data = W.readFileBytes(path)
    if type(data) ~= "string" or #data < 12 then
        W.state = "error"
        W.status = "read failed (binary): " .. tostring(path)
        return false, W.status
    end
    W.wad = data
    local pok, perr = pcall(W.parseDirectory)
    if not pok then
        W.state = "error"
        W.status = "bad wad: " .. tostring(perr)
        W.wad = nil
        return false, W.status
    end
    local fok, fp = pcall(W.wadFingerprint, data)
    W.wadFp = (fok and fp) or nil       -- selects this wad's cache subdirectory
    W.state = "ready"
    W.status = string.format("%s: %d lumps, %d maps", W.wadId, #W.lumps, #W.listMaps())
    pcall(W.loadGraphics)   -- best-effort palette/pnames/texture defs (Phase 3)
    return true
end

-- Names of every map marker (ExMy or MAPxx) present, in directory order.
function W.listMaps()
    local out = {}
    if not W.lumps then return out end
    for _, L in ipairs(W.lumps) do
        local nm = L.name
        if nm:match("^E%dM%d$") or nm:match("^MAP%d%d$") then
            out[#out + 1] = nm
        end
    end
    return out
end

-- 1-based ordinal of the marker lump for a map name, or nil.
function W.findMap(name)
    if not W.lumps then return nil end
    name = trimName(name)
    for i, L in ipairs(W.lumps) do
        if L.name == name then return i end
    end
    return nil
end

----------------------------------------------------------------------
-- SECTION B: map geometry lump parsers
-- Each: count = #bytes // recSize (only whole records read, so unpack can never
-- run off the end); record j (0-based) starts at Lua position j*recSize + 1.
----------------------------------------------------------------------
function W.parseVertexes(bytes)
    local out, rec = {}, 4
    local n = floor(#bytes / rec)
    for j = 0, n - 1 do
        local x, y = string.unpack("<i2i2", bytes, j * rec + 1)
        out[j + 1] = { x = x, y = y }
    end
    return out
end

function W.parseLinedefs(bytes)
    local out, rec = {}, 14
    local n = floor(#bytes / rec)
    for j = 0, n - 1 do
        local v1, v2, flags, special, tag, front, back =
            string.unpack("<I2I2I2I2I2I2I2", bytes, j * rec + 1)
        out[j + 1] = { v1 = v1, v2 = v2, flags = flags, special = special,
            tag = tag, front = front, back = back }
    end
    return out
end

function W.parseSidedefs(bytes)
    local out, rec = {}, 30
    local n = floor(#bytes / rec)
    for j = 0, n - 1 do
        local xoff, yoff, upper, lower, mid, sector =
            string.unpack("<i2i2c8c8c8I2", bytes, j * rec + 1)
        out[j + 1] = { xoff = xoff, yoff = yoff, upper = texName(upper),
            lower = texName(lower), mid = texName(mid), sector = sector }
    end
    return out
end

function W.parseSectors(bytes)
    local out, rec = {}, 26
    local n = floor(#bytes / rec)
    for j = 0, n - 1 do
        local fh, ch, ft, ct, light, special, tag =
            string.unpack("<i2i2c8c8i2I2I2", bytes, j * rec + 1)
        out[j + 1] = { floor = fh, ceil = ch, floorTex = texName(ft),
            ceilTex = texName(ct), light = light, special = special, tag = tag }
    end
    return out
end

function W.parseThings(bytes)
    local out, rec = {}, 10
    local n = floor(#bytes / rec)
    for j = 0, n - 1 do
        local x, y, angle, dtype, flags = string.unpack("<i2i2I2I2I2", bytes, j * rec + 1)
        out[j + 1] = { x = x, y = y, angle = angle, dtype = dtype, flags = flags }
    end
    return out
end

function W.parseSegs(bytes)
    local out, rec = {}, 12
    local n = floor(#bytes / rec)
    for j = 0, n - 1 do
        local v1, v2, angle, linedef, dir, offset =
            string.unpack("<I2I2i2I2i2i2", bytes, j * rec + 1)
        out[j + 1] = { v1 = v1, v2 = v2, angle = angle, linedef = linedef,
            dir = dir, offset = offset }
    end
    return out
end

function W.parseSsectors(bytes)
    local out, rec = {}, 4
    local n = floor(#bytes / rec)
    for j = 0, n - 1 do
        local segCount, firstSeg = string.unpack("<I2I2", bytes, j * rec + 1)
        out[j + 1] = { segCount = segCount, firstSeg = firstSeg }
    end
    return out
end

function W.parseNodes(bytes)
    local out, rec = {}, 28
    local n = floor(#bytes / rec)
    for j = 0, n - 1 do
        local x, y, dx, dy, rt, rb, rl, rr, lt, lb, ll, lr, rchild, lchild =
            string.unpack("<i2i2i2i2i2i2i2i2i2i2i2i2I2I2", bytes, j * rec + 1)
        out[j + 1] = { x = x, y = y, dx = dx, dy = dy,
            rbox = { top = rt, bottom = rb, left = rl, right = rr },
            lbox = { top = lt, bottom = lb, left = ll, right = lr },
            rchild = rchild, lchild = lchild }
    end
    return out
end

-- Resolve each seg's front/back sector once, at load time, so the per-frame
-- path does no indirection. A seg points at a linedef and a side (dir): dir 0
-- uses the linedef's front (right) sidedef as the seg front, dir 1 uses the
-- back (left) sidedef. backSector stays nil for a one-sided line (solid wall).
function W.resolveSegSectors(map)
    local lds, sds = map.linedefs, map.sidedefs
    for _, seg in ipairs(map.segs) do
        local ld = lds[seg.linedef + 1]
        if ld then
            local fSide, bSide
            if seg.dir == 0 then fSide, bSide = ld.front, ld.back
            else fSide, bSide = ld.back, ld.front end
            if fSide and fSide ~= NONE then
                local sd = sds[fSide + 1]
                if sd then seg.frontSector = sd.sector end
            end
            if bSide and bSide ~= NONE then
                local sd = sds[bSide + 1]
                if sd then seg.backSector = sd.sector end
            end
        end
    end
end

-- Decode a node child reference. Returns "subsector"|"node", index (0-based).
function W.decodeChild(ref)
    if (ref & SUBSECTOR_BIT) ~= 0 then
        return "subsector", (ref & (SUBSECTOR_BIT - 1))
    end
    return "node", ref
end

-- Locate the marker, walk the ORDERED lumps that follow it (stopping at the
-- first non-map lump), grab the geometry sub-lumps from within that run only,
-- and parse them. Returns a map table, or nil plus an error string.
function W.loadMap(name)
    local m = W.findMap(name)
    if not m then
        W.status = "map not found: " .. tostring(name)
        return nil, W.status
    end
    local realName = W.lumps[m].name

    -- collect the sub-lumps that belong to this map, in directory order
    local sub, hexen = {}, false
    local i = m + 1
    while i <= #W.lumps do
        local nm = W.lumps[i].name
        if W.MAP_LUMPS[nm] then
            if not sub[nm] then sub[nm] = i end
            i = i + 1
        elseif nm == "BEHAVIOR" then
            hexen = true          -- Hexen-format map, not supported
            break
        else
            break
        end
    end
    if hexen then
        W.status = realName .. ": Hexen-format map not supported"
        return nil, W.status
    end

    local map = { name = realName }
    local ok, err = pcall(function()
        map.vertexes = W.parseVertexes(W.lumpBytes(sub.VERTEXES))
        map.sectors  = W.parseSectors(W.lumpBytes(sub.SECTORS))
        map.sidedefs = W.parseSidedefs(W.lumpBytes(sub.SIDEDEFS))
        map.linedefs = W.parseLinedefs(W.lumpBytes(sub.LINEDEFS))
        map.things   = W.parseThings(W.lumpBytes(sub.THINGS))
        map.segs     = W.parseSegs(W.lumpBytes(sub.SEGS))
        map.ssectors = W.parseSsectors(W.lumpBytes(sub.SSECTORS))
        map.nodes    = W.parseNodes(W.lumpBytes(sub.NODES))
        W.resolveSegSectors(map)
        if #map.nodes > 0 then
            map.rootNode = #map.nodes - 1               -- last node = BSP root
        elseif #map.ssectors > 0 then
            map.rootNode = SUBSECTOR_BIT                 -- single-subsector map
        else
            map.rootNode = nil
        end
    end)
    if not ok then
        W.state = "error"
        W.status = realName .. ": parse error: " .. tostring(err)
        return nil, W.status
    end

    -- Sky pre-compute: whether any sector uses the F_SKY1 pseudo-flat (so the
    -- sky backdrop is drawn) and which sky wall-texture this map wants.
    map.usesSky = false
    for _, s in ipairs(map.sectors) do
        if s.ceilTex == "F_SKY1" then map.usesSky = true; break end
    end
    map.skyName = W.skyTexName(realName)

    W.map = map
    W.status = string.format(
        "%s: v=%d ld=%d sd=%d sec=%d th=%d seg=%d ss=%d nd=%d",
        realName, #map.vertexes, #map.linedefs, #map.sidedefs, #map.sectors,
        #map.things, #map.segs, #map.ssectors, #map.nodes)
    return map
end

----------------------------------------------------------------------
-- SECTION C: graphics lump parsers (palette, patch names, texture defs,
-- marker-namespaced flats/patches, and the picture/patch column format).
-- Every body is best-effort: a malformed graphics lump degrades to "no
-- textures" (renderer stays on the Phase-2 flat strips), never a hard abort.
----------------------------------------------------------------------
-- Scan the directory ONCE, tracking the flats and patches marker namespaces,
-- so a flat/patch is located by name only within its own namespace (with a
-- global fallback for malformed PWADs). Markers have size 0; skip them.
function W.scanNamespaces()
    W.flatLump = {}
    W.patchLump = {}
    W.spriteLump = {}
    if not W.lumps then return end
    local inFlats, inPatches, inSprites = false, false, false
    for ord, L in ipairs(W.lumps) do
        local nm = L.name
        if nm == "F_START" or nm == "FF_START" or nm == "F1_START" or nm == "F2_START" then
            inFlats = true
        elseif nm == "F_END" or nm == "FF_END" or nm == "F1_END" or nm == "F2_END" then
            inFlats = false
        elseif nm == "P_START" or nm == "PP_START" or nm == "P1_START"
            or nm == "P2_START" or nm == "P3_START" then
            inPatches = true
        elseif nm == "P_END" or nm == "PP_END" or nm == "P1_END"
            or nm == "P2_END" or nm == "P3_END" then
            inPatches = false
        elseif nm == "S_START" or nm == "SS_START" then
            inSprites = true
        elseif nm == "S_END" or nm == "SS_END" then
            inSprites = false
        elseif L.size and L.size > 0 then
            if inFlats and not W.flatLump[nm] then W.flatLump[nm] = ord end
            if inPatches and not W.patchLump[nm] then W.patchLump[nm] = ord end
            if inSprites and not W.spriteLump[nm] then W.spriteLump[nm] = ord end
        end
    end
end

-- PLAYPAL palette 0 -> W.pal[0..255] = {r,g,b}. Requires >= 768 bytes.
function W.loadPalette()
    W.pal = nil
    local li = W.lumpIndex and W.lumpIndex.PLAYPAL
    local p = W.lumpBytes(li and li[1])
    if #p < 768 then return end
    local pal = {}
    for i = 0, 255 do
        local r, g, b = string.unpack("<BBB", p, i * 3 + 1)
        pal[i] = { r, g, b }
    end
    W.pal = pal
end

-- PNAMES -> W.pnames[0..count-1] = "NAME" (patch lump keys, uppercased).
function W.loadPnames()
    W.pnames = {}
    local li = W.lumpIndex and W.lumpIndex.PNAMES
    local p = W.lumpBytes(li and li[1])
    if #p < 4 then return end
    local n = string.unpack("<i4", p, 1)
    if n < 0 or 4 + n * 8 > #p then return end
    for i = 0, n - 1 do
        local nm = string.unpack("<c8", p, 4 + i * 8 + 1)
        W.pnames[i] = trimName(nm)
    end
end

-- One TEXTUREx lump -> merge maptexture_t defs into W.texDefs. The
-- maptexture_t header is 22 bytes (masked is int32, not int16).
function W.parseTextureLump(lname)
    local li = W.lumpIndex and W.lumpIndex[lname]
    local p = W.lumpBytes(li and li[1])
    if #p < 4 then return end
    local nt = string.unpack("<i4", p, 1)
    if nt < 0 or 4 + nt * 4 > #p then return end
    for k = 0, nt - 1 do
        local ofs = string.unpack("<i4", p, 4 + k * 4 + 1)
        if ofs > 0 and ofs + 22 <= #p then
            -- name(c8) masked(i4) width(i2) height(i2) columndir(i4) patchcount(i2)
            local name, _, w, h, _2, pc = string.unpack("<c8i4i2i2i4i2", p, ofs + 1)
            if w > 0 and h > 0 and pc >= 0 then
                local patches = {}
                local base = ofs + 22
                for j = 0, pc - 1 do
                    local pofs = base + j * 10
                    if pofs + 10 <= #p then
                        -- originx(i2) originy(i2) patch(i2) stepdir(i2) colormap(i2)
                        local ox, oy, pidx = string.unpack("<i2i2i2", p, pofs + 1)
                        patches[#patches + 1] = { originX = ox, originY = oy, pnameIdx = pidx }
                    end
                end
                W.texDefs[trimName(name)] = { w = w, h = h, patches = patches }
            end
        end
    end
end

-- Parse TEXTURE1 always, TEXTURE2 if present, merged into W.texDefs.
function W.loadTextureDefs()
    W.texDefs = W.texDefs or {}
    W.parseTextureLump("TEXTURE1")
    if W.lumpIndex and W.lumpIndex.TEXTURE2 then W.parseTextureLump("TEXTURE2") end
end

-- Decode a picture/patch lump into width, height and per-column post lists.
-- cols[px] = { {top=, pix="<bytes>"}, ... } (post pixels are palette indices).
-- Vanilla absolute-topdelta posts; 0xFF terminates a column. Bounds-guarded.
function W.patchColumns(data)
    if #data < 8 then return nil end
    local w, h = string.unpack("<i2i2", data, 1)   -- width,height,leftoffset,topoffset
    if w <= 0 or h <= 0 or w > 4096 or h > 4096 then return nil end
    if 8 + w * 4 > #data then return nil end
    local cols = {}
    for x = 0, w - 1 do
        local colofs = string.unpack("<I4", data, 8 + x * 4 + 1)
        local posts = {}
        local pos = colofs + 1
        local guard = 0
        while pos >= 1 and pos + 1 <= #data and guard < 1024 do
            guard = guard + 1
            local top = data:byte(pos)
            if not top or top == 0xFF then break end
            local len = data:byte(pos + 1)
            if not len then break end
            local pstart = pos + 3               -- skip topdelta, length, 1 pad
            local pend = pstart + len - 1
            if pend > #data then break end
            posts[#posts + 1] = { top = top, pix = data:sub(pstart, pend) }
            pos = pos + len + 4                   -- topdelta+length+pad+pixels+pad
        end
        cols[x] = posts
    end
    return w, h, cols
end

----------------------------------------------------------------------
-- SECTION D: PNG encoder (RGBA8, stored-DEFLATE). Byte-exact so
-- Texture.LoadTexture can read it back. CRC-32 covers each chunk's
-- type..data; Adler-32 covers the raw (filtered) deflate INPUT.
----------------------------------------------------------------------
function W.initCRC()
    if W.crctab then return end
    local t = {}
    for n = 0, 255 do
        local c = n
        for _ = 1, 8 do
            if (c & 1) ~= 0 then c = 0xEDB88320 ~ (c >> 1) else c = c >> 1 end
        end
        t[n] = c
    end
    W.crctab = t
end

function W.crc32(s)
    local t = W.crctab
    local c = 0xFFFFFFFF
    for i = 1, #s do
        c = t[(c ~ s:byte(i)) & 0xFF] ~ (c >> 8)
    end
    return (c ~ 0xFFFFFFFF) & 0xFFFFFFFF
end

function W.adler32(s)
    local a, b = 1, 0
    local i, n = 1, #s
    while i <= n do
        local stop = min(i + 5551, n)            -- <=5552 bytes between mods
        for k = i, stop do a = a + s:byte(k); b = b + a end
        a = a % 65521; b = b % 65521
        i = stop + 1
    end
    return ((b << 16) | a) & 0xFFFFFFFF
end

-- Pure-Lua SHA-256 (FIPS 180-4), incremental. Used only to verify the
-- downloaded shareware IWAD against its pinned digest: sha256New() makes a
-- state, sha256Feed(st, slice) may be called with slices of any size (the
-- ~4 MB body is fed ~96 KB per present frame so hashing never stalls a frame),
-- sha256Done(st) pads and returns the digest as lowercase hex.
W.SHA_K = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
}

function W.sha256New()
    return { h = { 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                   0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 },
             len = 0, tail = "", w = {} }
end

-- Compress every full 64-byte block of (st.tail .. s); any remainder carries
-- over in st.tail for the next call. All words stay masked to 32 bits (Lua
-- integers are 64-bit, so sums never overflow before the mask).
function W.sha256Feed(st, s)
    st.len = st.len + #s
    if #st.tail > 0 then s = st.tail .. s; st.tail = "" end
    local K, w, h = W.SHA_K, st.w, st.h
    local h1, h2, h3, h4, h5, h6, h7, h8 =
        h[1], h[2], h[3], h[4], h[5], h[6], h[7], h[8]
    local n = #s
    local pos = 1
    while pos + 63 <= n do
        w[1], w[2], w[3], w[4], w[5], w[6], w[7], w[8],
        w[9], w[10], w[11], w[12], w[13], w[14], w[15], w[16], pos =
            string.unpack(">I4I4I4I4I4I4I4I4I4I4I4I4I4I4I4I4", s, pos)
        for i = 17, 64 do
            local x, y = w[i - 15], w[i - 2]
            local s0 = (((x >> 7) | (x << 25)) ~ ((x >> 18) | (x << 14)) ~ (x >> 3)) & 0xFFFFFFFF
            local s1 = (((y >> 17) | (y << 15)) ~ ((y >> 19) | (y << 13)) ~ (y >> 10)) & 0xFFFFFFFF
            w[i] = (w[i - 16] + s0 + w[i - 7] + s1) & 0xFFFFFFFF
        end
        local a, b, c, d, e, f, g, hh = h1, h2, h3, h4, h5, h6, h7, h8
        for i = 1, 64 do
            local S1 = (((e >> 6) | (e << 26)) ~ ((e >> 11) | (e << 21)) ~ ((e >> 25) | (e << 7))) & 0xFFFFFFFF
            local ch = (e & f) ~ ((~e) & g)
            local t1 = (hh + S1 + ch + K[i] + w[i]) & 0xFFFFFFFF
            local S0 = (((a >> 2) | (a << 30)) ~ ((a >> 13) | (a << 19)) ~ ((a >> 22) | (a << 10))) & 0xFFFFFFFF
            local maj = (a & b) ~ (a & c) ~ (b & c)
            local t2 = (S0 + maj) & 0xFFFFFFFF
            hh = g; g = f; f = e; e = (d + t1) & 0xFFFFFFFF
            d = c; c = b; b = a; a = (t1 + t2) & 0xFFFFFFFF
        end
        h1 = (h1 + a) & 0xFFFFFFFF; h2 = (h2 + b) & 0xFFFFFFFF
        h3 = (h3 + c) & 0xFFFFFFFF; h4 = (h4 + d) & 0xFFFFFFFF
        h5 = (h5 + e) & 0xFFFFFFFF; h6 = (h6 + f) & 0xFFFFFFFF
        h7 = (h7 + g) & 0xFFFFFFFF; h8 = (h8 + hh) & 0xFFFFFFFF
    end
    h[1], h[2], h[3], h[4], h[5], h[6], h[7], h[8] =
        h1, h2, h3, h4, h5, h6, h7, h8
    if pos <= n then st.tail = string.sub(s, pos) end
end

-- Append the FIPS padding (0x80, zeros, 64-bit big-endian BIT length), compress
-- the final block(s), and return the 64-char lowercase hex digest.
function W.sha256Done(st)
    local msgLen = st.len
    local padLen = 55 - (msgLen % 64)
    if padLen < 0 then padLen = padLen + 64 end
    W.sha256Feed(st, "\128" .. string.rep("\0", padLen) .. string.pack(">I8", msgLen * 8))
    local h = st.h
    return string.format("%08x%08x%08x%08x%08x%08x%08x%08x",
        h[1], h[2], h[3], h[4], h[5], h[6], h[7], h[8])
end

-- rgba = w*h*4 row-major top-first RGBA -> a valid RGBA8 PNG byte string.
function W.encodePNG(rgba, w, h)
    W.initCRC()
    local function chunk(typ, data)
        return string.pack(">I4", #data) .. typ .. data
            .. string.pack(">I4", W.crc32(typ .. data))
    end
    local sig = "\137\80\78\71\13\10\26\10"
    -- IHDR: width(BE) height(BE) bitdepth=8 colortype=6(RGBA) comp=0 filter=0 interlace=0
    local ihdr = string.pack(">I4I4BBBBB", w, h, 8, 6, 0, 0, 0)
    -- Raw deflate INPUT = per-row filter byte 0 (None) + w*4 RGBA bytes.
    local rows = {}
    local stride = w * 4
    for y = 0, h - 1 do
        rows[#rows + 1] = "\0" .. rgba:sub(y * stride + 1, (y + 1) * stride)
    end
    local raw = table.concat(rows)
    -- Stored DEFLATE blocks (<=65535 bytes each).
    local blocks = {}
    local n = #raw
    if n == 0 then
        blocks[1] = string.pack("<BI2I2", 1, 0, 0xFFFF)
    else
        local i = 1
        while i <= n do
            local stop = min(i + 65534, n)
            local slice = raw:sub(i, stop)
            local isLast = (stop == n) and 1 or 0
            blocks[#blocks + 1] =
                string.pack("<BI2I2", isLast, #slice, (~#slice) & 0xFFFF) .. slice
            i = stop + 1
        end
    end
    -- zlib: header 0x78 0x01, stored blocks, Adler-32 (BE) of raw.
    local idat = "\120\1" .. table.concat(blocks) .. string.pack(">I4", W.adler32(raw))
    return sig .. chunk("IHDR", ihdr) .. chunk("IDAT", idat) .. chunk("IEND", "")
end

----------------------------------------------------------------------
-- SECTION E: texture pipeline (composite, flat -> RGBA, on-disk PNG cache,
-- lazy async LoadTexture with a per-frame bake budget + flat-shaded fallback).
----------------------------------------------------------------------
-- Composite a wall texture NAME -> row-major top-first RGBA, plus w,h. Later
-- patches overwrite earlier ones (last wins). Unpainted pixels are transparent.
function W.compositeTexture(name)
    if not name or not W.pal then return nil end
    W.texRGBA = W.texRGBA or {}; W.texW = W.texW or {}; W.texH = W.texH or {}
    local key = "T:" .. name
    if W.texRGBA[key] then return W.texRGBA[key], W.texW[key], W.texH[key] end
    local def = W.texDefs and W.texDefs[name]
    if not def then return nil end
    local w, h = def.w, def.h
    if w <= 0 or h <= 0 or w > 4096 or h > 4096 then return nil end
    local total = w * h
    local idx, alpha = {}, {}
    for k = 0, total - 1 do alpha[k] = 0 end
    for _, pe in ipairs(def.patches) do
        local pname = W.pnames and W.pnames[pe.pnameIdx]
        if pname then
            local ord = (W.patchLump and W.patchLump[pname])
                or (W.lumpIndex and W.lumpIndex[pname] and W.lumpIndex[pname][1])
            local data = W.lumpBytes(ord)
            if #data > 0 then
                local pw, ph, cols = W.patchColumns(data)
                if pw then
                    local ox, oy = pe.originX, pe.originY
                    for px = 0, pw - 1 do
                        local sx = ox + px
                        if sx >= 0 and sx < w then
                            local posts = cols[px]
                            if posts then
                                for _, post in ipairs(posts) do
                                    local pix, tp = post.pix, post.top
                                    for i = 1, #pix do
                                        local sy = oy + tp + (i - 1)
                                        if sy >= 0 and sy < h then
                                            local kk = sy * w + sx
                                            idx[kk] = pix:byte(i)
                                            alpha[kk] = 255
                                        end
                                    end
                                end
                            end
                        end
                    end
                end
            end
        end
    end
    local out, pal = {}, W.pal
    for k = 0, total - 1 do
        if alpha[k] == 255 then
            local col = pal[idx[k]] or { 0, 0, 0 }
            out[k + 1] = string.char(col[1], col[2], col[3], 255)
        else
            out[k + 1] = "\0\0\0\0"
        end
    end
    local rgba = table.concat(out)
    W.texRGBA[key] = rgba; W.texW[key] = w; W.texH[key] = h
    return rgba, w, h
end

-- A flat is a raw 64x64 palette-index bitmap (4096 bytes). Fully opaque.
function W.flatToRGBA(name)
    if not name or not W.pal then return nil end
    W.texRGBA = W.texRGBA or {}; W.texW = W.texW or {}; W.texH = W.texH or {}
    local key = "F:" .. name
    if W.texRGBA[key] then return W.texRGBA[key], 64, 64 end
    local ord = (W.flatLump and W.flatLump[name])
        or (W.lumpIndex and W.lumpIndex[name] and W.lumpIndex[name][1])
    local bytes = W.lumpBytes(ord)
    if #bytes < 4096 then return nil end
    local out, pal = {}, W.pal
    for i = 0, 4095 do
        local col = pal[bytes:byte(i + 1)] or { 0, 0, 0 }
        out[i + 1] = string.char(col[1], col[2], col[3], 255)
    end
    local rgba = table.concat(out)
    W.texRGBA[key] = rgba; W.texW[key] = 64; W.texH[key] = 64
    return rgba, 64, 64
end

-- Write raw bytes in BINARY mode. FileMgr.WriteFileContent is text-mode on this
-- build and corrupts binary, so PNGs must go through io.open(path, "wb").
function W.writeBytes(path, bytes)
    local ook, f = pcall(io.open, path, "wb")
    if not ook or not f then return false end
    local wok = pcall(f.write, f, bytes)
    pcall(f.close, f)
    return wok
end

-- Best-effort one-time graphics load after a wad opens (pcall-wrapped; on any
-- failure W.texturesOk stays false and the renderer keeps the flat strips).
function W.loadGraphics()
    if W.gfxTried then return end
    W.gfxTried = true
    W.texturesOk = false
    W.texDefs = {}
    local ok = pcall(function()
        W.scanNamespaces()
        W.buildSpriteFrames()   -- W.spriteFrames from the S_START/S_END namespace
        W.loadPalette()
        W.loadPnames()
        W.loadTextureDefs()
    end)
    if ok and W.pal then W.texturesOk = true end
    W.ensureCacheDir()      -- per-wad dir; W.wadFp was set by openWad before this
end

-- Get a live ImTextureID for a wall texture (isFlat=false) or flat (true), or
-- nil (caller falls back to a shaded strip). Call ONCE per seg per frame. Bakes
-- lazily to a disk PNG then LoadTexture's it async; polls IsTextureValid.
function W.getTex(name, isFlat)
    if not name or not W.pal or not W.cacheDir then return nil end
    local key = (isFlat and "F:" or "T:") .. name
    W.texCache = W.texCache or {}
    local c = W.texCache[key]
    if c == nil then
        if (W.bakeUsed or 0) >= (W.BAKE_BUDGET or 4) then return nil end
        local sw, sh
        if isFlat then
            sw, sh = 64, 64
        else
            local def = W.texDefs and W.texDefs[name]
            if not def or def.w <= 0 or def.h <= 0 then
                W.texCache[key] = { state = "fail" }; return nil
            end
            sw, sh = def.w, def.h
        end
        W.bakeUsed = (W.bakeUsed or 0) + 1
        local fn = key:gsub("[^%w_%-]", function(ch)
            return string.format("$%02X", ch:byte())
        end) .. ".png"
        local path = W.cacheDir .. "/" .. fn
        local exists = false
        local dok, de = pcall(FileMgr.DoesFileExist, path)
        if dok then exists = de end
        if not exists then
            local rgba, w, h
            if isFlat then rgba, w, h = W.flatToRGBA(name)
            else rgba, w, h = W.compositeTexture(name) end
            if not rgba then W.texCache[key] = { state = "fail" }; return nil end
            local pok, png = pcall(W.encodePNG, rgba, w, h)
            if not pok or not png then W.texCache[key] = { state = "fail" }; return nil end
            if not W.writeBytes(path, png) then
                W.texCache[key] = { state = "fail" }; return nil
            end
            sw, sh = w, h
        end
        local id
        local lok, lid = pcall(Texture.LoadTexture, path)
        if lok then id = lid end
        if not id then W.texCache[key] = { state = "fail" }; return nil end
        W.texCache[key] = { id = id, state = "pending", w = sw, h = sh }
        return nil
    end
    if c.state == "fail" then return nil end
    if c.state == "pending" then
        local vok, valid = pcall(Texture.IsTextureValid, c.id)
        if not (vok and valid) then return nil end
        local tok, tex = pcall(Texture.GetTexture, c.id)
        if not (tok and tex) then return nil end
        c.tex = tex
        c.state = "ready"
    end
    if c.state == "ready" and c.tex then
        local gok, handle = pcall(function() return c.tex:GetCurrent() end)
        if gok and handle then return handle end
    end
    return nil
end

----------------------------------------------------------------------
-- SECTION F: BSP traversal + flat-shaded wall renderer
--
-- DOOM world convention (mirrored here): map units, x grows east, y grows
-- north. Camera W.viewAngle is in RADIANS, 0 = +x (east), increasing
-- counter-clockwise, so viewAngle = rad(thing.angle) needs no remap. Forward
-- world vector = (cos,sin); right world vector = (sin,-cos). View space:
-- translate by -view then rotate by -viewAngle so depth = +forward and
-- lateral = +right. 1/depth is linear in screen-x, so inverse depth is what
-- we interpolate per column (never depth itself).
----------------------------------------------------------------------
W.BASECOL = { wall = { 170, 150, 120 }, upper = { 150, 155, 175 }, lower = { 185, 150, 118 } }

-- Per-frame projection + occlusion buffer setup. Call once before the walk.
function W.setupView(sw, sh)
    W.hudH = floor(sh * 0.16)              -- vanilla status bar: 32 of 200 lines
    W.viewW = sw
    W.viewH = sh - W.hudH                  -- world drawn over y=[0, viewH]
    W.centerX = W.viewW * 0.5
    W.centerY = W.viewH * 0.5
    W.horizon = W.centerY
    W.projScale = (W.viewW * 0.5) / tan(W.HFOV * 0.5)
    W.RW = clamp(floor(sw / 8), 80, 200)   -- internal render columns (perf cap)
    W.colW = W.viewW / W.RW
    W.sinA = sin(W.viewAngle); W.cosA = cos(W.viewAngle)
    W.ceilclip = W.ceilclip or {}
    W.floorclip = W.floorclip or {}
    W.colClosed = W.colClosed or {}
    -- Drawseg silhouette pool (Doom-faithful sprite masking). Each occluding seg
    -- records, for every column it spans, a snapshot of the cumulative clip window
    -- (top = ceilclip, bottom = floorclip) plus its per-column depth. The BSP walk
    -- is near-child-first, so ceilclip/floorclip already fold in every nearer seg;
    -- the snapshot is therefore cumulative, and drawThing rebuilds each sprite's
    -- clip from the farthest in-front seg per column (far->near, first real writer
    -- wins). Pools are reused across frames (no per-frame allocation).
    W.dsPool = W.dsPool or {}       -- reused drawseg records {colL,colR,invL,invR,top[],bot[]}
    W.clipTop = W.clipTop or {}     -- per-sprite scratch (drawThing inits its own range)
    W.clipBot = W.clipBot or {}
    for c = 0, W.RW - 1 do
        W.ceilclip[c] = 0; W.floorclip[c] = W.viewH; W.colClosed[c] = false
    end
    W.dsCount = 0                   -- drawsegs recorded this frame
    W.closedCount = 0
    W.bakeUsed = 0                         -- per-frame texture-bake budget counter
    -- Visplane per-frame reset: bump the stamp (a plane column is "live" iff its
    -- stamp == frameSeq), drop the plane-key map (pooled planes are never wiped).
    W.frameSeq = (W.frameSeq or 0) + 1
    W.planeCount = 0
    W.planeMap = W.planeMap or {}
    for k in pairs(W.planeMap) do W.planeMap[k] = nil end
    W.planeDraws = 0
end

-- Cross product of the partition line direction with the vector to the point.
-- 0 = right/front child (nd.rchild), 1 = left/back child. Equal counts as back.
function W.pointOnSide(x, y, nd)
    local cross = nd.dx * (y - nd.y) - nd.dy * (x - nd.x)
    if cross < 0 then return 0 else return 1 end
end

-- Descend near child first so the first wall to claim a column wins (painter).
function W.renderNode(ref, depth)
    if W.closedCount >= W.RW then return end          -- screen fully covered
    depth = (depth or 0) + 1
    if depth > (W.nodeMax or 8192) then return end    -- guard vs cyclic/garbage BSP
    local kind, idx = W.decodeChild(ref)
    if kind == "subsector" then W.renderSubsector(idx); return end
    local nd = W.map.nodes[idx + 1]
    if not nd then return end
    local side = W.pointOnSide(W.viewX, W.viewY, nd)
    if side == 0 then
        W.renderNode(nd.rchild, depth); W.renderNode(nd.lchild, depth)
    else
        W.renderNode(nd.lchild, depth); W.renderNode(nd.rchild, depth)
    end
end

function W.renderSubsector(ssIdx)
    local ss = W.map.ssectors[ssIdx + 1]
    if not ss then return end
    for k = 0, ss.segCount - 1 do
        local seg = W.map.segs[ss.firstSeg + k + 1]
        if seg then W.renderSeg(seg) end
    end
end

-- One filled internal column; +0.8 on the right edge hides seams between cols.
function W.strip(col, y0, y1, r, g, b)
    if y1 <= y0 then return end
    local x0 = col * W.colW
    rectf(x0, y0, x0 + W.colW + 0.8, y1, r, g, b, 255)
end

-- Brightness scalar = sector light x distance diminish, with vanilla fake
-- contrast (r_segs.c): exactly-E-W walls one light level (16) darker, exactly-
-- N-S walls one brighter. Muzzle flashes add W.extralight. Shared by the
-- flat-shaded path (as a color multiplier) and the textured path (as a tint).
function W.wallLight(sector, depth, seg)
    local light = sector.light + (W.extralight or 0)
    local v1 = W.map.vertexes[seg.v1 + 1]
    local v2 = W.map.vertexes[seg.v2 + 1]
    if v1 and v2 then
        if v1.y == v2.y then light = light - 16
        elseif v1.x == v2.x then light = light + 16 end
    end
    local lf = 0.22 + 0.78 * (clamp(light, 0, 255) / 255)
    local fog = clamp(1.0 - depth * W.PLANE_FOG, 0.26, 1.0)
    return clamp(lf * fog, 0.10, 1.15)
end

-- Flat color = base tint x wallLight (Phase-2 fallback when no texture is ready).
function W.wallShade(sector, depth, kind, seg)
    local base = W.BASECOL[kind] or W.BASECOL.wall
    local br = W.wallLight(sector, depth, seg)
    return base[1] * br, base[2] * br, base[3] * br
end

-- Pack a grey ImU32 tint from a brightness scalar (r=g=b so channel order does
-- not matter; bit 24 is the ImGui default alpha). Modulates AddImage output.
function W.greyTint(br)
    local s = ci(255 * br)
    return 0xFF000000 | (s << 16) | (s << 8) | s
end

-- Draw one perspective-correct textured column as CLAMP-safe vertical bands.
-- The sampler is CLAMP, so a wall taller than texH is one AddImage per texel
-- band (each band keeps uv v inside [0,1]). yTopFull/yBotFull are the UNCLAMPED
-- projected screen y of the wall's top/bottom (V is affine in screen y between
-- them); [yDrawTop,yDrawBot] is the clip-clamped visible range for this column.
function W.stripTex(col, yDrawTop, yDrawBot, yTopFull, yBotFull, vTop, vBot, tex, u, texH, tint)
    if yDrawBot <= yDrawTop then return end
    local span = yBotFull - yTopFull
    if span <= 0 then return end
    local dv = vBot - vTop
    if dv <= 0 then return end
    local x0 = col * W.colW
    local x1 = x0 + W.colW + 0.8               -- same seam-overlap as W.strip
    local vA = vTop + dv * (yDrawTop - yTopFull) / span
    local vB = vTop + dv * (yDrawBot - yTopFull) / span
    local kStart = floor(vA / texH)
    local kEnd = floor((vB - 1e-4) / texH)
    if kEnd - kStart > 64 then kEnd = kStart + 64 end   -- band cap for huge walls
    for k = kStart, kEnd do
        local bandLo = k * texH
        local vLo = max(vA, bandLo)
        local vHi = min(vB, bandLo + texH)
        if vHi > vLo then
            local yLo = yTopFull + (vLo - vTop) / dv * span
            local yHi = yTopFull + (vHi - vTop) / dv * span
            local v0 = (vLo - bandLo) / texH
            local v1 = (vHi - bandLo) / texH
            ImGui.AddImage(tex, x0, yLo, x1, yHi, u, v0, u, v1, tint)
        end
    end
end

-- Resolve per-column U (point-sampled, so CLAMP horizontal is fine) + V pegging
-- for one wall part, then hand off to W.stripTex. pegZ = the world height that
-- maps to texel row 0; vWorld(h) = pegZ - h + yoff (viewZ cancels out).
function W.drawWallPart(col, yDraw0, yDraw1, yFull0, yFull1, hTop, hBot,
    tex, texW, texH, pegZ, xoff, yoff, segoff, distU, tint)
    local uTexel = (xoff + segoff + distU) % texW   -- Lua % is non-negative here
    local u = (floor(uTexel) + 0.5) / texW
    local vTop = pegZ - hTop + yoff
    local vBot = pegZ - hBot + yoff
    W.stripTex(col, yDraw0, yDraw1, yFull0, yFull1, vTop, vBot, tex, u, texH, tint)
end

-- Project + draw a single seg. Endpoints are the seg's own vertices in draw
-- order (v1->v2); do NOT reorder by dir.
function W.renderSeg(seg)
    local V = W.map.vertexes
    local A = V[seg.v1 + 1]; local B = V[seg.v2 + 1]
    if not A or not B then return end

    local ax = A.x - W.viewX; local ay = A.y - W.viewY
    local depthA = ax * W.cosA + ay * W.sinA
    local latA = ax * W.sinA - ay * W.cosA
    local bx = B.x - W.viewX; local by = B.y - W.viewY
    local depthB = bx * W.cosA + by * W.sinA
    local latB = bx * W.sinA - by * W.cosA

    -- backface cull: draw only front-facing walls (viewer on the front side)
    if latA * depthB - latB * depthA >= 0 then return end

    -- distance along the wall at each endpoint (for perspective-correct U); the
    -- near-clip branches below interpolate it at the crossing just like lateral.
    local segLen = sqrt((B.x - A.x) * (B.x - A.x) + (B.y - A.y) * (B.y - A.y))
    local distA, distB = 0, segLen

    -- near-plane clip to depth >= NEARZ (interpolate lateral at the crossing)
    if depthA < W.NEARZ and depthB < W.NEARZ then return end
    if depthA < W.NEARZ then
        local t = (W.NEARZ - depthA) / (depthB - depthA)
        latA = latA + (latB - latA) * t; depthA = W.NEARZ
        distA = distA + (distB - distA) * t
    end
    if depthB < W.NEARZ then
        local t = (W.NEARZ - depthB) / (depthA - depthB)
        latB = latB + (latA - latB) * t; depthB = W.NEARZ
        distB = distB + (distA - distB) * t
    end

    local sxA = W.centerX + (latA / depthA) * W.projScale
    local sxB = W.centerX + (latB / depthB) * W.projScale
    if sxB - sxA < 0.5 then return end                 -- too thin / degenerate
    if sxB <= 0 or sxA >= W.viewW then return end       -- fully off-screen (no edge smear)
    local invA = 1 / depthA; local invB = 1 / depthB
    -- U/z is linear in screen x, so interpolate dist*inv (recover dist = uoz/inv).
    local uozA = distA * invA; local uozB = distB * invB

    local fsi = seg.frontSector
    if not fsi then return end                          -- miniseg guard
    local fs = W.map.sectors[fsi + 1]
    if not fs then return end
    local bs = seg.backSector and W.map.sectors[seg.backSector + 1] or nil
    -- Only a genuine one-sided line is a solid (middle-textured) wall. A two-sided
    -- line always draws its upper/lower parts, even when the back sector is closed
    -- (a shut door: the leaf is the UPPER texture, not the middle). The portal path
    -- collapses the column to fully occlude when the opening is zero, so occlusion
    -- is unchanged; this just stops a closed door rendering as an untextured slab.
    local solid = (bs == nil)

    -- Per-seg texture setup: resolve this seg's own sidedef, its x/y offsets and
    -- unpeg flags, and fetch the GPU textures ONCE (nil handle => shaded strip).
    local horizon, projScale, viewZ = W.horizon, W.projScale, W.viewZ
    local sd, xoff, yoff = nil, 0, 0
    local PEGTOP, PEGBOT = false, false
    local texMid, texUp, texLo
    local dMid, dUp, dLo
    if W.texturesOk and W.pal then
        local ld = W.map.linedefs[seg.linedef + 1]
        if ld then
            local sideIdx = (seg.dir == 0) and ld.front or ld.back
            if sideIdx and sideIdx ~= NONE then sd = W.map.sidedefs[sideIdx + 1] end
            if sd then
                xoff = sd.xoff or 0; yoff = sd.yoff or 0
                local flags = ld.flags or 0
                PEGTOP = (flags & 0x0008) ~= 0
                PEGBOT = (flags & 0x0010) ~= 0
                -- A two-sided line's mid is a MASKED texture (grate/fence): it
                -- is not drawn inline here but recorded on the drawseg and drawn
                -- in the sorted masked pass (W.drawMaskedSeg), like vanilla's
                -- R_RenderMaskedSegRange, so sprites sort correctly against it.
                texMid = W.getTex(sd.mid, false); dMid = sd.mid and W.texDefs[sd.mid]
                if not solid then
                    texUp = W.getTex(sd.upper, false); dUp = sd.upper and W.texDefs[sd.upper]
                    texLo = W.getTex(sd.lower, false); dLo = sd.lower and W.texDefs[sd.lower]
                end
            end
        end
    end
    local segoff = seg.offset or 0

    local colL = clamp(floor(sxA / W.colW), 0, W.RW - 1)
    local colR = clamp(floor(sxB / W.colW), 0, W.RW - 1)
    -- Grab a pooled drawseg silhouette record: per-column top/bot snapshot arrays
    -- (indexed col-colL) plus 1/depth at both end columns for the per-column depth
    -- test in drawThing. Degrades (records nothing) past the seg cap.
    local dsi, dsTop, dsBot = nil, nil, nil
    if W.dsCount < W.DS_MAXSEGS then
        W.dsCount = W.dsCount + 1
        dsi = W.dsPool[W.dsCount]
        if not dsi then dsi = { top = {}, bot = {} }; W.dsPool[W.dsCount] = dsi end
        dsi.mid = nil                 -- pooled record: clear stale masked-mid flag
        dsTop, dsBot = dsi.top, dsi.bot
    end
    local dsInvL = invA + (invB - invA) * clamp(((colL + 0.5) * W.colW - sxA) / (sxB - sxA), 0, 1)
    local dsInvR = invA + (invB - invA) * clamp(((colR + 0.5) * W.colW - sxA) / (sxB - sxA), 0, 1)
    local dsWrote = false
    for col = colL, colR do
        if dsi then dsTop[col - colL] = -1; dsBot[col - colL] = -1 end  -- -1 = unset/no clip
        if not W.colClosed[col] then
            local top = W.ceilclip[col]; local bot = W.floorclip[col]
            if top < bot then
                local t = clamp(((col + 0.5) * W.colW - sxA) / (sxB - sxA), 0, 1)
                local inv = invA + (invB - invA) * t
                local depth = 1 / inv
                -- Grey light tint + world dist along the wall are shared by all
                -- textured parts of this column; only computed when texturing.
                local tint, distU
                if texMid or texUp or texLo then
                    tint = W.greyTint(W.wallLight(fs, depth, seg))
                    distU = (uozA + (uozB - uozA) * t) / inv
                end
                -- VISPLANE CAPTURE: the front sector's floor + ceiling gaps that
                -- this column leaves (OLD top/bot, before the clip update below).
                -- Ceiling band = [top .. front ceiling projection]; floor band =
                -- [front floor projection .. bot]. Solid and portal cases unify.
                local yCeilFront  = horizon - (fs.ceil  - viewZ) * projScale * inv
                local yFloorFront = horizon - (fs.floor - viewZ) * projScale * inv
                W.addPlaneCol(true,  fs.ceilTex,  fs.ceil,  fs.light, col, top, clamp(yCeilFront, top, bot))
                W.addPlaneCol(false, fs.floorTex, fs.floor, fs.light, col, clamp(yFloorFront, top, bot), bot)
                if solid then
                    local yCeilFull = horizon - (fs.ceil - viewZ) * projScale * inv
                    local yFloorFull = horizon - (fs.floor - viewZ) * projScale * inv
                    local yT = clamp(yCeilFull, top, bot)
                    local yB = clamp(yFloorFull, top, bot)
                    if yB > yT then
                        if texMid and dMid then
                            local pegZ = PEGBOT and (fs.floor + dMid.h) or fs.ceil
                            W.drawWallPart(col, yT, yB, yCeilFull, yFloorFull,
                                fs.ceil, fs.floor, texMid, dMid.w, dMid.h,
                                pegZ, xoff, yoff, segoff, distU, tint)
                        else
                            local r, g, b = W.wallShade(fs, depth, "wall", seg)
                            W.strip(col, yT, yB, r, g, b)
                        end
                    end
                    W.colClosed[col] = true; W.closedCount = W.closedCount + 1
                    if dsi then                 -- full wall: closed window (top>=bot hides sprites)
                        dsTop[col - colL] = W.viewH; dsBot[col - colL] = 0
                        dsWrote = true
                    end
                else
                    local yFtop = horizon - (fs.ceil - viewZ) * projScale * inv
                    local yFbot = horizon - (fs.floor - viewZ) * projScale * inv
                    local yBtop = horizon - (bs.ceil - viewZ) * projScale * inv
                    local yBbot = horizon - (bs.floor - viewZ) * projScale * inv
                    -- Sky wins over the upper step: when the back sector's ceiling
                    -- is F_SKY1, skip the upper wall so the sky backdrop shows through.
                    if bs.ceil < fs.ceil and bs.ceilTex ~= "F_SKY1" then  -- upper step
                        local a = clamp(yFtop, top, bot); local b2 = clamp(yBtop, top, bot)
                        if b2 > a then
                            if texUp and dUp then
                                local pegZ = PEGTOP and fs.ceil or (bs.ceil + dUp.h)
                                W.drawWallPart(col, a, b2, yFtop, yBtop,
                                    fs.ceil, bs.ceil, texUp, dUp.w, dUp.h,
                                    pegZ, xoff, yoff, segoff, distU, tint)
                            else
                                local r, g, bl = W.wallShade(fs, depth, "upper", seg)
                                W.strip(col, a, b2, r, g, bl)
                            end
                        end
                    end
                    if bs.floor > fs.floor then                -- lower step
                        local a = clamp(yBbot, top, bot); local b2 = clamp(yFbot, top, bot)
                        if b2 > a then
                            if texLo and dLo then
                                local pegZ = PEGBOT and fs.ceil or bs.floor
                                W.drawWallPart(col, a, b2, yBbot, yFbot,
                                    bs.floor, fs.floor, texLo, dLo.w, dLo.h,
                                    pegZ, xoff, yoff, segoff, distU, tint)
                            else
                                local r, g, bl = W.wallShade(fs, depth, "lower", seg)
                                W.strip(col, a, b2, r, g, bl)
                            end
                        end
                    end
                    -- shrink the open window to the back opening (never close mid)
                    local nTop = max(top, clamp(max(yFtop, yBtop), top, bot))
                    local nBot = min(bot, clamp(min(yFbot, yBbot), top, bot))
                    W.ceilclip[col] = nTop
                    W.floorclip[col] = nBot
                    if nTop >= nBot then
                        W.colClosed[col] = true; W.closedCount = W.closedCount + 1
                        if dsi then             -- collapsed portal: closed window
                            dsTop[col - colL] = W.viewH; dsBot[col - colL] = 0
                            dsWrote = true
                        end
                    elseif dsi then
                        -- open portal: snapshot the cumulative clip window. A sprite
                        -- behind is bounded by this opening (steps AND clear doorways).
                        dsTop[col - colL] = nTop; dsBot[col - colL] = nBot
                        dsWrote = true
                    end
                end
            end
        end
    end
    if dsi and not dsWrote then
        W.dsCount = W.dsCount - 1        -- recorded nothing occluding: reclaim the slot
    elseif dsi then
        dsi.colL = colL; dsi.colR = colR
        dsi.invL = dsInvL; dsi.invR = dsInvR
        if (not solid) and texMid and dMid then
            -- Masked mid texture (grate/fence): flag this drawseg for the sorted
            -- masked pass. The per-column top/bot snapshot above is exactly the
            -- opening window folded with every nearer occluder, so drawMaskedSeg
            -- only needs the projection + texture-mapping constants of this seg.
            dsi.mid = texMid; dsi.midW = dMid.w; dsi.midH = dMid.h
            dsi.midSxA = sxA; dsi.midSxB = sxB
            dsi.midInvA = invA; dsi.midInvB = invB
            dsi.midUozA = uozA; dsi.midUozB = uozB
            dsi.midUOff = xoff + segoff
            dsi.midFs = fs; dsi.midSeg = seg
            dsi.midDepth = 2 / (dsInvL + dsInvR)   -- seg-center depth, for the far->near sort
            -- Vanilla pegging (r_segs.c): the texture hangs one texH from the
            -- opening top, or sits on the opening bottom when lower-unpegged;
            -- rowoffset shifts it. Never tiled vertically (masked = one band).
            local openTop = (bs.ceil < fs.ceil) and bs.ceil or fs.ceil
            local openBot = (bs.floor > fs.floor) and bs.floor or fs.floor
            dsi.midHTop = (PEGBOT and (openBot + dMid.h) or openTop) + yoff
            dsi.midHBot = dsi.midHTop - dMid.h
        end
    end
end

-- Background: an 8-band ceiling gradient over [0,horizon] and floor gradient
-- over [horizon,viewH]. Drawn before the BSP walk; shows through portals.
function W.drawBackground()
    local sw, horizon, viewH = W.viewW, W.horizon, W.viewH
    local NB = 8
    for i = 0, NB - 1 do
        local y0 = horizon * i / NB
        local y1 = horizon * (i + 1) / NB
        local tt = i / NB
        rectf(0, y0, sw, y1 + 1, 26 + 34 * tt, 28 + 30 * tt, 40 + 40 * tt, 255)
    end
    for i = 0, NB - 1 do
        local y0 = horizon + (viewH - horizon) * i / NB
        local y1 = horizon + (viewH - horizon) * (i + 1) / NB
        local tt = i / NB
        rectf(0, y0, sw, y1 + 1, 60 + 46 * tt, 46 + 30 * tt, 34 + 16 * tt, 255)
    end
end

----------------------------------------------------------------------
-- SECTION G: visplanes (textured floors + ceilings) + sky
--
-- Floors/ceilings are the exact gaps the wall pass leaves, captured per column
-- during the front-to-back BSP walk (W.addPlaneCol) into pooled, stamp-validated
-- visplanes, then filled after the walk (W.drawPlanes). A plane's horizontal runs
-- are extracted with the classic column-sweep (O(perimeter)) and each run is one
-- affine-mapped quad (ImGui.AddImageQuad) of a TILED flat, with a distance/light
-- black-overlay shade. When a flat is not yet baked, or a run is wider than one
-- tiled period (near-horizon LOD), the run degrades to one distance-shaded solid
-- rect. F_SKY1 ceilings are skipped so the cylindrical sky backdrop shows through.
----------------------------------------------------------------------
-- Map name -> sky wall-texture name. ExMy -> SKY<episode>; DOOM2 MAPxx banded.
function W.skyTexName(mapName)
    mapName = trimName(mapName)
    local e = mapName:match("^E(%d)M%d$")
    if e then return "SKY" .. e end
    local n = tonumber(mapName:match("^MAP(%d%d)$"))
    if n then
        if n <= 11 then return "SKY1" elseif n <= 20 then return "SKY2" else return "SKY3" end
    end
    return "SKY1"
end

-- Fetch (or make) the pooled visplane that owns this column for the given
-- (isCeil, flat, height, light). Each column is written at most once per plane;
-- a second subsector wanting the same key at the same column gets a sibling.
function W.getPlane(isCeil, flat, height, light, col)
    local key = (isCeil and "C" or "F") .. flat .. "|" .. height .. "|" .. light
    local list = W.planeMap[key]
    if not list then list = {}; W.planeMap[key] = list end
    for i = 1, #list do
        local p = list[i]
        if p.stamp[col] ~= W.frameSeq then return p end   -- this column still free
    end
    -- Need a fresh sibling: reuse the pool slot (stamp-validated, never wiped).
    W.planeCount = W.planeCount + 1
    W.planePool = W.planePool or {}
    local p = W.planePool[W.planeCount]
    if not p then
        p = { top = {}, bot = {}, stamp = {} }
        W.planePool[W.planeCount] = p
    end
    p.isCeil = isCeil; p.flat = flat; p.height = height; p.light = light
    p.minx = col; p.maxx = col
    p.tex = nil; p.texTried = false; p.avg = nil
    list[#list + 1] = p
    return p
end

-- Record one column's [yTop,yBot] band into the matching visplane. Sky ceilings
-- and untextured ("-") flats are skipped (the backdrop/plane below shows through).
function W.addPlaneCol(isCeil, flat, height, light, col, yTop, yBot)
    if yBot <= yTop then return end
    if not flat then return end                       -- "-" ceil/floor: nothing to draw
    if isCeil and flat == "F_SKY1" then return end    -- sky is a backdrop, not a plane
    local p = W.getPlane(isCeil, flat, height, light, col)
    p.top[col] = yTop; p.bot[col] = yBot; p.stamp[col] = W.frameSeq
    if col < p.minx then p.minx = col end
    if col > p.maxx then p.maxx = col end
end

-- Average palette colour of a flat (for the solid LOD / not-ready fallback),
-- cached. Returns {r,g,b} or nil (caller then uses W.PLANECOL).
function W.flatAvg(name)
    W.flatAvgCache = W.flatAvgCache or {}
    local a = W.flatAvgCache[name]
    if a ~= nil then if a == false then return nil else return a end end
    local rgba = W.flatToRGBA(name)
    if not rgba then W.flatAvgCache[name] = false; return nil end
    local rs, gs, bs = 0, 0, 0
    for i = 0, 4095 do
        rs = rs + rgba:byte(i * 4 + 1)
        gs = gs + rgba:byte(i * 4 + 2)
        bs = bs + rgba:byte(i * 4 + 3)
    end
    a = { floor(rs / 4096), floor(gs / 4096), floor(bs / 4096) }
    W.flatAvgCache[name] = a
    return a
end

-- A flat replicated FLAT_TILE x FLAT_TILE into an (64*N) square RGBA buffer, so
-- one uv unit [0,1] spans FLAT_TILE repeats = 64*FLAT_TILE world units. Reuses
-- the wall/flat pipeline; returns rgba, S, S (or nil).
function W.flatTiledRGBA(name)
    local src = W.flatToRGBA(name); if not src then return nil end   -- 64x64x4 bytes
    local N = W.FLAT_TILE; local S = 64 * N
    local rows = {}
    for ty = 0, 63 do
        local r = src:sub(ty * 64 * 4 + 1, ty * 64 * 4 + 64 * 4)     -- one 64-texel row
        rows[ty + 1] = r:rep(N)                                       -- N tiles across
    end
    local band = table.concat(rows)                                  -- 64 rows tall, S wide
    return band:rep(N), S, S                                         -- N tiles down
end

-- Get a live ImTextureID for a TILED flat (keyed "FT:" so it never collides with
-- the wall/flat keys). Clone of W.getTex(true) with the tiled bake; nil until the
-- async upload validates (callers fall back to solid).
function W.getTexTiled(name)
    if not name or not W.pal or not W.cacheDir then return nil end
    local key = "FT:" .. name
    W.texCache = W.texCache or {}
    local c = W.texCache[key]
    if c == nil then
        if (W.bakeUsed or 0) >= (W.BAKE_BUDGET or 4) then return nil end
        local S = 64 * W.FLAT_TILE
        W.bakeUsed = (W.bakeUsed or 0) + 1
        local fn = ("FT_" .. name):gsub("[^%w_%-]", function(ch)
            return string.format("$%02X", ch:byte())
        end) .. ".png"
        local path = W.cacheDir .. "/" .. fn
        local exists = false
        local dok, de = pcall(FileMgr.DoesFileExist, path)
        if dok then exists = de end
        if not exists then
            local rgba, w, h = W.flatTiledRGBA(name)
            if not rgba then W.texCache[key] = { state = "fail" }; return nil end
            local pok, png = pcall(W.encodePNG, rgba, w, h)
            if not pok or not png then W.texCache[key] = { state = "fail" }; return nil end
            if not W.writeBytes(path, png) then W.texCache[key] = { state = "fail" }; return nil end
            -- A 512x512 tiled-flat encode is ~58ms (pure-Lua crc32/adler32 over ~1MB),
            -- vs ~1-4ms for a wall. Charge it heavily so at most ~1 happens per frame,
            -- spreading the first-visit bakes instead of freezing for ~1.4s on map entry.
            W.bakeUsed = (W.bakeUsed or 0) + 3
        end
        local id
        local lok, lid = pcall(Texture.LoadTexture, path)
        if lok then id = lid end
        if not id then W.texCache[key] = { state = "fail" }; return nil end
        W.texCache[key] = { id = id, state = "pending", w = S, h = S }
        return nil
    end
    if c.state == "fail" then return nil end
    if c.state == "pending" then
        local vok, valid = pcall(Texture.IsTextureValid, c.id)
        if not (vok and valid) then return nil end
        local tok, tex = pcall(Texture.GetTexture, c.id)
        if not (tok and tex) then return nil end
        c.tex = tex; c.state = "ready"
    end
    if c.state == "ready" and c.tex then
        local gok, handle = pcall(function() return c.tex:GetCurrent() end)
        if gok and handle then return handle end
    end
    return nil
end

-- Resolve a plane's tiled texture (lazy) + average colour, once per frame.
function W.resolvePlaneTex(p)
    if p.texTried then return end
    p.texTried = true
    if W.texturesOk and W.pal and W.cacheDir then
        p.tex = W.getTexTiled(p.flat)
        p.texW = 64 * W.FLAT_TILE; p.texH = p.texW
    end
    p.avg = W.flatAvg(p.flat)
end

-- Brightness scalar for a plane row: sector light x distance diminish (mirrors
-- W.wallLight minus the fake contrast). Muzzle flashes add W.extralight.
function W.planeLight(light, rowDist)
    local lf = 0.22 + 0.78 * (clamp(light + (W.extralight or 0), 0, 255) / 255)
    local fog = clamp(1.0 - rowDist * W.PLANE_FOG, 0.26, 1.0)
    return clamp(lf * fog, 0.10, 1.0)
end

-- Draw one merged horizontal run of a plane: rows [rq*STEP .. +STEP], columns
-- [cS..cE]. rowDist (perpendicular depth) is constant across a row, so the run is
-- an affine quad; when the run spans more than one tiled period (near-horizon LOD)
-- or the flat is not ready, it degrades to one distance-shaded solid rect.
function W.drawSpan(p, rq, cS, cE)
    local STEP = W.ROWSTEP
    local horizon, projScale, viewZ = W.horizon, W.projScale, W.viewZ
    local colW = W.colW
    local yT = rq * STEP
    local yB = yT + STEP + 0.8                      -- vertical seam overlap
    local xL = cS * colW
    local xR = (cE + 1) * colW + 0.8                -- horizontal seam overlap
    local dH = abs(viewZ - p.height)                -- |eye - plane height|
    local dyT = yT - horizon; if abs(dyT) < 0.5 then dyT = (dyT < 0) and -0.5 or 0.5 end
    local dyB = yB - horizon; if abs(dyB) < 0.5 then dyB = (dyB < 0) and -0.5 or 0.5 end
    local rdT = projScale * dH / abs(dyT)           -- rowDist at the two edge rows
    local rdB = projScale * dH / abs(dyB)
    local br = W.planeLight(p.light, (rdT + rdB) * 0.5)

    local cosA, sinA, viewX, viewY, cx = W.cosA, W.sinA, W.viewX, W.viewY, W.centerX
    local sL = (xL - cx) / projScale
    local sR = (xR - cx) / projScale
    local wLtx = viewX + rdT * (cosA + sL * sinA); local wLty = viewY + rdT * (sinA - sL * cosA) -- TL
    local wRtx = viewX + rdT * (cosA + sR * sinA); local wRty = viewY + rdT * (sinA - sR * cosA) -- TR
    local wRbx = viewX + rdB * (cosA + sR * sinA); local wRby = viewY + rdB * (sinA - sR * cosA) -- BR
    local wLbx = viewX + rdB * (cosA + sL * sinA); local wLby = viewY + rdB * (sinA - sL * cosA) -- BL

    W.planeDraws = W.planeDraws + 1
    local texWorld = 64 * W.FLAT_TILE               -- one uv unit spans this many world units
    if p.tex and W.quadOk then
        local uTL, vTL = wLtx / texWorld, wLty / texWorld
        local uTR, vTR = wRtx / texWorld, wRty / texWorld
        local uBR, vBR = wRbx / texWorld, wRby / texWorld
        local uBL, vBL = wLbx / texWorld, wLby / texWorld
        local umin = min(uTL, uTR, uBR, uBL); local umax = max(uTL, uTR, uBR, uBL)
        local vmin = min(vTL, vTR, vBR, vBL); local vmax = max(vTL, vTR, vBR, vBL)
        if (umax - umin) <= 1.0 and (vmax - vmin) <= 1.0 then
            local ou, ov = floor(umin), floor(vmin) -- shift the near corner into [0,1)
            local qp, qt = W.qp, W.qt
            qp[1].x = xL; qp[1].y = yT; qp[2].x = xR; qp[2].y = yT
            qp[3].x = xR; qp[3].y = yB; qp[4].x = xL; qp[4].y = yB
            qt[1].x = uTL - ou; qt[1].y = vTL - ov; qt[2].x = uTR - ou; qt[2].y = vTR - ov
            qt[3].x = uBR - ou; qt[3].y = vBR - ov; qt[4].x = uBL - ou; qt[4].y = vBL - ov
            ImGui.AddImageQuad(p.tex, qp[1], qp[2], qp[3], qp[4], qt[1], qt[2], qt[3], qt[4], 255)
            if br < 0.97 then                        -- shade via a black overlay
                ImGui.AddRectFilled(xL, yT, xR, yB, 0, 0, 0, ci((1 - br) * 255))
            end
            return
        end
    end
    -- Solid fallback / far LOD: one distance-shaded rect (texture is a blur here).
    local base = p.avg or (p.isCeil and W.PLANECOL.ceil or W.PLANECOL.floor)
    ImGui.AddRectFilled(xL, yT, xR, yB, ci(base[1] * br), ci(base[2] * br), ci(base[3] * br), 255)
end

-- Fill every live visplane's gap. Per plane: resolve its texture, then extract
-- horizontal runs with the classic DOOM column sweep (compare each column's row
-- range to the previous) and draw each run. Row indices are quantized to ROWSTEP.
function W.drawPlanes()
    if W.quadOk == nil then
        W.quadOk = (type(ImGui.AddImageQuad) == "function")
            and (type(V2) == "table") and (type(V2.New) == "function")
        if W.quadOk then
            W.qp = { V2.New(0, 0), V2.New(0, 0), V2.New(0, 0), V2.New(0, 0) }
            W.qt = { V2.New(0, 0), V2.New(0, 0), V2.New(0, 0), V2.New(0, 0) }
        end
    end
    W.spanstart = W.spanstart or {}
    local ss = W.spanstart
    local STEP = W.ROWSTEP
    local BIG = 0x40000000                           -- empty-range top sentinel (> any row)
    for i = 1, W.planeCount do
        if W.planeDraws >= W.PLANE_BUDGET then break end
        local p = W.planePool[i]
        W.resolvePlaneTex(p)
        -- Column sweep (classic DOOM R_MakeSpans): compare each column's row range
        -- to the PREVIOUS column's ORIGINAL range. Empty range = top > bottom, with
        -- top = BIG so the "open from top" arm runs. prevT/prevB keep the previous
        -- column's unmodified range; the four while-loops mutate local copies only.
        local prevT, prevB = BIG, -1
        for c = p.minx, p.maxx + 1 do               -- +1 flushes any still-open spans
            local curT, curB = BIG, -1
            if c <= p.maxx and p.stamp[c] == W.frameSeq then
                -- floor (not ceil) the top so the topmost band overlaps the wall
                -- edge by <STEP px; walls are drawn first, planes over them, so this
                -- covers the sub-STEP seam that otherwise leaks the background gradient.
                local tt = floor(p.top[c] / STEP)
                local bb = floor((p.bot[c] - 1e-3) / STEP)
                if bb >= tt then curT, curB = tt, bb end
            end
            local t1, b1, t2, b2 = prevT, prevB, curT, curB
            while t1 < t2 and t1 <= b1 do W.drawSpan(p, t1, ss[t1], c - 1); t1 = t1 + 1 end
            while b1 > b2 and b1 >= t1 do W.drawSpan(p, b1, ss[b1], c - 1); b1 = b1 - 1 end
            while t2 < t1 and t2 <= b2 do ss[t2] = c; t2 = t2 + 1 end
            while b2 > b1 and b2 >= t1 do ss[b2] = c; b2 = b2 - 1 end
            prevT, prevB = curT, curB
            if W.planeDraws >= W.PLANE_BUDGET then break end
        end
    end
end

-- Cylindrical sky backdrop over the ceiling region [0,horizon]. HFOV=90deg maps
-- exactly one sky-texture width across the screen, offset by view angle; two
-- axis-aligned AddImage pieces cover the single wrap boundary (2 draws total).
function W.drawSky()
    if not (W.map and W.map.skyName) then return end
    local tex = W.getTex(W.map.skyName, false)      -- sky is a wall TEXTURE (patch path)
    if not tex then return end                       -- backdrop gradient already drawn
    local sw, horizon = W.viewW, W.horizon
    local base = (W.viewAngle / (pi * 0.5)) * W.SKY_DIR
    local u0 = base - floor(base)                    -- frac() into [0,1)
    local xw = (1.0 - u0) * sw                        -- single wrap boundary on screen
    local tint = 0xFFFFFFFF
    ImGui.AddImage(tex, 0, 0, xw, horizon, u0, 0.0, 1.0, 1.0, tint)  -- piece A: u [u0..1]
    ImGui.AddImage(tex, xw, 0, sw, horizon, 0.0, 0.0, u0, 1.0, tint) -- piece B: u [0..u0]
end

----------------------------------------------------------------------
-- SECTION H: THINGS as billboard sprites (static render, no AI/pickups)
--
-- Map THINGS (items, decorations, monster idle frames) are drawn as camera-
-- facing billboards after the walls + planes pass. Each thing type maps (by its
-- doomednum) to a sprite prefix + idle frame in W.THING_SPR; the S_START/S_END
-- lump namespace (scanned in W.scanNamespaces) is indexed into W.spriteFrames
-- for O(1) frame/rotation resolution. Sprites are composited (single patch, with
-- alpha) to an on-disk PNG and uploaded exactly like walls/flats (shared budget +
-- async LoadTexture). Depth-sorting is far->near for correct sprite-vs-sprite
-- overlap; per-column silhouette clipping against the drawseg list (built during
-- the BSP wall pass, see W.buildSpriteClip) hides sprites behind walls and clips
-- partial cover. Unknown doomednums are skipped (no clutter, no wrong art).
----------------------------------------------------------------------
-- H.1: doomednum -> sprite catalogue. Player/DM starts (1-4,11) deliberately
-- absent. r = blocking radius (a LATER collision phase, unused here). hang = top
-- anchored to the sector ceiling. anim = optional idle flash frames (unused here).
W.THING_SPR = {
    -- MONSTERS (idle spawn frame 'A', directional)
    [3004]={spr="POSS",seq="A",rot=true, kind="monster",r=20},
    [9]   ={spr="SPOS",seq="A",rot=true, kind="monster",r=20},
    [3001]={spr="TROO",seq="A",rot=true, kind="monster",r=20},
    [3002]={spr="SARG",seq="A",rot=true, kind="monster",r=30},
    [58]  ={spr="SARG",seq="A",rot=true, kind="monster",r=30},
    [3006]={spr="SKUL",seq="A",rot=true, kind="monster",r=16},
    [3005]={spr="HEAD",seq="A",rot=true, kind="monster",r=31},
    [3003]={spr="BOSS",seq="A",rot=true, kind="monster",r=24},
    [65]  ={spr="CPOS",seq="A",rot=true, kind="monster",r=20},
    [69]  ={spr="BOS2",seq="A",rot=true, kind="monster",r=24},
    [68]  ={spr="BSPI",seq="A",rot=true, kind="monster",r=64},
    [71]  ={spr="PAIN",seq="A",rot=true, kind="monster",r=31},
    [66]  ={spr="SKEL",seq="A",rot=true, kind="monster",r=20},
    [67]  ={spr="FATT",seq="A",rot=true, kind="monster",r=48},
    [64]  ={spr="VILE",seq="A",rot=true, kind="monster",r=20},
    [7]   ={spr="SPID",seq="A",rot=true, kind="monster",r=128},
    [16]  ={spr="CYBR",seq="A",rot=true, kind="monster",r=40},
    [84]  ={spr="SSWV",seq="A",rot=true, kind="monster",r=20},
    [88]  ={spr="BBRN",seq="A",rot=false,kind="monster",r=16},
    [72]  ={spr="KEEN",seq="A",rot=false,kind="monster",r=16,hang=true},
    -- WEAPONS (single image, non-directional)
    [2001]={spr="SHOT",seq="A",rot=false,kind="weapon"},
    [82]  ={spr="SGN2",seq="A",rot=false,kind="weapon"},
    [2002]={spr="MGUN",seq="A",rot=false,kind="weapon"},
    [2003]={spr="LAUN",seq="A",rot=false,kind="weapon"},
    [2004]={spr="PLAS",seq="A",rot=false,kind="weapon"},
    [2005]={spr="CSAW",seq="A",rot=false,kind="weapon"},
    [2006]={spr="BFUG",seq="A",rot=false,kind="weapon"},
    -- AMMO
    [2007]={spr="CLIP",seq="A",rot=false,kind="ammo"},
    [2048]={spr="AMMO",seq="A",rot=false,kind="ammo"},
    [2008]={spr="SHEL",seq="A",rot=false,kind="ammo"},
    [2049]={spr="SBOX",seq="A",rot=false,kind="ammo"},
    [2010]={spr="ROCK",seq="A",rot=false,kind="ammo"},
    [2046]={spr="BROK",seq="A",rot=false,kind="ammo"},
    [2047]={spr="CELL",seq="A",rot=false,kind="ammo"},
    [17]  ={spr="CELP",seq="A",rot=false,kind="ammo"},
    [8]   ={spr="BPAK",seq="A",rot=false,kind="ammo"},
    -- HEALTH / ARMOR / POWERUPS
    [2011]={spr="STIM",seq="A",rot=false,kind="powerup"},
    [2012]={spr="MEDI",seq="A",rot=false,kind="powerup"},
    [2014]={spr="BON1",seq="A",rot=false,kind="powerup"},
    [2015]={spr="BON2",seq="A",rot=false,kind="powerup"},
    [2018]={spr="ARM1",seq="A",rot=false,kind="powerup"},
    [2019]={spr="ARM2",seq="A",rot=false,kind="powerup"},
    [2013]={spr="SOUL",seq="A",rot=false,kind="powerup"},
    [2022]={spr="PINV",seq="A",rot=false,kind="powerup"},
    [2023]={spr="PSTR",seq="A",rot=false,kind="powerup"},
    [2024]={spr="PINS",seq="A",rot=false,kind="powerup"},
    [2025]={spr="SUIT",seq="A",rot=false,kind="powerup"},
    [2026]={spr="PMAP",seq="A",rot=false,kind="powerup"},
    [2045]={spr="PVIS",seq="A",rot=false,kind="powerup"},
    [83]  ={spr="MEGA",seq="A",rot=false,kind="powerup"},
    -- KEYS
    [5] ={spr="BKEY",seq="A",rot=false,kind="key"}, [40]={spr="BSKU",seq="A",rot=false,kind="key"},
    [6] ={spr="YKEY",seq="A",rot=false,kind="key"}, [39]={spr="YSKU",seq="A",rot=false,kind="key"},
    [13]={spr="RKEY",seq="A",rot=false,kind="key"}, [38]={spr="RSKU",seq="A",rot=false,kind="key"},
    -- BARREL + SOLID DECOR
    [2035]={spr="BAR1",seq="A",rot=false,kind="decor",r=10},
    [2028]={spr="COLU",seq="A",rot=false,kind="decor",r=16},
    [30]={spr="COL1",seq="A",rot=false,kind="decor",r=16},
    [31]={spr="COL2",seq="A",rot=false,kind="decor",r=16},
    [32]={spr="COL3",seq="A",rot=false,kind="decor",r=16},
    [33]={spr="COL4",seq="A",rot=false,kind="decor",r=16},
    [36]={spr="COL5",seq="A",rot=false,kind="decor",r=16},
    [37]={spr="COL6",seq="A",rot=false,kind="decor",r=16},
    [35]={spr="CBRA",seq="A",rot=false,kind="decor",r=16},
    [43]={spr="TRE1",seq="A",rot=false,kind="decor",r=16},
    [54]={spr="TRE2",seq="A",rot=false,kind="decor",r=32},
    [47]={spr="SMIT",seq="A",rot=false,kind="decor",r=16},
    [48]={spr="ELEC",seq="A",rot=false,kind="decor",r=16},
    [41]={spr="CEYE",seq="A",rot=false,kind="decor",r=16},
    [42]={spr="FSKU",seq="A",rot=false,kind="decor",r=16},
    -- NON-SOLID DECOR: candle + torches (idle flame anim optional)
    [34]={spr="CAND",seq="A",rot=false,kind="decor"},
    [44]={spr="TBLU",seq="A",rot=false,kind="decor",anim="ABCD"},
    [45]={spr="TGRN",seq="A",rot=false,kind="decor",anim="ABCD"},
    [46]={spr="TRED",seq="A",rot=false,kind="decor",anim="ABCD"},
    [55]={spr="SMBT",seq="A",rot=false,kind="decor",anim="ABCD"},
    [56]={spr="SMGT",seq="A",rot=false,kind="decor",anim="ABCD"},
    [57]={spr="SMRT",seq="A",rot=false,kind="decor",anim="ABCD"},
    -- CORPSES / GIBS (static death frame; NOT frame 'A'). Non-solid.
    [10]={spr="PLAY",seq="W",rot=false,kind="decor"},
    [12]={spr="PLAY",seq="W",rot=false,kind="decor"},
    [24]={spr="POL5",seq="A",rot=false,kind="decor"},
    [15]={spr="PLAY",seq="N",rot=false,kind="decor"},
    [18]={spr="POSS",seq="L",rot=false,kind="decor"},
    [19]={spr="SPOS",seq="L",rot=false,kind="decor"},
    [20]={spr="TROO",seq="M",rot=false,kind="decor"},
    [21]={spr="SARG",seq="N",rot=false,kind="decor"},
    [22]={spr="HEAD",seq="L",rot=false,kind="decor"},
    -- IMPALED / HANGING DECOR
    [25]={spr="POL1",seq="A",rot=false,kind="decor",r=16},
    [26]={spr="POL6",seq="A",rot=false,kind="decor",r=16},
    [27]={spr="POL4",seq="A",rot=false,kind="decor",r=16},
    [28]={spr="POL2",seq="A",rot=false,kind="decor",r=16},
    [29]={spr="POL3",seq="A",rot=false,kind="decor",r=16},
    [49]={spr="GOR1",seq="A",rot=false,kind="decor",hang=true},
    [50]={spr="GOR2",seq="A",rot=false,kind="decor",hang=true},
    [51]={spr="GOR3",seq="A",rot=false,kind="decor",hang=true},
    [52]={spr="GOR4",seq="A",rot=false,kind="decor",hang=true},
    [53]={spr="GOR5",seq="A",rot=false,kind="decor",hang=true},
}
-- Placeholder tint by kind (used while a sprite texture bakes, or if it never does)
W.KINDCOL = { monster={210,70,60}, weapon={230,200,70}, ammo={200,170,90},
    key={90,180,230}, powerup={90,220,120}, decor={150,150,160} }

----------------------------------------------------------------------
-- SECTION Ha: gameplay data tables (pickups, ammo, weapon names, monster HP)
-- Ported from DOOM p_inter.c (P_GiveBody/Armor/Ammo/Weapon/Card, clipammo[]).
----------------------------------------------------------------------
W.CLIPAMMO = { bul = 10, shl = 4, rck = 1, cel = 20 }   -- one "clip" per ammo type
-- doomednum -> pickup descriptor. amt/max health, pts/atype armor, at/clips ammo,
-- slot weapon, col/form key, pw power. "always" = taken even at max (bonuses).
W.PICKUP = {
    [2011] = { k = "health", amt = 10,  max = 100, msg = "Picked up a stimpack." },
    [2012] = { k = "health", amt = 25,  max = 100, msg = "Picked up a medikit." },
    [2014] = { k = "health", amt = 1,   max = 200, always = true, count = true, msg = "Picked up a health bonus." },
    [2013] = { k = "health", amt = 100, max = 200, always = true, count = true, msg = "Supercharge!" },
    [83]   = { k = "mega", count = true, msg = "MegaSphere!" },
    [2018] = { k = "armor", pts = 100, atype = 1, msg = "Picked up the armor." },
    [2019] = { k = "armor", pts = 200, atype = 2, msg = "Picked up the MegaArmor!" },
    [2015] = { k = "armorbonus", amt = 1, max = 200, always = true, count = true, msg = "Picked up an armor bonus." },
    [2007] = { k = "ammo", at = "bul", clips = 1, msg = "Picked up a clip." },
    [2048] = { k = "ammo", at = "bul", clips = 5, msg = "Picked up a box of bullets." },
    [2008] = { k = "ammo", at = "shl", clips = 1, msg = "Picked up 4 shotgun shells." },
    [2049] = { k = "ammo", at = "shl", clips = 5, msg = "Picked up a box of shotgun shells." },
    [2010] = { k = "ammo", at = "rck", clips = 1, msg = "Picked up a rocket." },
    [2046] = { k = "ammo", at = "rck", clips = 5, msg = "Picked up a box of rockets." },
    [2047] = { k = "ammo", at = "cel", clips = 1, msg = "Picked up an energy cell." },
    [17]   = { k = "ammo", at = "cel", clips = 5, msg = "Picked up an energy cell pack." },
    [8]    = { k = "backpack", msg = "Picked up a backpack full of ammo!" },
    [2001] = { k = "weapon", slot = 3, at = "shl", msg = "You got the shotgun!" },
    [82]   = { k = "weapon", slot = 9, at = "shl", msg = "You got the super shotgun!" },
    [2002] = { k = "weapon", slot = 4, at = "bul", msg = "You got the chaingun!" },
    [2003] = { k = "weapon", slot = 5, at = "rck", msg = "You got the rocket launcher!" },
    [2004] = { k = "weapon", slot = 6, at = "cel", msg = "You got the plasma gun!" },
    [2006] = { k = "weapon", slot = 7, at = "cel", msg = "You got the BFG9000!  Oh, yes." },
    [2005] = { k = "weapon", slot = 8, at = nil,   msg = "A chainsaw!  Find some meat!" },
    [5]  = { k = "key", col = "blue",   form = "card",  msg = "Picked up a blue keycard." },
    [40] = { k = "key", col = "blue",   form = "skull", msg = "Picked up a blue skull key." },
    [6]  = { k = "key", col = "yellow", form = "card",  msg = "Picked up a yellow keycard." },
    [39] = { k = "key", col = "yellow", form = "skull", msg = "Picked up a yellow skull key." },
    [13] = { k = "key", col = "red",    form = "card",  msg = "Picked up a red keycard." },
    [38] = { k = "key", col = "red",    form = "skull", msg = "Picked up a red skull key." },
    [2022] = { k = "power", pw = "invuln",  dur = 30 * 35, count = true, msg = "Invulnerability!" },
    [2023] = { k = "power", pw = "berserk", dur = -1, heal = 100, count = true, msg = "Berserk!" },
    [2024] = { k = "power", pw = "invis",   dur = 60 * 35, count = true, msg = "Partial Invisibility." },
    [2025] = { k = "power", pw = "radsuit", dur = 60 * 35, msg = "Radiation Shielding Suit." },
    [2026] = { k = "power", pw = "allmap",  dur = -1, count = true, msg = "Computer Area Map." },
    [2045] = { k = "power", pw = "infrared", dur = 120 * 35, count = true, msg = "Light Amplification Visor." },
}
W.KEYCOL = { blue = {80,120,255}, yellow = {255,220,60}, red = {255,70,60} }
W.WEAPNAME = { [1]="FIST", [2]="PISTOL", [3]="SHOTGUN", [4]="CHAINGUN",
    [5]="ROCKET", [6]="PLASMA", [7]="BFG9000", [8]="CHAINSAW", [9]="SSG" }
-- number key -> first OWNED slot in preference order (SSG over shotgun, saw over fist)
W.SLOTKEY = { [1]={8,1}, [2]={2}, [3]={9,3}, [4]={4}, [5]={5}, [6]={6}, [7]={7} }
-- HUD ammo key per weapon slot (stub until W.WEAPONS lands in the combat chunk)
W.HUDAMMOKEY = { [2]="bul", [3]="shl", [4]="bul", [5]="rck", [6]="cel", [7]="cel", [9]="shl" }
-- fallback spawn HP by sprite prefix (species without a W.MINFO entry = statues)
W.MONHP = { POSS=20, SPOS=30, TROO=60, SARG=150, HEAD=400, BOSS=1000, SKUL=100,
    CPOS=70, BOS2=1000, BSPI=500, PAIN=400, SKEL=300, FATT=600, VILE=700,
    SPID=3000, CYBR=4000, SSWV=50, KEEN=100, BBRN=250 }

----------------------------------------------------------------------
-- SECTION Hb: combat data (DOOM M_Random, monster info, weapon stats, fx sprites)
-- Ported from linuxdoom m_random.c, info.c/p_enemy.c, p_pspr.c.
----------------------------------------------------------------------
W.TIC = 1 / 35                              -- one DOOM tic in seconds
W.rndIdx = 0
W.rndtable = { 0,8,109,220,222,241,149,107,75,248,254,140,16,66,
 74,21,211,47,80,242,154,27,205,128,161,89,77,36,95,110,85,48,212,140,211,
 249,22,79,200,50,28,188,52,140,202,120,68,145,62,70,184,190,91,197,152,
 224,149,104,25,178,252,182,202,182,141,197,4,81,181,242,145,42,39,227,
 156,198,225,193,219,93,122,175,249,0,175,143,70,239,46,246,163,53,163,
 109,168,135,2,235,25,92,20,145,138,77,69,166,78,176,173,212,166,113,94,
 161,41,50,239,49,111,164,70,60,2,37,171,75,136,156,11,56,42,146,138,229,
 73,146,77,61,98,196,135,106,63,197,195,86,96,203,113,101,170,247,181,113,
 80,250,108,7,255,237,129,226,79,107,112,166,103,241,24,223,239,120,198,
 58,60,82,128,3,184,66,143,224,145,224,81,206,163,45,63,90,168,114,59,33,
 159,95,28,139,123,98,125,196,15,70,194,253,54,14,109,226,71,17,161,93,
 186,87,244,138,20,52,123,251,26,36,17,46,52,231,232,76,31,221,84,37,216,
 165,212,106,197,242,98,43,39,175,254,145,190,84,118,222,187,136,120,163,
 236,249 }
function W.pRandom() W.rndIdx = (W.rndIdx + 1) & 0xFF; return W.rndtable[W.rndIdx + 1] end

-- info.c mobjinfo (exact vanilla numbers). speed = map units per P_Move call;
-- the state chains set the call cadence, so units/sec is emergent, not stored.
-- Sound fields are lump BASE names; *N > 1 means pick base1..baseN at random
-- (A_Look / A_Scream randomize the former-human and imp barks). melee/missile
-- say which attack branches exist (both true = one shared atk chain decides).
W.MINFO = {
    POSS = { hp=20, speed=8, r=20, h=56, mass=100, pain=200, countkill=true,
        melee=false, missile=true,
        sight="DSPOSIT", sightN=3, act="DSPOSACT", psfx="DSPOPAIN", dsfx="DSPODTH", dsfxN=3 },
    SPOS = { hp=30, speed=8, r=20, h=56, mass=100, pain=170, countkill=true,
        melee=false, missile=true,
        sight="DSPOSIT", sightN=3, act="DSPOSACT", psfx="DSPOPAIN", dsfx="DSPODTH", dsfxN=3 },
    TROO = { hp=60, speed=8, r=20, h=56, mass=100, pain=200, countkill=true,
        melee=true, missile=true,
        sight="DSBGSIT", sightN=2, act="DSBGACT", psfx="DSPOPAIN", dsfx="DSBGDTH", dsfxN=2 },
    SARG = { hp=150, speed=10, r=30, h=56, mass=400, pain=180, countkill=true,
        melee=true, missile=false, atksfx="DSSGTATK",
        sight="DSSGTSIT", act="DSDMACT", psfx="DSDMPAIN", dsfx="DSSGTDTH" },
    HEAD = { hp=400, speed=8, r=31, h=56, mass=400, pain=128, countkill=true,
        melee=true, missile=true, float=true,
        sight="DSCACSIT", act="DSDMACT", psfx="DSDMPAIN", dsfx="DSCACDTH" },
    BOSS = { hp=1000, speed=8, r=24, h=64, mass=1000, pain=50, countkill=true,
        melee=true, missile=true,
        sight="DSBRSSIT", act="DSDMACT", psfx="DSDMPAIN", dsfx="DSBRSDTH" },
    BAR1 = { hp=20, speed=0, r=10, h=42, mass=100, pain=0, noblood=true },
}

-- info.c states[], one chain per (species, phase). Entry = {f=frame letter,
-- t=tics, a=action key, b=fullbright, s=sprite prefix override}. Actions run on
-- state ENTRY (P_SetMobjState). Chain-end rules (W.advMState): stnd/run loop;
-- atk/pain fall through to run; t=-1 freezes (corpse); walking PAST the end of
-- die removes the thing (the barrel explosion vanishes this way).
W.SSTATES = {
POSS = {
 stnd={{f="A",t=10,a="look"},{f="B",t=10,a="look"}},
 run={{f="A",t=4,a="chase"},{f="A",t=4,a="chase"},{f="B",t=4,a="chase"},{f="B",t=4,a="chase"},
      {f="C",t=4,a="chase"},{f="C",t=4,a="chase"},{f="D",t=4,a="chase"},{f="D",t=4,a="chase"}},
 atk={{f="E",t=10,a="face"},{f="F",t=8,a="posatk"},{f="E",t=8}},
 pain={{f="G",t=3},{f="G",t=3,a="pain"}},
 die={{f="H",t=5},{f="I",t=5,a="scream"},{f="J",t=5,a="fall"},{f="K",t=5},{f="L",t=-1}},
 xdie={{f="M",t=5},{f="N",t=5,a="xscream"},{f="O",t=5,a="fall"},{f="P",t=5},{f="Q",t=5},
       {f="R",t=5},{f="S",t=5},{f="T",t=5},{f="U",t=-1}},
},
SPOS = {
 stnd={{f="A",t=10,a="look"},{f="B",t=10,a="look"}},
 run={{f="A",t=3,a="chase"},{f="A",t=3,a="chase"},{f="B",t=3,a="chase"},{f="B",t=3,a="chase"},
      {f="C",t=3,a="chase"},{f="C",t=3,a="chase"},{f="D",t=3,a="chase"},{f="D",t=3,a="chase"}},
 atk={{f="E",t=10,a="face"},{f="F",t=10,a="sposatk",b=true},{f="E",t=10}},
 pain={{f="G",t=3},{f="G",t=3,a="pain"}},
 die={{f="H",t=5},{f="I",t=5,a="scream"},{f="J",t=5,a="fall"},{f="K",t=5},{f="L",t=-1}},
 xdie={{f="M",t=5},{f="N",t=5,a="xscream"},{f="O",t=5,a="fall"},{f="P",t=5},{f="Q",t=5},
       {f="R",t=5},{f="S",t=5},{f="T",t=5},{f="U",t=-1}},
},
TROO = {
 stnd={{f="A",t=10,a="look"},{f="B",t=10,a="look"}},
 run={{f="A",t=3,a="chase"},{f="A",t=3,a="chase"},{f="B",t=3,a="chase"},{f="B",t=3,a="chase"},
      {f="C",t=3,a="chase"},{f="C",t=3,a="chase"},{f="D",t=3,a="chase"},{f="D",t=3,a="chase"}},
 atk={{f="E",t=8,a="face"},{f="F",t=8,a="face"},{f="G",t=6,a="troopatk"}},
 pain={{f="H",t=2},{f="H",t=2,a="pain"}},
 die={{f="I",t=8},{f="J",t=8,a="scream"},{f="K",t=6},{f="L",t=6,a="fall"},{f="M",t=-1}},
 xdie={{f="N",t=5},{f="O",t=5,a="xscream"},{f="P",t=5},{f="Q",t=5,a="fall"},{f="R",t=5},
       {f="S",t=5},{f="T",t=5},{f="U",t=-1}},
},
SARG = {
 stnd={{f="A",t=10,a="look"},{f="B",t=10,a="look"}},
 run={{f="A",t=2,a="chase"},{f="A",t=2,a="chase"},{f="B",t=2,a="chase"},{f="B",t=2,a="chase"},
      {f="C",t=2,a="chase"},{f="C",t=2,a="chase"},{f="D",t=2,a="chase"},{f="D",t=2,a="chase"}},
 atk={{f="E",t=8,a="face"},{f="F",t=8,a="face"},{f="G",t=8,a="sargatk"}},
 pain={{f="H",t=2},{f="H",t=2,a="pain"}},
 die={{f="I",t=8},{f="J",t=8,a="scream"},{f="K",t=4},{f="L",t=4,a="fall"},{f="M",t=4},{f="N",t=-1}},
},
HEAD = {
 stnd={{f="A",t=10,a="look"}},
 run={{f="A",t=3,a="chase"}},
 atk={{f="B",t=5,a="face"},{f="C",t=5,a="face"},{f="D",t=5,a="headatk",b=true}},
 pain={{f="E",t=3},{f="E",t=3,a="pain"},{f="F",t=6}},
 die={{f="G",t=8},{f="H",t=8,a="scream"},{f="I",t=8},{f="J",t=8},{f="K",t=8,a="fall"},{f="L",t=-1}},
},
BOSS = {
 stnd={{f="A",t=10,a="look"},{f="B",t=10,a="look"}},
 run={{f="A",t=3,a="chase"},{f="A",t=3,a="chase"},{f="B",t=3,a="chase"},{f="B",t=3,a="chase"},
      {f="C",t=3,a="chase"},{f="C",t=3,a="chase"},{f="D",t=3,a="chase"},{f="D",t=3,a="chase"}},
 atk={{f="E",t=8,a="face"},{f="F",t=8,a="face"},{f="G",t=8,a="bruisatk"}},
 pain={{f="H",t=2},{f="H",t=2,a="pain"}},
 die={{f="I",t=8},{f="J",t=8,a="scream"},{f="K",t=8},{f="L",t=8,a="fall"},{f="M",t=8},
      {f="N",t=8},{f="O",t=-1,a="bossdeath"}},
},
BAR1 = {
 stnd={{f="A",t=6},{f="B",t=6}},
 die={{s="BEXP",f="A",t=5,b=true},{s="BEXP",f="B",t=5,b=true,a="scream"},
      {s="BEXP",f="C",t=5,b=true},{s="BEXP",f="D",t=10,b=true,a="explode"},
      {s="BEXP",f="E",t=10,b=true}},
},
}

-- 8-direction movement tables (p_enemy.c dirtype). movedir 0..7 = E,NE,N,NW,W,SW,S,SE;
-- 8 = DI_NODIR. Diagonal step = vanilla 47000/65536 (slightly over cos45, a quirk
-- kept on purpose). DIRDEG is the facing angle for sprite rotation.
W.DIRX = { 1, 0.7172, 0, -0.7172, -1, -0.7172, 0, 0.7172 }
W.DIRY = { 0, 0.7172, 1, 0.7172, 0, -0.7172, -1, -0.7172 }
W.DIRDEG = { 0, 45, 90, 135, 180, 225, 270, 315 }
W.OPPOSITE = { [0]=4, [1]=5, [2]=6, [3]=7, [4]=0, [5]=1, [6]=2, [7]=3, [8]=8 }
W.DIAGS = { 3, 1, 5, 7 }        -- NW,NE,SW,SE, indexed ((dy<0)<<1)+(dx>0) + 1

-- Pick a possibly-randomized sound lump: base name + 1-based variant suffix when
-- the species has N variants (posit/bgsit/podth/bgdth), else the base name as-is.
function W.sndPick(base, n)
    if not base then return nil end
    if n and n > 1 then return base .. (1 + W.pRandom() % n) end
    return base
end

-- Weapon psprite states (info.c). Named flat table, next-pointers by name; a
-- t=0 state runs its action and falls straight through to nx (P_SetPsprite's
-- zero-tic cycle), which is how the chaingun re-fire and LIGHTDONE work.
W.WSTATES = {
    LIGHTDONE  ={spr="SHTG",f="E",t=0,a="light0"},
    PUNCH      ={spr="PUNG",f="A",t=1,a="ready",nx="PUNCH"},
    PUNCHDOWN  ={spr="PUNG",f="A",t=1,a="lower",nx="PUNCHDOWN"},
    PUNCHUP    ={spr="PUNG",f="A",t=1,a="raise",nx="PUNCHUP"},
    PUNCH1     ={spr="PUNG",f="B",t=4,nx="PUNCH2"},
    PUNCH2     ={spr="PUNG",f="C",t=4,a="punch",nx="PUNCH3"},
    PUNCH3     ={spr="PUNG",f="D",t=5,nx="PUNCH4"},
    PUNCH4     ={spr="PUNG",f="C",t=4,nx="PUNCH5"},
    PUNCH5     ={spr="PUNG",f="B",t=5,a="refire",nx="PUNCH"},
    PISTOL     ={spr="PISG",f="A",t=1,a="ready",nx="PISTOL"},
    PISTOLDOWN ={spr="PISG",f="A",t=1,a="lower",nx="PISTOLDOWN"},
    PISTOLUP   ={spr="PISG",f="A",t=1,a="raise",nx="PISTOLUP"},
    PISTOL1    ={spr="PISG",f="A",t=4,nx="PISTOL2"},
    PISTOL2    ={spr="PISG",f="B",t=6,a="firepistol",nx="PISTOL3"},
    PISTOL3    ={spr="PISG",f="C",t=4,nx="PISTOL4"},
    PISTOL4    ={spr="PISG",f="B",t=5,a="refire",nx="PISTOL"},
    PISTOLFLASH={spr="PISF",f="A",t=7,b=true,a="light1",nx="LIGHTDONE"},
    SGUN       ={spr="SHTG",f="A",t=1,a="ready",nx="SGUN"},
    SGUNDOWN   ={spr="SHTG",f="A",t=1,a="lower",nx="SGUNDOWN"},
    SGUNUP     ={spr="SHTG",f="A",t=1,a="raise",nx="SGUNUP"},
    SGUN1      ={spr="SHTG",f="A",t=3,nx="SGUN2"},
    SGUN2      ={spr="SHTG",f="A",t=7,a="fireshotgun",nx="SGUN3"},
    SGUN3      ={spr="SHTG",f="B",t=5,nx="SGUN4"},
    SGUN4      ={spr="SHTG",f="C",t=5,nx="SGUN5"},
    SGUN5      ={spr="SHTG",f="D",t=4,nx="SGUN6"},
    SGUN6      ={spr="SHTG",f="C",t=5,nx="SGUN7"},
    SGUN7      ={spr="SHTG",f="B",t=5,nx="SGUN8"},
    SGUN8      ={spr="SHTG",f="A",t=3,nx="SGUN9"},
    SGUN9      ={spr="SHTG",f="A",t=7,a="refire",nx="SGUN"},
    SGUNFLASH1 ={spr="SHTF",f="A",t=4,b=true,a="light1",nx="SGUNFLASH2"},
    SGUNFLASH2 ={spr="SHTF",f="B",t=3,b=true,a="light2",nx="LIGHTDONE"},
    DSGUN      ={spr="SHT2",f="A",t=1,a="ready",nx="DSGUN"},
    DSGUNDOWN  ={spr="SHT2",f="A",t=1,a="lower",nx="DSGUNDOWN"},
    DSGUNUP    ={spr="SHT2",f="A",t=1,a="raise",nx="DSGUNUP"},
    DSGUN1     ={spr="SHT2",f="A",t=3,nx="DSGUN2"},
    DSGUN2     ={spr="SHT2",f="A",t=7,a="fireshotgun2",nx="DSGUN3"},
    DSGUN3     ={spr="SHT2",f="B",t=7,nx="DSGUN4"},
    DSGUN4     ={spr="SHT2",f="C",t=7,a="checkreload",nx="DSGUN5"},
    DSGUN5     ={spr="SHT2",f="D",t=7,a="opensg2",nx="DSGUN6"},
    DSGUN6     ={spr="SHT2",f="E",t=7,nx="DSGUN7"},
    DSGUN7     ={spr="SHT2",f="F",t=7,a="loadsg2",nx="DSGUN8"},
    DSGUN8     ={spr="SHT2",f="G",t=6,nx="DSGUN9"},
    DSGUN9     ={spr="SHT2",f="H",t=6,a="closesg2",nx="DSGUN10"},
    DSGUN10    ={spr="SHT2",f="A",t=5,a="refire",nx="DSGUN"},
    DSGUNFLASH1={spr="SHT2",f="I",t=5,b=true,a="light1",nx="DSGUNFLASH2"},
    DSGUNFLASH2={spr="SHT2",f="J",t=4,b=true,a="light2",nx="LIGHTDONE"},
    CHAIN      ={spr="CHGG",f="A",t=1,a="ready",nx="CHAIN"},
    CHAINDOWN  ={spr="CHGG",f="A",t=1,a="lower",nx="CHAINDOWN"},
    CHAINUP    ={spr="CHGG",f="A",t=1,a="raise",nx="CHAINUP"},
    CHAIN1     ={spr="CHGG",f="A",t=4,a="firecgun",nx="CHAIN2"},
    CHAIN2     ={spr="CHGG",f="B",t=4,a="firecgun",nx="CHAIN3"},
    CHAIN3     ={spr="CHGG",f="B",t=0,a="refire",nx="CHAIN"},
    CHAINFLASH1={spr="CHGF",f="A",t=5,b=true,a="light1",nx="LIGHTDONE"},
    CHAINFLASH2={spr="CHGF",f="B",t=5,b=true,a="light2",nx="LIGHTDONE"},
    MISSILE    ={spr="MISG",f="A",t=1,a="ready",nx="MISSILE"},
    MISSILEDOWN={spr="MISG",f="A",t=1,a="lower",nx="MISSILEDOWN"},
    MISSILEUP  ={spr="MISG",f="A",t=1,a="raise",nx="MISSILEUP"},
    MISSILE1   ={spr="MISG",f="B",t=8,a="gunflash",nx="MISSILE2"},
    MISSILE2   ={spr="MISG",f="B",t=12,a="firemissile",nx="MISSILE3"},
    MISSILE3   ={spr="MISG",f="B",t=0,a="refire",nx="MISSILE"},
    MISSILEFLASH1={spr="MISF",f="A",t=3,b=true,a="light1",nx="MISSILEFLASH2"},
    MISSILEFLASH2={spr="MISF",f="B",t=4,b=true,nx="MISSILEFLASH3"},
    MISSILEFLASH3={spr="MISF",f="C",t=4,b=true,a="light2",nx="MISSILEFLASH4"},
    MISSILEFLASH4={spr="MISF",f="D",t=4,b=true,a="light2",nx="LIGHTDONE"},
    SAW        ={spr="SAWG",f="C",t=4,a="ready",nx="SAWB"},
    SAWB       ={spr="SAWG",f="D",t=4,a="ready",nx="SAW"},
    SAWDOWN    ={spr="SAWG",f="C",t=1,a="lower",nx="SAWDOWN"},
    SAWUP      ={spr="SAWG",f="C",t=1,a="raise",nx="SAWUP"},
    SAW1       ={spr="SAWG",f="A",t=4,a="saw",nx="SAW2"},
    SAW2       ={spr="SAWG",f="B",t=4,a="saw",nx="SAW3"},
    SAW3       ={spr="SAWG",f="B",t=0,a="refire",nx="SAW"},
    PLASMA     ={spr="PLSG",f="A",t=1,a="ready",nx="PLASMA"},
    PLASMADOWN ={spr="PLSG",f="A",t=1,a="lower",nx="PLASMADOWN"},
    PLASMAUP   ={spr="PLSG",f="A",t=1,a="raise",nx="PLASMAUP"},
    PLASMA1    ={spr="PLSG",f="A",t=3,a="fireplasma",nx="PLASMA2"},
    PLASMA2    ={spr="PLSG",f="B",t=20,a="refire",nx="PLASMA"},
    PLASMAFLASH1={spr="PLSF",f="A",t=4,b=true,a="light1",nx="LIGHTDONE"},
    PLASMAFLASH2={spr="PLSF",f="B",t=4,b=true,a="light1",nx="LIGHTDONE"},
    BFG        ={spr="BFGG",f="A",t=1,a="ready",nx="BFG"},
    BFGDOWN    ={spr="BFGG",f="A",t=1,a="lower",nx="BFGDOWN"},
    BFGUP      ={spr="BFGG",f="A",t=1,a="raise",nx="BFGUP"},
    BFG1       ={spr="BFGG",f="A",t=20,a="bfgsound",nx="BFG2"},
    BFG2       ={spr="BFGG",f="B",t=10,a="gunflash",nx="BFG3"},
    BFG3       ={spr="BFGG",f="B",t=10,a="firebfg",nx="BFG4"},
    BFG4       ={spr="BFGG",f="B",t=20,a="refire",nx="BFG"},
    BFGFLASH1  ={spr="BFGF",f="A",t=11,b=true,a="light1",nx="BFGFLASH2"},
    BFGFLASH2  ={spr="BFGF",f="B",t=6,b=true,a="light2",nx="LIGHTDONE"},
}

-- d_items.c weaponinfo: ammo type, per-shot cost, psprite entry states.
W.WEAPONS = {
    [1] = { name="FIST",     ammo=nil,   up="PUNCHUP",   down="PUNCHDOWN",   ready="PUNCH",   atk="PUNCH1" },
    [2] = { name="PISTOL",   ammo="bul", up="PISTOLUP",  down="PISTOLDOWN",  ready="PISTOL",  atk="PISTOL1",  flash="PISTOLFLASH" },
    [3] = { name="SHOTGUN",  ammo="shl", up="SGUNUP",    down="SGUNDOWN",    ready="SGUN",    atk="SGUN1",    flash="SGUNFLASH1" },
    [4] = { name="CHAINGUN", ammo="bul", up="CHAINUP",   down="CHAINDOWN",   ready="CHAIN",   atk="CHAIN1",   flash="CHAINFLASH1", flash2="CHAINFLASH2" },
    [5] = { name="ROCKET",   ammo="rck", up="MISSILEUP", down="MISSILEDOWN", ready="MISSILE", atk="MISSILE1", flash="MISSILEFLASH1" },
    [6] = { name="PLASMA",   ammo="cel", up="PLASMAUP",  down="PLASMADOWN",  ready="PLASMA",  atk="PLASMA1",  flash="PLASMAFLASH1", flash2="PLASMAFLASH2" },
    [7] = { name="BFG9000",  ammo="cel", cost=40, up="BFGUP", down="BFGDOWN", ready="BFG",    atk="BFG1",     flash="BFGFLASH1" },
    [8] = { name="CHAINSAW", ammo=nil,   up="SAWUP",     down="SAWDOWN",     ready="SAW",     atk="SAW1" },
    [9] = { name="SSG",      ammo="shl", cost=2, up="DSGUNUP", down="DSGUNDOWN", ready="DSGUN", atk="DSGUN1", flash="DSGUNFLASH1" },
}

-- Synthetic THING_SPR id (never in a WAD) for pooled fx + projectiles: r=nil so
-- they never block movement; drawn via the normal sprite path (th.spr overrides).
W.THING_SPR[30040] = { spr="MISL", seq="A", rot=false, kind="fx" }

-- Missiles (info.c mobjinfo, exact). speed = units per TIC (fracunits/tic).
-- dmg = the direct-hit multiplier ((P_Random%8+1)*dmg). splash = A_Explode
-- radius+damage (rockets only; the BFG ball sprays tracers instead, see
-- W.bfgSpray). fly/boom = sprite frames + per-frame tics (all fullbright).
-- r = missile radius (added to the target radius for the contact test).
W.PROJ = {
    ROCKET      = { flySpr="MISL", fly="A",  flyT=1, boomSpr="MISL", boom="BCD",    boomT={8,6,4},
        speed=20, r=11, splash=128, seesfx="DSRLAUNC", dsfx="DSBAREXP", dmg=20 },
    PLASMA      = { flySpr="PLSS", fly="AB", flyT=6, boomSpr="PLSE", boom="ABCDE",  boomT=4,
        speed=25, r=13, splash=0,   seesfx="DSPLASMA", dsfx="DSFIRXPL", dmg=5 },
    BFG         = { flySpr="BFS1", fly="AB", flyT=4, boomSpr="BFE1", boom="ABCDEF", boomT=8,
        speed=25, r=13, splash=0,   spray=true,        dsfx="DSRXPLOD", dmg=100 },
    TROOPSHOT   = { flySpr="BAL1", fly="AB", flyT=4, boomSpr="BAL1", boom="CDE",    boomT=6,
        speed=10, r=6,  splash=0,   seesfx="DSFIRSHT", dsfx="DSFIRXPL", dmg=3 },
    HEADSHOT    = { flySpr="BAL2", fly="AB", flyT=4, boomSpr="BAL2", boom="CDE",    boomT=6,
        speed=10, r=6,  splash=0,   seesfx="DSFIRSHT", dsfx="DSFIRXPL", dmg=5 },
    BRUISERSHOT = { flySpr="BAL7", fly="AB", flyT=4, boomSpr="BAL7", boom="CDE",    boomT=6,
        speed=15, r=6,  splash=0,   seesfx="DSFIRSHT", dsfx="DSFIRXPL", dmg=8 },
}

-- H.2b: build an 8-slot frame/rotation index from the sprite namespace once.
-- Lump name = NAME(4) + frame(A-Z) + rot(0-8), optionally a mirrored second pair.
-- rot 0 = one image for all view angles; the two-pair form (e.g. TROOA2A8) reuses
-- one image for two rotations, the second MIRRORED.
function W.buildSpriteFrames()
    W.spriteFrames = {}
    if not W.spriteLump then return end
    for name in pairs(W.spriteLump) do
        if #name >= 6 then
            local pref = name:sub(1, 4)
            local fr = W.spriteFrames[pref]
            if not fr then fr = {}; W.spriteFrames[pref] = fr end
            local function put(fl, rd, mirror)
                if rd == 0 then
                    local e = fr[fl]; if not e then e = { lump = {}, flip = {} }; fr[fl] = e end
                    e.rot0 = name
                elseif rd >= 1 and rd <= 8 then
                    local e = fr[fl]; if not e then e = { lump = {}, flip = {} }; fr[fl] = e end
                    e.lump[rd] = name; e.flip[rd] = mirror; e.rotate = true
                end
            end
            put(name:sub(5, 5), tonumber(name:sub(6, 6)) or -1, false)
            if #name >= 8 then put(name:sub(7, 7), tonumber(name:sub(8, 8)) or -1, true) end
        end
    end
end

-- H.2c: resolve a lump name + mirror flag for (prefix, frameLetter, rot 1..8).
-- Fallbacks cover a missing rotation (rot-0 image, then any present rotation).
function W.spriteFrameLump(spr, fl, rot)
    local fr = W.spriteFrames and W.spriteFrames[spr]; if not fr then return nil end
    local e = fr[fl]; if not e then return nil end
    if not e.rotate then return (e.rot0 or e.lump[1]), false end
    local nm = e.lump[rot]; if nm then return nm, e.flip[rot] or false end
    if e.rot0 then return e.rot0, false end
    for r = 1, 8 do if e.lump[r] then return e.lump[r], e.flip[r] or false end end
    return nil
end

-- H.3: single-patch composite WITH alpha (0 untouched -> transparent, 255 drawn).
-- Mirrors W.compositeTexture, but for one sprite lump.
function W.spriteRGBA(name)
    local ord = W.spriteLump and W.spriteLump[name]
    local data = W.lumpBytes(ord); if #data < 8 then return nil end
    local w, h, cols = W.patchColumns(data); if not w then return nil end
    local total = w * h; local idx, alpha = {}, {}
    for k = 0, total - 1 do alpha[k] = 0 end
    for px = 0, w - 1 do
        local posts = cols[px]
        if posts then
            for _, post in ipairs(posts) do
                local pix, tp = post.pix, post.top
                for i = 1, #pix do
                    local sy = tp + (i - 1)
                    if sy >= 0 and sy < h then local kk = sy * w + px; idx[kk] = pix:byte(i); alpha[kk] = 255 end
                end
            end
        end
    end
    local out, pal = {}, W.pal
    for k = 0, total - 1 do
        if alpha[k] == 255 then
            local c = pal[idx[k]] or { 0, 0, 0 }
            out[k + 1] = string.char(c[1], c[2], c[3], 255)
        else
            out[k + 1] = "\0\0\0\0"
        end
    end
    return table.concat(out), w, h
end

-- H.3: sprite meta {tex, w, h, xoff(leftOffset), yoff(topOffset)} or nil. The
-- {w,h,xoff,yoff} come from a cheap 4-int header read (NOT budget-gated) so
-- projection can run with a placeholder before the GPU texture is ready.
function W.spriteTex(name)
    if not name or not W.pal then return nil end
    W.spriteMeta = W.spriteMeta or {}
    local meta = W.spriteMeta[name]
    if meta == nil then
        local data = W.lumpBytes(W.spriteLump and W.spriteLump[name])
        if #data < 8 then W.spriteMeta[name] = false; return nil end
        local w, h, lo, to = string.unpack("<i2i2i2i2", data, 1)
        if w <= 0 or h <= 0 or w > 4096 or h > 4096 then W.spriteMeta[name] = false; return nil end
        meta = { w = w, h = h, xoff = lo, yoff = to }
        W.spriteMeta[name] = meta
    end
    if meta == false then return nil end
    if W.cacheDir then meta.tex = W.spriteGpu(name) else meta.tex = nil end
    return meta
end

-- H.3: async GPU upload of a sprite, keyed "SP:" in the shared texCache, gated by
-- the shared per-frame bake budget. Clone of W.getTex's bake/poll path.
function W.spriteGpu(name)
    local key = "SP:" .. name
    W.texCache = W.texCache or {}
    local c = W.texCache[key]
    if c == nil then
        if (W.bakeUsed or 0) >= (W.BAKE_BUDGET or 4) then return nil end
        W.bakeUsed = (W.bakeUsed or 0) + 1
        local fn = key:gsub("[^%w_%-]", function(ch) return string.format("$%02X", ch:byte()) end) .. ".png"
        local path = W.cacheDir .. "/" .. fn
        local exists = false
        local dok, de = pcall(FileMgr.DoesFileExist, path); if dok then exists = de end
        local sw, sh
        if not exists then
            local rgba, w, h = W.spriteRGBA(name)
            if not rgba then W.texCache[key] = { state = "fail" }; return nil end
            local pok, png = pcall(W.encodePNG, rgba, w, h)
            if not pok or not png then W.texCache[key] = { state = "fail" }; return nil end
            if not W.writeBytes(path, png) then W.texCache[key] = { state = "fail" }; return nil end
            sw, sh = w, h
        else
            local m = W.spriteMeta[name]; sw, sh = m.w, m.h
        end
        local id
        local lok, lid = pcall(Texture.LoadTexture, path); if lok then id = lid end
        if not id then W.texCache[key] = { state = "fail" }; return nil end
        W.texCache[key] = { id = id, state = "pending", w = sw, h = sh }
        return nil
    end
    if c.state == "fail" then return nil end
    if c.state == "pending" then
        local vok, valid = pcall(Texture.IsTextureValid, c.id); if not (vok and valid) then return nil end
        local tok, tex = pcall(Texture.GetTexture, c.id); if not (tok and tex) then return nil end
        c.tex = tex; c.state = "ready"
    end
    if c.state == "ready" and c.tex then
        local gok, handle = pcall(function() return c.tex:GetCurrent() end)
        if gok and handle then return handle end
    end
    return nil
end

-- Build the per-column sprite clip window (mfloorclip/mceilingclip) over columns
-- [cL,cR] for a sprite at inverse depth invD (=1/depth). Walks the drawseg list
-- far->near; the FIRST seg that both is in front of the sprite (its per-column
-- 1/depth > invD) and actually recorded that column wins it, and its snapshot is
-- the cumulative clip window there (ceilclip=top, floorclip=bottom). Because the
-- record order is near->far, the first winner in a far->near sweep is the FARTHEST
-- in-front seg, whose cumulative snapshot already folds in every nearer occluder.
-- clipTop/clipBot are left at -1 where nothing in front occludes (no clip).
function W.buildSpriteClip(cL, cR, invD)
    local ctop, cbot, ds = W.clipTop, W.clipBot, W.dsPool
    for c = cL, cR do ctop[c] = -1; cbot[c] = -1 end
    for di = W.dsCount, 1, -1 do                          -- far -> near
        local d = ds[di]
        local dcL, dcR = d.colL, d.colR
        if dcR >= cL and dcL <= cR then                  -- horizontal overlap
            local dw = dcR - dcL
            local ivL = d.invL
            local ivStep = (dw > 0) and ((d.invR - ivL) / dw) or 0
            local dtop, dbot = d.top, d.bot
            local a = (cL > dcL) and cL or dcL
            local b = (cR < dcR) and cR or dcR
            for c = a, b do
                if ctop[c] < 0 then                      -- scratch still unset here
                    if ivL + ivStep * (c - dcL) > invD then   -- seg in front of the sprite
                        local k = c - dcL
                        local vt = dtop[k]
                        if vt >= 0 then                  -- seg actually recorded this column
                            ctop[c] = vt
                            cbot[c] = dbot[k]
                        end
                    end
                end
            end
        end
    end
end

-- H.6: project + draw one thing as a billboard, per-column silhouette-clipped by
-- the drawseg list (W.buildSpriteClip): full walls hide the whole column, portals
-- clip the sprite to the cumulative opening. depth (= thing-center forward
-- distance) is treated constant over the whole billboard, so scale + z-test are
-- per-thing (matches DOOM).
function W.drawThing(th, e, depth)
    local fl = th.frame or e.seq:sub(1, 1)             -- actor state can override the frame
    local rotal = (th.rot ~= nil) and th.rot or e.rot  -- and the directional flag
    local spr = th.spr or e.spr                        -- projectiles swap prefix (fly -> boom)
    local lump, mirror
    if rotal then
        local ang = (atan(th.y - W.viewY, th.x - W.viewX) - math.rad(th.angle) + 9 * pi / 8) % TWO_PI
        lump, mirror = W.spriteFrameLump(spr, fl, (floor(ang / (pi / 4)) % 8) + 1)
    else
        lump, mirror = W.spriteFrameLump(spr, fl, 1)
    end
    if not lump then return end
    local meta = W.spriteTex(lump); if not meta then return end
    -- projection (H.5)
    local dx, dy = th.x - W.viewX, th.y - W.viewY
    local lateral = dx * W.sinA - dy * W.cosA
    local scale = W.projScale / depth
    local screenXc = W.centerX + lateral * scale
    local sec = W.sectorAt(th.x, th.y)
    local anchorZ
    if th.z then anchorZ = th.z                        -- live actor feet height
    elseif e.hang then anchorZ = (sec and sec.ceil or 0) - meta.h
    else anchorZ = (sec and sec.floor or 0) end
    local worldTop = anchorZ + meta.yoff
    local worldBot = worldTop - meta.h
    local yTop = W.horizon - (worldTop - W.viewZ) * scale
    local yBot = W.horizon - (worldBot - W.viewZ) * scale
    local sprW = meta.w * scale
    local xLeft = screenXc - meta.xoff * scale
    local xRight = xLeft + sprW
    if xRight <= 0 or xLeft >= W.viewW then return end
    if sprW <= 0 then return end
    -- shade: sector light x distance, same curve as planes; fullbright frames
    -- (muzzle fx, fireballs, explosions, strobing attack frames) skip the shade
    local br = W.planeLight(sec and sec.light or 160, depth)
    local tint = th.bright and 0xFFFFFFFF or W.greyTint(br)
    local colW = W.colW
    local cL = clamp(floor(xLeft / colW), 0, W.RW - 1)
    local cR = clamp(floor((xRight - 1e-4) / colW), 0, W.RW - 1)
    local spanH = yBot - yTop                    -- sprite full screen height (>0)
    -- Per-column silhouette clip from the drawseg list. depth is the constant
    -- thing-center forward distance, so the whole billboard z-tests at one depth.
    W.buildSpriteClip(cL, cR, 1 / depth)
    local ctop, cbot, viewH = W.clipTop, W.clipBot, W.viewH
    -- Runs merge only while BOTH clip edges match, so an unclipped sprite is still
    -- ONE draw; only actually-clipped columns fragment. The clip changes the drawn
    -- min_y/max_y AND the uv v-range (v is affine in screen y over [yTop,yBot]).
    local run, runYT, runYB = -1, 0, 0
    local function flush(cEnd)
        if run < 0 then return end
        local rxL = max(xLeft, run * colW)
        local rxR = min(xRight, (cEnd + 1) * colW)
        if rxR > rxL and runYB > runYT then
            local u0 = (rxL - xLeft) / sprW
            local u1 = (rxR - xLeft) / sprW
            if mirror then u0, u1 = 1 - u0, 1 - u1 end
            local v0 = (spanH > 0) and ((runYT - yTop) / spanH) or 0
            local v1 = (spanH > 0) and ((runYB - yTop) / spanH) or 1
            -- half-texel inset: sample texel centers at the sprite edges so the top/
            -- bottom/side rows do not bleed a stray line at the quad boundary.
            local uw, vh = 0.5 / meta.w, 0.5 / meta.h
            if u0 < uw then u0 = uw elseif u0 > 1 - uw then u0 = 1 - uw end
            if u1 < uw then u1 = uw elseif u1 > 1 - uw then u1 = 1 - uw end
            if v0 < vh then v0 = vh end
            if v1 > 1 - vh then v1 = 1 - vh end
            if meta.tex then
                ImGui.AddImage(meta.tex, rxL, runYT, rxR, runYB, u0, v0, u1, v1, tint)
            elseif W.SPRITE_PLACEHOLDER then
                local col = W.KINDCOL[e.kind] or W.KINDCOL.decor
                ImGui.AddRectFilled(rxL, runYT, rxR, runYB, ci(col[1] * br), ci(col[2] * br), ci(col[3] * br), 110)
            end
            W.spriteDraws = W.spriteDraws + 1     -- one charge per emitted run (matches old)
        end
        run = -1
    end
    for c = cL, cR do
        if W.spriteDraws >= W.SPRITE_BUDGET then flush(c - 1); break end
        local ct = ctop[c]; if ct < 0 then ct = 0 end         -- unset -> no ceiling clip
        local cb = cbot[c]; if cb < 0 then cb = viewH end      -- unset -> no floor clip
        local yDT = (yTop > ct) and yTop or ct                -- max(yTop, clipTop)
        local yDB = (yBot < cb) and yBot or cb                -- min(yBot, clipBot)
        if yDB > yDT then                        -- at least partly visible
            if run < 0 then
                run, runYT, runYB = c, yDT, yDB
            elseif yDT ~= runYT or yDB ~= runYB then
                flush(c - 1); run, runYT, runYB = c, yDT, yDB
            end                                  -- else same clip -> extend run
        else
            flush(c - 1)
            W.spriteOccl = (W.spriteOccl or 0) + 1
        end
    end
    flush(cR)
end

-- Draw one masked mid texture (a two-sided line's middle texture: grates,
-- fences, cage bars). Deferred from the wall pass and drawn here in the sorted
-- masked pass so sprites BEHIND it were already painted (they show through the
-- texture's transparent holes) and sprites in front paint over it. Per column:
-- project the one-texture-tall band (masked mids never tile vertically), clip
-- to the drawseg's recorded opening snapshot (which already folds in every
-- nearer occluder), and emit a single CLAMP-safe AddImage (v stays in [0,1]).
function W.drawMaskedSeg(d)
    local tex, texW = d.mid, d.midW
    local colL = d.colL
    local dsTop, dsBot = d.top, d.bot
    local sxA, sxB = d.midSxA, d.midSxB
    local invA, invB = d.midInvA, d.midInvB
    local uozA, uozB = d.midUozA, d.midUozB
    local hTop, hBot = d.midHTop, d.midHBot
    local fs, seg = d.midFs, d.midSeg
    local horizon, projScale, viewZ, colW = W.horizon, W.projScale, W.viewZ, W.colW
    local sxSpan = sxB - sxA
    if sxSpan <= 0 then return end
    for col = colL, d.colR do
        local ct = dsTop[col - colL]
        if ct and ct >= 0 then
            local cb = dsBot[col - colL]
            if cb > ct then
                local t = clamp(((col + 0.5) * colW - sxA) / sxSpan, 0, 1)
                local inv = invA + (invB - invA) * t
                local yT = horizon - (hTop - viewZ) * projScale * inv
                local yB = horizon - (hBot - viewZ) * projScale * inv
                local y0 = (yT > ct) and yT or ct        -- max(band top, window top)
                local y1 = (yB < cb) and yB or cb        -- min(band bot, window bot)
                if y1 > y0 and yB > yT then
                    local distU = (uozA + (uozB - uozA) * t) / inv
                    local u = (floor((d.midUOff + distU) % texW) + 0.5) / texW
                    local x0 = col * colW
                    ImGui.AddImage(tex, x0, y0, x0 + colW + 0.8, y1,
                        u, (y0 - yT) / (yB - yT), u, (y1 - yT) / (yB - yT),
                        W.greyTint(W.wallLight(fs, 1 / inv, seg)))
                end
            end
        end
    end
end

-- H.6: collect visible/in-range things, depth-sort far->near, draw the nearest
-- SPRITE_MAX under the per-frame SPRITE_BUDGET. Scratch is reused (no per-frame
-- alloc for the collect list; the sort view is small and bounded). Masked mid
-- walls (see W.drawMaskedSeg) are merged into the same far->near paint order.
function W.renderThings()
    if not (W.map and W.map.things and W.pal) then return end
    W.spriteDraws = 0
    W.spriteOccl = 0
    local list = W.thingScratch or {}; W.thingScratch = list
    local n = 0
    for _, th in ipairs(W.map.things) do
        local e = W.THING_SPR[th.dtype]
        if e and (th.flags & 0x0010) == 0 and not th.removed then
            local dx, dy = th.x - W.viewX, th.y - W.viewY
            local depth = dx * W.cosA + dy * W.sinA
            if depth > W.NEARZ and (dx * dx + dy * dy) <= W.SPRITE_MAXDIST2 then
                n = n + 1; local r = list[n]; if not r then r = {}; list[n] = r end
                r.th = th; r.e = e; r.depth = depth
            end
        end
    end
    local view = W.thingView or {}; W.thingView = view
    for i = 1, n do view[i] = list[i] end
    for i = n + 1, #view do view[i] = nil end
    table.sort(view, function(a, b) return a.depth > b.depth end)
    local startI = 1
    if n > W.SPRITE_MAX then startI = n - W.SPRITE_MAX + 1 end
    -- Collect this frame's masked mid walls and sort them far->near too.
    local ms = W.msScratch or {}; W.msScratch = ms
    local mn = 0
    for di = 1, W.dsCount do
        local d = W.dsPool[di]
        if d.mid then mn = mn + 1; ms[mn] = d end
    end
    for i = mn + 1, #ms do ms[i] = nil end
    if mn > 1 then table.sort(ms, function(a, b) return a.midDepth > b.midDepth end) end
    -- Merge-walk both far->near streams so nearer items always paint later.
    -- Masked walls ignore the sprite budget (they are world geometry): once the
    -- budget is gone sprites are skipped but the walls still draw.
    local si, mi = startI, 1
    while si <= n or mi <= mn do
        local sv = (si <= n) and view[si] or nil
        if mi <= mn and (not sv or ms[mi].midDepth >= sv.depth) then
            W.drawMaskedSeg(ms[mi]); mi = mi + 1
        else
            if W.spriteDraws < W.SPRITE_BUDGET then
                W.drawThing(sv.th, sv.e, sv.depth)
            end
            si = si + 1
        end
    end
end

----------------------------------------------------------------------
-- SECTION I: player spawn, sector lookup, floor follow, collision
----------------------------------------------------------------------
-- Walk the BSP to the leaf subsector containing (x,y).
function W.pointInSubsector(x, y)
    local ref = W.map.rootNode
    -- A valid BSP walk visits each node at most once; cap the descent so a cyclic
    -- or garbage NODES lump (from a malformed PWAD) cannot hang the render thread.
    local guard = #W.map.nodes + 1
    while (ref & SUBSECTOR_BIT) == 0 do             -- node indices are < 0x8000
        local nd = W.map.nodes[ref + 1]
        if not nd then break end
        guard = guard - 1
        if guard < 0 then break end
        local side = W.pointOnSide(x, y, nd)
        ref = (side == 0) and nd.rchild or nd.lchild
    end
    return ref & (SUBSECTOR_BIT - 1)
end

-- subsector -> sector, resolved lazily and cached (no edit to Phase-1 loadMap).
function W.subsectorSector(map, ssIdx)
    map.ssSec = map.ssSec or {}
    local s = map.ssSec[ssIdx]
    if s == nil then
        s = false
        local ss = map.ssectors[ssIdx + 1]
        if ss then
            for k = 0, ss.segCount - 1 do
                local seg = map.segs[ss.firstSeg + k + 1]
                if seg and seg.frontSector then s = seg.frontSector; break end
            end
        end
        map.ssSec[ssIdx] = s
    end
    if s == false then return nil end
    return map.sectors[s + 1]
end

function W.sectorAt(x, y)
    if not (W.map and W.map.rootNode) then return nil end
    return W.subsectorSector(W.map, W.pointInSubsector(x, y))
end

function W.spawnPlayer(map)
    W.map = map
    W.nodeMax = (map.nodes and #map.nodes + 8) or 8192
    local start
    for _, th in ipairs(map.things) do
        if th.dtype == 1 then start = th; break end
    end
    if not start then
        W.gameState = "error"; W.status = "no player start (THING type 1)"
        return false
    end
    W.viewX = start.x; W.viewY = start.y
    W.viewAngle = math.rad(start.angle)
    W.momx = 0; W.momy = 0; W.momz = 0      -- vanilla momentum state (units/tic)
    W.pz = W.floorZAt(W.viewX, W.viewY)     -- feet height
    W.viewheight = 41; W.dvh = 0; W.bob = 0
    W.viewZ = W.pz + W.viewheight
    W.reactionTics = 0
    W.attacker = nil
    W.extralight = 0
    W.usePressed = false
    W.activeSectors = {}                    -- in-progress door/sector movements
    W.spawnSpecials(map)                     -- arm light/damage/secret specials + tic clock
    if W.health == nil then W.newGame() end -- first level of a fresh game
    W.playerDead = false
    W.damageCount = 0; W.bonusCount = 0
    if W.health <= 0 then W.newGame() end
    -- psprites: raise the current weapon from the bottom (P_SetupPsprites)
    W.psp = { st = nil, tics = -1, sx = 1, sy = 32 }
    W.psf = { st = nil, tics = -1 }
    W.attackdown = false; W.refire = 0
    W.pendingWeapon = W.pendingWeapon or W.curWeapon
    W.bringUpWeapon()
    W.stInit()
    W.oldPX = W.viewX; W.oldPY = W.viewY; W.oldVZ = W.viewZ   -- interp: no glide on spawn
    W.spawnActors(map)                      -- live monsters/barrels + pickup index
    return true
end

-- P_PointOnLineSide: which side of the infinite line (through v1, direction ld)
-- point (x,y) lies on. 0 = front, 1 = back (cross-product sign, matches DOOM).
local function pointOnLineSide(x, y, v1x, v1y, ldx, ldy)
    if ldy * (x - v1x) > (y - v1y) * ldx then return 0 else return 1 end
end

-- P_BoxOnLineSide: is the axis-aligned box wholly on one side of the line (0/1),
-- or does it cross it (-1)? The tested corner pair keys off the line slope (DOOM).
local function boxOnLineSide(bl, br, bb, bt, v1x, v1y, ldx, ldy)
    local p1, p2
    if ldy == 0 then                                 -- horizontal line
        p1 = (bt > v1y) and 1 or 0; p2 = (bb > v1y) and 1 or 0
        if ldx < 0 then p1 = 1 - p1; p2 = 1 - p2 end
    elseif ldx == 0 then                             -- vertical line
        p1 = (br < v1x) and 1 or 0; p2 = (bl < v1x) and 1 or 0
        if ldy < 0 then p1 = 1 - p1; p2 = 1 - p2 end
    elseif (ldx > 0) == (ldy > 0) then               -- positive slope
        p1 = pointOnLineSide(bl, bt, v1x, v1y, ldx, ldy)
        p2 = pointOnLineSide(br, bb, v1x, v1y, ldx, ldy)
    else                                             -- negative slope
        p1 = pointOnLineSide(br, bt, v1x, v1y, ldx, ldy)
        p2 = pointOnLineSide(bl, bb, v1x, v1y, ldx, ldy)
    end
    if p1 == p2 then return p1 end
    return -1
end

-- DOOM-style position test (P_CheckPosition + P_TryMove). The player's bounding
-- box (RADIUS on each side) may occupy (nx,ny) UNLESS: its box crosses a one-sided
-- or explicitly-blocking line; or, across all two-sided lines it crosses, the
-- accumulated vertical opening is shorter than the player (PHEIGHT) or steps up
-- more than MAXSTEP from the player's feet; or it overlaps a solid THING. Players
-- may walk off any ledge (no dropoff gate), then fall via gravity.
function W.blocked(nx, ny)
    local R = W.RADIUS
    local bl, br, bb, bt = nx - R, nx + R, ny - R, ny + R
    local sec = W.sectorAt(nx, ny)
    if not sec then return true end                       -- off the map
    local tmfloor, tmceil = sec.floor, sec.ceil
    local V, LD, SD, SE = W.map.vertexes, W.map.linedefs, W.map.sidedefs, W.map.sectors
    for _, ld in ipairs(LD) do
        local a = V[ld.v1 + 1]; local b = V[ld.v2 + 1]
        if a and b then
            local lminx = (a.x < b.x) and a.x or b.x; local lmaxx = (a.x < b.x) and b.x or a.x
            local lminy = (a.y < b.y) and a.y or b.y; local lmaxy = (a.y < b.y) and b.y or a.y
            if br > lminx and bl < lmaxx and bt > lminy and bb < lmaxy   -- box vs line bbox
                and boxOnLineSide(bl, br, bb, bt, a.x, a.y, b.x - a.x, b.y - a.y) == -1 then
                if ld.back == NONE or ld.front == NONE then return true end   -- one-sided
                if (ld.flags & 0x0001) ~= 0 then return true end             -- ML_BLOCKING
                local fsd = SD[ld.front + 1]; local bsd = SD[ld.back + 1]
                local fsec = fsd and SE[fsd.sector + 1]
                local bsec = bsd and SE[bsd.sector + 1]
                if not (fsec and bsec) then return true end
                local ot = (fsec.ceil < bsec.ceil) and fsec.ceil or bsec.ceil
                local ob = (fsec.floor > bsec.floor) and fsec.floor or bsec.floor
                if ot < tmceil then tmceil = ot end
                if ob > tmfloor then tmfloor = ob end
            end
        end
    end
    local feet = W.pz
    if tmceil - tmfloor < W.PHEIGHT then return true end      -- opening too short to fit
    if tmfloor - feet > W.MAXSTEP then return true end        -- step up too high
    -- Solid THINGS (barrels, columns, trees, monsters) block by AABB overlap.
    for _, th in ipairs(W.map.things) do
        local e = W.THING_SPR[th.dtype]
        if e and e.r and (th.flags & 0x0010) == 0 and not th.dead and not th.removed then
            local rr = R + e.r
            if abs(nx - th.x) < rr and abs(ny - th.y) < rr then return true end
        end
    end
    return false
end

-- Highest floor the player's bounding box overlaps at (x,y) = DOOM's tmfloorz, the
-- height the player actually stands at. Floor-follow MUST use this (not just the
-- center sector's floor): after a fall you can land with your box overlapping a
-- step, and standing at the lower center floor while the box sits on a higher step
-- is exactly the mismatch that wedged the player. Standing on the box's top floor
-- keeps tmfloor == feet, so you are never "inside" a step and can always walk off.
function W.floorZFor(R, x, y)
    local bl, br, bb, bt = x - R, x + R, y - R, y + R
    local sec = W.sectorAt(x, y)
    if not sec then return W.pz or 0 end              -- off-map: keep current height
    local fz = sec.floor
    local V, LD, SD, SE = W.map.vertexes, W.map.linedefs, W.map.sidedefs, W.map.sectors
    for _, ld in ipairs(LD) do
        if ld.back ~= NONE and ld.front ~= NONE then
            local a = V[ld.v1 + 1]; local b = V[ld.v2 + 1]
            if a and b then
                local lminx = (a.x < b.x) and a.x or b.x; local lmaxx = (a.x < b.x) and b.x or a.x
                local lminy = (a.y < b.y) and a.y or b.y; local lmaxy = (a.y < b.y) and b.y or a.y
                if br > lminx and bl < lmaxx and bt > lminy and bb < lmaxy
                    and boxOnLineSide(bl, br, bb, bt, a.x, a.y, b.x - a.x, b.y - a.y) == -1 then
                    local fsd = SD[ld.front + 1]; local bsd = SD[ld.back + 1]
                    local fsec = fsd and SE[fsd.sector + 1]
                    local bsec = bsd and SE[bsd.sector + 1]
                    if fsec and bsec then
                        local ob = (fsec.floor > bsec.floor) and fsec.floor or bsec.floor
                        if ob > fz then fz = ob end
                    end
                end
            end
        end
    end
    return fz
end

-- Player floor (body radius). Monsters call floorZFor with their own radius.
function W.floorZAt(x, y) return W.floorZFor(W.RADIUS, x, y) end

-- P_TryMove for the player: commit the position if the box test passes, firing
-- any walk-over trigger lines the move crossed. Momentum stays untouched.
function W.pTryMove(nx, ny)
    if W.blocked(nx, ny) then return false end
    local ox, oy = W.viewX, W.viewY
    W.viewX = nx; W.viewY = ny
    W.crossLines(ox, oy, nx, ny, true, nil)
    return true
end

-- Would this line block the player's box (for the slide trace)? One-sided and
-- ML_BLOCKING always; a two-sided line blocks when its live opening is too
-- short for the player or steps up more than MAXSTEP from the current feet.
function W.lineBlocksPlayer(ld)
    if ld.back == NONE or ld.front == NONE then return true end
    if (ld.flags & 0x0001) ~= 0 then return true end
    local SD, SE = W.map.sidedefs, W.map.sectors
    local fsd = SD[ld.front + 1]; local bsd = SD[ld.back + 1]
    local fsec = fsd and SE[fsd.sector + 1]
    local bsec = bsd and SE[bsd.sector + 1]
    if not (fsec and bsec) then return true end
    local ot = (fsec.ceil < bsec.ceil) and fsec.ceil or bsec.ceil
    local ob = (fsec.floor > bsec.floor) and fsec.floor or bsec.floor
    if ot - ob < W.PHEIGHT then return true end
    if ob - W.pz > W.MAXSTEP then return true end
    if ot - W.pz < W.PHEIGHT then return true end
    return false
end

-- P_SlideMove: the blocked move slides along the nearest blocking wall instead
-- of stopping dead. Three lead-corner traces find the closest blocking line;
-- the remaining momentum is projected onto it (P_HitSlideLine) and re-tried.
-- Momentum is CLIPPED to the projected vector, so pushing into a wall does not
-- keep the full speed (matches vanilla). Stairstep axis fallback if all else fails.
function W.slideMove()
    local R = W.RADIUS
    local V, LD = W.map.vertexes, W.map.linedefs
    for _ = 1, 3 do
        local mx, my = W.momx, W.momy
        if mx == 0 and my == 0 then return end
        local leadx = W.viewX + ((mx > 0) and R or -R)
        local leady = W.viewY + ((my > 0) and R or -R)
        local trailx = W.viewX - ((mx > 0) and R or -R)
        local traily = W.viewY - ((my > 0) and R or -R)
        local bestT, bestLd = 1.0, nil
        for _, ld in ipairs(LD) do
            local a = V[ld.v1 + 1]; local b = V[ld.v2 + 1]
            if a and b then
                local t1, u1 = W.raySeg(leadx, leady, leadx + mx, leady + my, a.x, a.y, b.x, b.y)
                if t1 and t1 >= 0 and t1 < bestT and u1 >= 0 and u1 <= 1 and W.lineBlocksPlayer(ld) then bestT = t1; bestLd = ld end
                local t2, u2 = W.raySeg(leadx, traily, leadx + mx, traily + my, a.x, a.y, b.x, b.y)
                if t2 and t2 >= 0 and t2 < bestT and u2 >= 0 and u2 <= 1 and W.lineBlocksPlayer(ld) then bestT = t2; bestLd = ld end
                local t3, u3 = W.raySeg(trailx, leady, trailx + mx, leady + my, a.x, a.y, b.x, b.y)
                if t3 and t3 >= 0 and t3 < bestT and u3 >= 0 and u3 <= 1 and W.lineBlocksPlayer(ld) then bestT = t3; bestLd = ld end
            end
        end
        if not bestLd then                             -- no line found: stairstep
            if not W.pTryMove(W.viewX, W.viewY + my) then W.pTryMove(W.viewX + mx, W.viewY) end
            return
        end
        -- move up to the blocking line (a hair short), then slide the remainder
        local goT = bestT - 0.03125 / (abs(mx) + abs(my) + 0.001)
        if goT > 0 then W.pTryMove(W.viewX + mx * goT, W.viewY + my * goT) end
        local a = V[bestLd.v1 + 1]; local b = V[bestLd.v2 + 1]
        local lx, ly = b.x - a.x, b.y - a.y
        local ll = lx * lx + ly * ly
        if ll <= 0 then return end
        local left = 1.0 - ((goT > 0) and goT or 0)
        local d = (mx * left * lx + my * left * ly) / ll   -- P_HitSlideLine projection
        W.momx = d * lx
        W.momy = d * ly
        if W.pTryMove(W.viewX + W.momx, W.viewY + W.momy) then return end
    end
    -- boxed in: stairstep as the last resort, then give up this tic
    if not W.pTryMove(W.viewX, W.viewY + W.momy) then W.pTryMove(W.viewX + W.momx, W.viewY) end
end

-- Safety net: if the player is somehow inside a blocking zone (e.g. landed hard
-- against a tall step after a fall), push out toward the first clear direction so
-- they can never be permanently trapped. Inert in normal play (collision keeps the
-- player clear of blockers, so W.blocked at the current spot is false).
W.UNSTICK_DIRS = { {8,0},{-8,0},{0,8},{0,-8},{6,6},{6,-6},{-6,6},{-6,-6} }
function W.unstick()
    if not W.blocked(W.viewX, W.viewY) then return end
    for _, d in ipairs(W.UNSTICK_DIRS) do
        if not W.blocked(W.viewX + d[1], W.viewY + d[2]) then
            W.viewX = W.viewX + d[1]; W.viewY = W.viewY + d[2]
            return
        end
    end
end

----------------------------------------------------------------------
-- SECTION Ib: sector effects (doors) + line "use"
--
-- Sectors are animated in place. The renderer, floor-follow, and W.blocked all
-- read sec.ceil / sec.floor live every frame, so raising a door sector's ceiling
-- both reveals it and unblocks passage with no other change. W.activeSectors[si]
-- holds at most one in-progress movement per sector index (keyed by sidedef sector).
----------------------------------------------------------------------
-- Specials engine constants (DOOM units per 35 Hz tic; movers run on a tic clock).
W.VDOORSPEED = 2      -- door plane units per tic (blazing = x4)
W.VDOORWAIT  = 150    -- tics a door holds open before auto-closing
W.PLATSPEED  = 1      -- lift base speed (variants scale this)
W.PLATWAIT   = 105    -- tics a lift waits down/up (35 * 3)
W.FLOORSPEED = 1      -- floor mover base speed (turbo = x4)
W.CEILSPEED  = 1      -- ceiling mover base speed
W.BUTTONTIME = 35     -- tics a pressed switch stays flipped before reverting

-- Manual (use-activated) door line specials. type = door behaviour; key = keycard
-- colour required to open; one = one-shot (special cleared, door stays open).
W.DOOR_SPECIALS = {
    [1]   = { type = "normal" },
    [26]  = { type = "normal", key = "blue" },
    [27]  = { type = "normal", key = "yellow" },
    [28]  = { type = "normal", key = "red" },
    [31]  = { type = "open", one = true },
    [32]  = { type = "open", one = true, key = "blue" },
    [33]  = { type = "open", one = true, key = "red" },
    [34]  = { type = "open", one = true, key = "yellow" },
    [117] = { type = "blazeRaise" },
    [118] = { type = "blazeOpen", one = true },
}

-- Walk-over (cross) line specials -> generic effect. once = W1 (fires one time,
-- then the special clears); no once = WR (repeatable). mon = monsters may also
-- trigger; monOnly = only monsters (a player passes with no effect).
W.CROSS_KIND = {
    [2]={ev="door",kind="open",once=true}, [3]={ev="door",kind="close",once=true},
    [4]={ev="door",kind="normal",once=true,mon=true}, [5]={ev="floor",kind="raiseFloor",once=true},
    [6]={ev="ceil",kind="fastCrushAndRaise",once=true}, [8]={ev="stairs",kind="build8",once=true},
    [10]={ev="plat",kind="downWaitUpStay",once=true,mon=true}, [12]={ev="light",amount=0,once=true},
    [13]={ev="light",amount=255,once=true}, [16]={ev="door",kind="close30",once=true},
    [17]={ev="light",amount="strobe",once=true}, [19]={ev="floor",kind="lowerFloor",once=true},
    [22]={ev="plat",kind="raiseToNearestAndChange",once=true}, [25]={ev="ceil",kind="crushAndRaise",once=true},
    [30]={ev="floor",kind="raiseToTexture",once=true}, [35]={ev="light",amount=35,once=true},
    [36]={ev="floor",kind="turboLower",once=true}, [37]={ev="floor",kind="lowerAndChange",once=true},
    [38]={ev="floor",kind="lowerFloorToLowest",once=true}, [39]={ev="tele",once=true,mon=true},
    [40]={ev="combo40",once=true}, [44]={ev="ceil",kind="lowerAndCrush",once=true},
    [52]={ev="exit"}, [53]={ev="plat",kind="perpetualRaise",once=true},
    [54]={ev="platstop",once=true}, [56]={ev="floor",kind="raiseFloorCrush",once=true},
    [57]={ev="ceilstop",once=true}, [58]={ev="floor",kind="raiseFloor24",once=true},
    [59]={ev="floor",kind="raiseFloor24AndChange",once=true}, [104]={ev="light",amount="off",once=true},
    [108]={ev="door",kind="blazeRaise",once=true}, [109]={ev="door",kind="blazeOpen",once=true},
    [100]={ev="stairs",kind="turbo16",once=true}, [110]={ev="door",kind="blazeClose",once=true},
    [119]={ev="floor",kind="raiseFloorToNearest",once=true}, [121]={ev="plat",kind="blazeDWUS",once=true},
    [124]={ev="secretexit"}, [125]={ev="tele",once=true,monOnly=true},
    [130]={ev="floor",kind="raiseFloorTurbo",once=true}, [141]={ev="ceil",kind="silentCrushAndRaise",once=true},
    [72]={ev="ceil",kind="lowerAndCrush"}, [73]={ev="ceil",kind="crushAndRaise"}, [74]={ev="ceilstop"},
    [75]={ev="door",kind="close"}, [76]={ev="door",kind="close30"}, [77]={ev="ceil",kind="fastCrushAndRaise"},
    [79]={ev="light",amount=35}, [80]={ev="light",amount=0}, [81]={ev="light",amount=255},
    [82]={ev="floor",kind="lowerFloorToLowest"}, [83]={ev="floor",kind="lowerFloor"},
    [84]={ev="floor",kind="lowerAndChange"}, [86]={ev="door",kind="open"}, [87]={ev="plat",kind="perpetualRaise"},
    [88]={ev="plat",kind="downWaitUpStay",mon=true}, [89]={ev="platstop"}, [90]={ev="door",kind="normal"},
    [91]={ev="floor",kind="raiseFloor"}, [92]={ev="floor",kind="raiseFloor24"},
    [93]={ev="floor",kind="raiseFloor24AndChange"}, [94]={ev="floor",kind="raiseFloorCrush"},
    [95]={ev="plat",kind="raiseToNearestAndChange"}, [96]={ev="floor",kind="raiseToTexture"},
    [97]={ev="tele",mon=true}, [98]={ev="floor",kind="turboLower"}, [105]={ev="door",kind="blazeRaise"},
    [106]={ev="door",kind="blazeOpen"}, [107]={ev="door",kind="blazeClose"}, [120]={ev="plat",kind="blazeDWUS"},
    [126]={ev="tele",monOnly=true}, [128]={ev="floor",kind="raiseFloorToNearest"},
    [129]={ev="floor",kind="raiseFloorTurbo"},
}

-- Switch/button (use-activated) line specials. again = SR/button (texture reverts
-- after a delay, stays usable); no again = S1 (one-shot). lock = keycard colour.
W.SWITCH_KIND = {
    [7]={ev="stairs",kind="build8"}, [9]={ev="donut"}, [11]={ev="exit"},
    [14]={ev="plat",kind="raiseAndChange",amount=32}, [15]={ev="plat",kind="raiseAndChange",amount=24},
    [18]={ev="floor",kind="raiseFloorToNearest"}, [20]={ev="plat",kind="raiseToNearestAndChange"},
    [21]={ev="plat",kind="downWaitUpStay"}, [23]={ev="floor",kind="lowerFloorToLowest"},
    [29]={ev="door",kind="normal"}, [41]={ev="ceil",kind="lowerToFloor"}, [71]={ev="floor",kind="turboLower"},
    [49]={ev="ceil",kind="crushAndRaise"}, [50]={ev="door",kind="close"}, [51]={ev="secretexit"},
    [55]={ev="floor",kind="raiseFloorCrush"}, [101]={ev="floor",kind="raiseFloor"},
    [102]={ev="floor",kind="lowerFloor"}, [103]={ev="door",kind="open"}, [111]={ev="door",kind="blazeRaise"},
    [112]={ev="door",kind="blazeOpen"}, [113]={ev="door",kind="blazeClose"}, [122]={ev="plat",kind="blazeDWUS"},
    [127]={ev="stairs",kind="turbo16"}, [131]={ev="floor",kind="raiseFloorTurbo"},
    [133]={ev="lockeddoor",kind="blazeOpen",lock="blue"}, [135]={ev="lockeddoor",kind="blazeOpen",lock="red"},
    [137]={ev="lockeddoor",kind="blazeOpen",lock="yellow"}, [140]={ev="floor",kind="raiseFloor512"},
    [42]={ev="door",kind="close",again=true}, [43]={ev="ceil",kind="lowerToFloor",again=true},
    [45]={ev="floor",kind="lowerFloor",again=true}, [60]={ev="floor",kind="lowerFloorToLowest",again=true},
    [61]={ev="door",kind="open",again=true}, [62]={ev="plat",kind="downWaitUpStay",again=true},
    [63]={ev="door",kind="normal",again=true}, [64]={ev="floor",kind="raiseFloor",again=true},
    [66]={ev="plat",kind="raiseAndChange",amount=24,again=true}, [67]={ev="plat",kind="raiseAndChange",amount=32,again=true},
    [65]={ev="floor",kind="raiseFloorCrush",again=true}, [68]={ev="plat",kind="raiseToNearestAndChange",again=true},
    [69]={ev="floor",kind="raiseFloorToNearest",again=true}, [70]={ev="floor",kind="turboLower",again=true},
    [114]={ev="door",kind="blazeRaise",again=true}, [115]={ev="door",kind="blazeOpen",again=true},
    [116]={ev="door",kind="blazeClose",again=true}, [123]={ev="plat",kind="blazeDWUS",again=true},
    [132]={ev="floor",kind="raiseFloorTurbo",again=true},
    [99]={ev="lockeddoor",kind="blazeOpen",lock="blue",again=true},
    [134]={ev="lockeddoor",kind="blazeOpen",lock="red",again=true},
    [136]={ev="lockeddoor",kind="blazeOpen",lock="yellow",again=true},
    [138]={ev="light",amount=255,again=true}, [139]={ev="light",amount=35,again=true},
}

-- Gun-triggered (impact) line specials.
W.SHOOT_KIND = {
    [24]={ev="floor",kind="raiseFloor"},
    [46]={ev="door",kind="open",again=true},
    [47]={ev="plat",kind="raiseToNearestAndChange"},
}

-- Wall switch texture pairs (SW1x <-> SW2x); flipping gives the pressed look.
W.SWITCH_PAIR = {}
W.SWITCH_NAMES = {
    "SW1BRCOM","SW2BRCOM","SW1BRN1","SW2BRN1","SW1BRN2","SW2BRN2","SW1BRNGN","SW2BRNGN",
    "SW1BROWN","SW2BROWN","SW1COMM","SW2COMM","SW1COMP","SW2COMP","SW1DIRT","SW2DIRT",
    "SW1EXIT","SW2EXIT","SW1GRAY","SW2GRAY","SW1GRAY1","SW2GRAY1","SW1METAL","SW2METAL",
    "SW1PIPE","SW2PIPE","SW1SLAD","SW2SLAD","SW1STARG","SW2STARG","SW1STON1","SW2STON1",
    "SW1STON2","SW2STON2","SW1STONE","SW2STONE","SW1STRTN","SW2STRTN",
    "SW1BLUE","SW2BLUE","SW1CMT","SW2CMT","SW1GARG","SW2GARG","SW1GSTON","SW2GSTON",
    "SW1HOT","SW2HOT","SW1LION","SW2LION","SW1SATYR","SW2SATYR","SW1SKIN","SW2SKIN",
    "SW1VINE","SW2VINE","SW1WOOD","SW2WOOD","SW1PANEL","SW2PANEL","SW1ROCK","SW2ROCK",
    "SW1MET2","SW2MET2","SW1WDMET","SW2WDMET","SW1BRIK","SW2BRIK","SW1MOD1","SW2MOD1",
    "SW1ZIM","SW2ZIM","SW1STON6","SW2STON6","SW1TEK","SW2TEK","SW1MARB","SW2MARB",
    "SW1SKULL","SW2SKULL",
}
function W.initSwitchPairs()
    local L = W.SWITCH_NAMES
    for i = 1, #L, 2 do W.SWITCH_PAIR[L[i]] = L[i + 1]; W.SWITCH_PAIR[L[i + 1]] = L[i] end
end
W.initSwitchPairs()

-- True for specials the forward "use" ray should prompt on and act on.
function W.isUseSpecial(sp)
    return (W.DOOR_SPECIALS[sp] ~= nil) or (W.SWITCH_KIND[sp] ~= nil)
end

-- Ray (x1,y1)->(x2,y2) vs segment (ax,ay)-(bx,by). Returns (t along ray, u along
-- segment) at the crossing, or nil when parallel. Caller range-checks t,u in [0,1].
function W.raySeg(x1, y1, x2, y2, ax, ay, bx, by)
    local rx, ry = x2 - x1, y2 - y1
    local sx, sy = bx - ax, by - ay
    local den = rx * sy - ry * sx
    if den == 0 then return nil end
    local qx, qy = ax - x1, ay - y1
    return (qx * sy - qy * sx) / den, (qx * ry - qy * rx) / den
end

-- Surrounding-sector height queries (DOOM p_spec.c). Each walks every two-sided
-- linedef touching sector index si and inspects the sector on the far side.
function W.eachNeighbor(si, fn)
    local LD, SD, SE = W.map.linedefs, W.map.sidedefs, W.map.sectors
    for _, ld in ipairs(LD) do
        if ld.front ~= NONE and ld.back ~= NONE then
            local fsd = SD[ld.front + 1]; local bsd = SD[ld.back + 1]
            local other
            if fsd and fsd.sector == si then other = bsd
            elseif bsd and bsd.sector == si then other = fsd end
            if other then local o = SE[other.sector + 1]; if o then fn(o, ld) end end
        end
    end
end

function W.findLowestFloor(si)
    local lo = W.map.sectors[si + 1].floor
    W.eachNeighbor(si, function(o) if o.floor < lo then lo = o.floor end end)
    return lo
end
function W.findHighestFloor(si)
    local hi = -500
    W.eachNeighbor(si, function(o) if o.floor > hi then hi = o.floor end end)
    return hi
end
function W.findLowestCeil(si)
    local lo = 32000
    W.eachNeighbor(si, function(o) if o.ceil < lo then lo = o.ceil end end)
    return lo
end
function W.findHighestCeil(si)
    local hi = 0
    W.eachNeighbor(si, function(o) if o.ceil > hi then hi = o.ceil end end)
    return hi
end
-- Lowest neighbouring floor strictly above cur (P_FindNextHighestFloor).
function W.findNextHighestFloor(si, cur)
    local best
    W.eachNeighbor(si, function(o)
        if o.floor > cur and (not best or o.floor < best) then best = o.floor end
    end)
    return best or cur
end
function W.findMinLight(si, maxl)
    local m = maxl
    W.eachNeighbor(si, function(o) if o.light < m then m = o.light end end)
    return m
end

-- Iterate every sector whose tag matches (remote specials). fn(si, sec) arms a
-- mover; sectors already running one are skipped (one per sector, like DOOM's
-- sec->specialdata). tag 0 is ignored so an untagged remote line does nothing.
function W.forTagSectors(tag, fn)
    if not tag or tag == 0 then return false end
    local rtn = false
    local SE = W.map.sectors
    for i = 1, #SE do
        if SE[i].tag == tag and not W.activeSectors[i - 1] then
            fn(i - 1, SE[i]); rtn = true
        end
    end
    return rtn
end

-- Iterate live solid things standing in sector si (monsters + barrels).
function W.eachThingInSector(si, fn)
    local sec = W.map.sectors[si + 1]; if not sec then return end
    for _, th in ipairs(W.map.things) do
        if th.think == "monster" and not th.dead and not th.removed then
            if W.sectorAt(th.x, th.y) == sec then fn(th) end
        end
    end
end

-- Would a plane closing to [nf, nc] crush a thing in sector si? P_ChangeSector's
-- fit test: the player and any live monster/barrel too tall for the new gap.
function W.thingBlocksPlane(si, nf, nc)
    local gap = nc - nf
    if gap < W.PHEIGHT and W.playerInSector(si) and not W.playerDead then return true end
    local hit = false
    W.eachThingInSector(si, function(th)
        if gap < ((th.info and th.info.h) or 56) then hit = true end
    end)
    return hit
end

-- Crush damage pulse (10 per 4 tics) on everything caught in sector si.
function W.crushThings(si)
    if (W.levelTime & 3) ~= 0 then return end
    if W.playerInSector(si) and not W.playerDead then W.hurtPlayer(10) end
    W.eachThingInSector(si, function(th)
        local gap = W.map.sectors[si + 1].ceil - W.map.sectors[si + 1].floor
        if gap < ((th.info and th.info.h) or 56) then W.damageMobj(th, 10, nil, nil) end
    end)
end

-- T_MovePlane: advance one plane of a sector one tic toward dest. Returns "ok",
-- "pastdest" (reached dest), or "crushed" (a thing is in the way). isCeil selects
-- the ceiling plane; dir is +1 up / -1 down. Crushers keep moving and hurt; other
-- movers back off and report crushed so the caller can reverse or stall.
function W.movePlane(sec, si, speed, dest, crush, isCeil, dir)
    local cur = isCeil and sec.ceil or sec.floor
    local compress = (isCeil and dir == -1) or ((not isCeil) and dir == 1)
    local nh, past
    if dir == -1 then
        if cur - speed < dest then nh = dest; past = true else nh = cur - speed end
    else
        if cur + speed > dest then nh = dest; past = true else nh = cur + speed end
    end
    if compress and W.thingBlocksPlane(si, isCeil and sec.floor or nh, isCeil and nh or sec.ceil) then
        if crush then
            W.crushThings(si)                -- crushers keep moving and hurt (10 per 4 tics)
        else
            return "crushed"                 -- do not move; caller reverses/stalls
        end
    end
    if isCeil then sec.ceil = nh else sec.floor = nh end
    return past and "pastdest" or "ok"
end

function W.playerInSector(si)
    local sec = W.map.sectors[si + 1]
    return sec ~= nil and W.sectorAt(W.viewX, W.viewY) == sec
end

-- T_VerticalDoor: one tic of a door. dir: 1 up, 0 wait-at-top, -1 down, 2 initial wait.
function W.doorThink(m)
    local sec, si = m.sec, m.si
    if m.dir == 0 then
        m.topcountdown = m.topcountdown - 1
        if m.topcountdown <= 0 then
            if m.type == "blazeRaise" then m.dir = -1; pcall(W.playSfx, "DSBDCLS")
            elseif m.type == "normal" then m.dir = -1; pcall(W.playSfx, "DSDORCLS")
            elseif m.type == "close30" then m.dir = 1; pcall(W.playSfx, "DSDOROPN") end
        end
    elseif m.dir == 2 then
        m.topcountdown = m.topcountdown - 1
        if m.topcountdown <= 0 and m.type == "raiseIn5" then
            m.dir = 1; m.type = "normal"; pcall(W.playSfx, "DSDOROPN")
        end
    elseif m.dir == -1 then
        local res = W.movePlane(sec, si, m.speed, sec.floor, false, true, -1)
        if res == "pastdest" then
            if m.type == "blazeRaise" or m.type == "blazeClose" then
                W.activeSectors[si] = nil; pcall(W.playSfx, "DSBDCLS")
            elseif m.type == "normal" or m.type == "close" then
                W.activeSectors[si] = nil
            elseif m.type == "close30" then
                m.dir = 0; m.topcountdown = 35 * 30
            end
        elseif res == "crushed" then
            if m.type ~= "blazeClose" and m.type ~= "close" then
                m.dir = 1; pcall(W.playSfx, "DSDOROPN")     -- reopen: never crush the player
            end
        end
    elseif m.dir == 1 then
        local res = W.movePlane(sec, si, m.speed, m.topheight, false, true, 1)
        if res == "pastdest" then
            if m.type == "blazeRaise" or m.type == "normal" then
                m.dir = 0; m.topcountdown = m.topwait
            else
                W.activeSectors[si] = nil                     -- open / blazeOpen: stay open
            end
        end
    end
end

-- EV_DoDoor: remote (tagged) door on every sector matching the line tag.
function W.evDoDoor(ld, kind)
    return W.forTagSectors(ld.tag, function(si, sec)
        local m = { kind = "door", sec = sec, si = si, type = kind,
            topwait = W.VDOORWAIT, speed = W.VDOORSPEED, topcountdown = 0, dir = 1 }
        if kind == "blazeClose" then
            m.topheight = W.findLowestCeil(si) - 4; m.dir = -1; m.speed = W.VDOORSPEED * 4
            pcall(W.playSfx, "DSBDCLS")
        elseif kind == "close" then
            m.topheight = W.findLowestCeil(si) - 4; m.dir = -1; pcall(W.playSfx, "DSDORCLS")
        elseif kind == "close30" then
            m.topheight = sec.ceil; m.dir = -1; pcall(W.playSfx, "DSDORCLS")
        elseif kind == "blazeRaise" or kind == "blazeOpen" then
            m.topheight = W.findLowestCeil(si) - 4; m.speed = W.VDOORSPEED * 4
            if m.topheight ~= sec.ceil then pcall(W.playSfx, "DSBDOPN") end
        else -- normal / open
            m.topheight = W.findLowestCeil(si) - 4
            if m.topheight ~= sec.ceil then pcall(W.playSfx, "DSDOROPN") end
        end
        W.activeSectors[si] = m
    end)
end

-- "You need a <colour> key to open this door" (PD_*K), or a generic fallback.
W.KEYDOORMSG = { blue = "PD_BLUEK", yellow = "PD_YELLOWK", red = "PD_REDK" }
function W.needKeyMsg(col)
    W.hudMsg = W.STR[W.KEYDOORMSG[col]] or ("You need a " .. tostring(col) .. " key")
    W.hudMsgUntil = now() + 2.0
    pcall(W.playSfx, "DSOOF")
end

-- EV_DoLockedDoor: a remote door gated behind a keycard.
function W.evDoLockedDoor(ld, kind, lock)
    if lock and not (W.keys and W.keys[lock]) then
        W.needKeyMsg(lock); return false
    end
    return W.evDoDoor(ld, kind)
end

-- EV_VerticalDoor: open (or toggle) a manual door on the sector behind the line.
function W.evVerticalDoor(ld)
    local d = W.DOOR_SPECIALS[ld.special]; if not d then return end
    if d.key and not (W.keys and W.keys[d.key]) then
        W.needKeyMsg(d.key); return
    end
    if ld.back == NONE then return end
    local bsd = W.map.sidedefs[ld.back + 1]; if not bsd then return end
    local si = bsd.sector
    local sec = W.map.sectors[si + 1]; if not sec then return end
    local m = W.activeSectors[si]
    if m and m.kind == "door" then                            -- already active: raise doors toggle
        if m.type == "normal" or m.type == "blazeRaise" then
            m.dir = (m.dir == -1) and 1 or -1
        end
        return
    end
    local blaze = (d.type == "blazeRaise" or d.type == "blazeOpen")
    local top = W.findLowestCeil(si) - 4
    if top < sec.floor then top = sec.floor end
    W.activeSectors[si] = { kind = "door", sec = sec, si = si, type = d.type,
        topheight = top, speed = blaze and (W.VDOORSPEED * 4) or W.VDOORSPEED,
        dir = 1, topwait = W.VDOORWAIT, topcountdown = 0 }
    pcall(W.playSfx, blaze and "DSBDOPN" or "DSDOROPN")
    if d.one then ld.special = 0 end                          -- D1 open: one-shot
end

-- T_MoveFloor: one tic of a floor mover; on arrival apply any texture/special change.
function W.floorThink(m)
    local res = W.movePlane(m.sec, m.si, m.speed, m.dest, m.crush, false, m.dir)
    if res == "pastdest" then
        if m.dir == -1 and m.type == "lowerAndChange" then
            m.sec.special = m.newspecial or 0; m.sec.floorTex = m.texture
        end
        W.activeSectors[m.si] = nil; pcall(W.playSfx, "DSPSTOP")
    end
end

-- EV_DoFloor: remote floor mover on tagged sectors.
function W.evDoFloor(ld, kind)
    local fsd = W.map.sidedefs[ld.front + 1]
    local fsec = fsd and W.map.sectors[fsd.sector + 1]
    return W.forTagSectors(ld.tag, function(si, sec)
        local m = { kind = "floor", sec = sec, si = si, type = kind, crush = false, dir = 1, speed = W.FLOORSPEED }
        if kind == "lowerFloor" then
            m.dir = -1; m.dest = W.findHighestFloor(si)
        elseif kind == "lowerFloorToLowest" then
            m.dir = -1; m.dest = W.findLowestFloor(si)
        elseif kind == "turboLower" then
            m.dir = -1; m.speed = W.FLOORSPEED * 4; m.dest = W.findHighestFloor(si)
            if m.dest ~= sec.floor then m.dest = m.dest + 8 end
        elseif kind == "raiseFloorCrush" or kind == "raiseFloor" then
            if kind == "raiseFloorCrush" then m.crush = true end
            m.dest = W.findLowestCeil(si); if m.dest > sec.ceil then m.dest = sec.ceil end
            if kind == "raiseFloorCrush" then m.dest = m.dest - 8 end
        elseif kind == "raiseFloorTurbo" then
            m.speed = W.FLOORSPEED * 4; m.dest = W.findNextHighestFloor(si, sec.floor)
        elseif kind == "raiseFloorToNearest" or kind == "raiseToTexture" then
            m.dest = W.findNextHighestFloor(si, sec.floor)   -- raiseToTexture lacks tex heights; nearest step
        elseif kind == "raiseFloor24" then
            m.dest = sec.floor + 24
        elseif kind == "raiseFloor512" then
            m.dest = sec.floor + 512
        elseif kind == "raiseFloor24AndChange" then
            m.dest = sec.floor + 24
            if fsec then sec.floorTex = fsec.floorTex; sec.special = fsec.special end
        elseif kind == "lowerAndChange" then
            m.dir = -1; m.dest = W.findLowestFloor(si); m.texture = sec.floorTex; m.newspecial = 0
            W.eachNeighbor(si, function(o) if o.floor == m.dest then m.texture = o.floorTex; m.newspecial = o.special end end)
        else
            m.dest = sec.floor
        end
        W.activeSectors[si] = m
    end)
end

-- T_PlatRaise: one tic of a lift (down-wait-up, perpetual, raise-and-change).
function W.platThink(m)
    local sec, si = m.sec, m.si
    if m.status == "up" then
        local res = W.movePlane(sec, si, m.speed, m.high, m.crush, false, 1)
        if (m.type == "raiseAndChange" or m.type == "raiseToNearestAndChange") and (W.levelTime % 8) == 0 then
            pcall(W.playSfx, "DSSTNMOV")
        end
        if res == "crushed" and not m.crush then
            m.count = m.wait; m.status = "down"; pcall(W.playSfx, "DSPSTART")
        elseif res == "pastdest" then
            m.count = m.wait; m.status = "waiting"; pcall(W.playSfx, "DSPSTOP")
            if m.type == "blazeDWUS" or m.type == "downWaitUpStay"
                or m.type == "raiseAndChange" or m.type == "raiseToNearestAndChange" then
                W.activeSectors[si] = nil
            end
        end
    elseif m.status == "down" then
        local res = W.movePlane(sec, si, m.speed, m.low, false, false, -1)
        if res == "pastdest" then m.count = m.wait; m.status = "waiting"; pcall(W.playSfx, "DSPSTOP") end
    elseif m.status == "waiting" then
        m.count = m.count - 1
        if m.count <= 0 then
            m.status = (sec.floor == m.low) and "up" or "down"
            pcall(W.playSfx, "DSPSTART")
        end
    end
end

-- EV_DoPlat: remote lift on tagged sectors.
function W.evDoPlat(ld, kind, amount)
    if kind == "perpetualRaise" then                         -- resume any in-stasis lifts of this tag
        for _, m in pairs(W.activeSectors) do
            if m.kind == "plat" and m.tag == ld.tag and m.status == "in_stasis" then m.status = m.oldstatus or "up" end
        end
    end
    local fsd = W.map.sidedefs[ld.front + 1]
    local fsec = fsd and W.map.sectors[fsd.sector + 1]
    return W.forTagSectors(ld.tag, function(si, sec)
        local m = { kind = "plat", sec = sec, si = si, type = kind, crush = false, tag = ld.tag, count = 0 }
        if kind == "raiseToNearestAndChange" then
            m.speed = W.PLATSPEED / 2; if fsec then sec.floorTex = fsec.floorTex end
            m.high = W.findNextHighestFloor(si, sec.floor); m.wait = 0; m.status = "up"; sec.special = 0
            pcall(W.playSfx, "DSSTNMOV")
        elseif kind == "raiseAndChange" then
            m.speed = W.PLATSPEED / 2; if fsec then sec.floorTex = fsec.floorTex end
            m.high = sec.floor + (amount or 0); m.wait = 0; m.status = "up"; pcall(W.playSfx, "DSSTNMOV")
        elseif kind == "downWaitUpStay" or kind == "blazeDWUS" then
            m.speed = (kind == "blazeDWUS") and (W.PLATSPEED * 8) or (W.PLATSPEED * 4)
            m.low = W.findLowestFloor(si); if m.low > sec.floor then m.low = sec.floor end
            m.high = sec.floor; m.wait = W.PLATWAIT; m.status = "down"; pcall(W.playSfx, "DSPSTART")
        elseif kind == "perpetualRaise" then
            m.speed = W.PLATSPEED; m.low = W.findLowestFloor(si)
            if m.low > sec.floor then m.low = sec.floor end
            m.high = W.findHighestFloor(si); if m.high < sec.floor then m.high = sec.floor end
            m.wait = W.PLATWAIT; m.status = ((W.levelTime & 1) == 0) and "up" or "down"
            pcall(W.playSfx, "DSPSTART")
        else
            m.speed = W.PLATSPEED; m.low = sec.floor; m.high = sec.floor; m.wait = W.PLATWAIT; m.status = "down"
        end
        W.activeSectors[si] = m
    end)
end

function W.evStopPlat(ld)
    for _, m in pairs(W.activeSectors) do
        if m.kind == "plat" and m.tag == ld.tag and m.status ~= "in_stasis" then
            m.oldstatus = m.status; m.status = "in_stasis"
        end
    end
    return true
end

-- T_MoveCeiling: one tic of a ceiling mover / crusher.
function W.ceilThink(m)
    local sec, si = m.sec, m.si
    if m.dir == 1 then
        local res = W.movePlane(sec, si, m.speed, m.topheight, false, true, 1)
        if res == "pastdest" then
            if m.type == "raiseToHighest" then W.activeSectors[si] = nil
            else m.dir = -1 end                              -- crushers reverse
            if m.type == "silentCrushAndRaise" then pcall(W.playSfx, "DSPSTOP") end
        end
    elseif m.dir == -1 then
        local res = W.movePlane(sec, si, m.speed, m.bottomheight, m.crush, true, -1)
        if res == "pastdest" then
            if m.type == "crushAndRaise" or m.type == "silentCrushAndRaise" then m.speed = W.CEILSPEED; m.dir = 1
            elseif m.type == "fastCrushAndRaise" then m.dir = 1
            else W.activeSectors[si] = nil end
            if m.type == "silentCrushAndRaise" then pcall(W.playSfx, "DSPSTOP") end
        elseif res == "crushed" then
            if m.type == "crushAndRaise" or m.type == "silentCrushAndRaise" or m.type == "lowerAndCrush" then
                m.speed = W.CEILSPEED / 8
            end
        end
    end
end

-- EV_DoCeiling: remote ceiling mover / crusher on tagged sectors.
function W.evDoCeiling(ld, kind)
    return W.forTagSectors(ld.tag, function(si, sec)
        local m = { kind = "ceil", sec = sec, si = si, type = kind, crush = false, tag = sec.tag }
        if kind == "fastCrushAndRaise" then
            m.crush = true; m.topheight = sec.ceil; m.bottomheight = sec.floor + 8; m.dir = -1; m.speed = W.CEILSPEED * 2
        elseif kind == "crushAndRaise" or kind == "silentCrushAndRaise" then
            m.crush = true; m.topheight = sec.ceil; m.bottomheight = sec.floor + 8; m.dir = -1; m.speed = W.CEILSPEED
        elseif kind == "lowerAndCrush" then
            m.bottomheight = sec.floor + 8; m.dir = -1; m.speed = W.CEILSPEED
        elseif kind == "lowerToFloor" then
            m.bottomheight = sec.floor; m.dir = -1; m.speed = W.CEILSPEED
        elseif kind == "raiseToHighest" then
            m.topheight = W.findHighestCeil(si); m.dir = 1; m.speed = W.CEILSPEED
        end
        W.activeSectors[si] = m
    end)
end

function W.evCeilStop(ld)
    for _, m in pairs(W.activeSectors) do
        if m.kind == "ceil" and m.tag == ld.tag and m.dir ~= 0 then m.olddir = m.dir; m.dir = 0 end
    end
    return true
end

-- EV_BuildStairs: raise the tagged sector, then step up each same-floor-texture
-- neighbour reached through a line whose front side is the current step.
function W.evBuildStairs(ld, kind)
    local size = (kind == "turbo16") and 16 or 8
    local speed = (kind == "turbo16") and (W.FLOORSPEED * 4) or (W.FLOORSPEED / 4)
    local LD, SD, SE = W.map.linedefs, W.map.sidedefs, W.map.sectors
    return W.forTagSectors(ld.tag, function(si, sec)
        local secnum = si
        local height = sec.floor + size
        local tex = sec.floorTex
        W.activeSectors[secnum] = { kind = "floor", sec = SE[secnum + 1], si = secnum,
            type = "stair", crush = false, dir = 1, speed = speed, dest = height }
        local ok = true
        while ok do
            ok = false
            for _, l in ipairs(LD) do
                if l.front ~= NONE and l.back ~= NONE then
                    local lfsd = SD[l.front + 1]; local lbsd = SD[l.back + 1]
                    if lfsd and lbsd and lfsd.sector == secnum then
                        local nn = lbsd.sector
                        local tsec = SE[nn + 1]
                        if tsec and tsec.floorTex == tex and not W.activeSectors[nn] then
                            height = height + size
                            secnum = nn
                            W.activeSectors[nn] = { kind = "floor", sec = tsec, si = nn,
                                type = "stair", crush = false, dir = 1, speed = speed, dest = height }
                            ok = true
                            break
                        end
                    end
                end
            end
        end
    end)
end

-- DOOM par times (g_game.c): pars[episode][map], DOOM II cpars[map].
W.PARS = {
    [1] = { 30, 75, 120, 90, 165, 180, 180, 30, 165 },
    [2] = { 90, 90, 90, 120, 90, 360, 240, 30, 170 },
    [3] = { 90, 45, 90, 150, 90, 90, 165, 30, 135 },
}
W.CPARS = {
    30, 90, 120, 120, 90, 150, 120, 120, 270, 90,
    210, 150, 150, 150, 210, 150, 420, 150, 210, 150,
    240, 150, 180, 150, 150, 300, 330, 420, 300, 180,
    120, 30,
}

function W.mapExists(name)
    for _, m in ipairs(W.mapList or {}) do if m == name then return true end end
    return false
end

-- G_DoCompleted: gather the intermission stats + compute the next map with the
-- vanilla secret-exit routing (ExM9 / MAP31/MAP32) and episode-end handling,
-- then hand off to the intermission screen.
function W.exitLevel(secret)
    W.finishLevel()                         -- keep gear across the level, drop keys/powers
    local cur = (W.map and W.map.name) or ""
    local ep, mp = cur:match("^E(%d)M(%d)$")
    local wm = { last = cur, secret = secret and true or false }
    if ep then
        ep, mp = tonumber(ep), tonumber(mp)
        wm.epsd = ep
        wm.lastIdx = mp - 1
        if mp == 9 then W.didsecret = true end
        local nmp
        if secret then nmp = 9
        elseif mp == 9 then nmp = ({ [1] = 4, [2] = 6, [3] = 7, [4] = 3 })[ep] or 4
        elseif mp == 8 then nmp = nil                    -- episode complete
        else nmp = mp + 1 end
        if nmp then wm.next = ("E%dM%d"):format(ep, nmp); wm.nextIdx = nmp - 1 end
        local p = W.PARS[ep]
        wm.par = p and p[mp] or nil                      -- E4+ shows no par
    else
        mp = tonumber(cur:match("^MAP(%d+)$") or "")
        if mp then
            wm.lastIdx = mp - 1
            local nmp
            if secret then nmp = (mp == 31) and 32 or 31
            elseif mp == 31 or mp == 32 then nmp = 16
            elseif mp == 30 then nmp = nil               -- game complete
            else nmp = mp + 1 end
            if nmp then wm.next = ("MAP%02d"):format(nmp); wm.nextIdx = nmp - 1 end
            wm.par = W.CPARS[mp]
        end
    end
    if wm.next and not W.mapExists(wm.next) then wm.next = nil end
    wm.kills = W.killCount or 0
    wm.maxkills = max(1, W.totalKills or 0)
    wm.items = W.itemCount or 0
    wm.maxitems = max(1, W.totalItems or 0)
    wm.secrets = W.secretCount or 0
    wm.maxsecret = max(1, W.totalSecret or 0)
    wm.time = floor((W.levelTime or 0) / 35)
    W.wiStart(wm)
end

-- After the intermission: load the next map, or return to the front-end menu
-- when the episode/game is over (the victory text screens are not simulated).
function W.worldDone(wm)
    if wm.next then W.startMap(wm.next)
    else
        W.menu.fromPlay = false; W.menu.screen = "main"; W.menu.cursor = 1
        W.gameState = "frontend"; W.status = "level complete"
        if W.musicOn then W.musPending = "VICTORY" end
    end
end

-- EV_Teleport: move a player/monster to the MT_TELEPORTMAN (thing type 14) in a
-- sector matching the line tag. side 1 (came from the back) does not teleport.
-- Vanilla trimmings: TFOG bursts + sound at BOTH ends, an 18-tic post-teleport
-- freeze, the player telefrags anything on the pad, and a monster whose pad is
-- occupied simply does not teleport (P_StompThing rule).
function W.evTeleport(ld, side, isPlayer, th)
    if side == 1 then return false end
    if not ld.tag or ld.tag == 0 then return false end
    for _, t in ipairs(W.map.things) do
        if t.dtype == 14 then
            local sec = W.sectorAt(t.x, t.y)
            if sec and sec.tag == ld.tag then
                local dz = W.floorZFor(W.RADIUS, t.x, t.y)
                -- destination occupancy: player stomps, monsters bounce off
                for _, o in ipairs(W.map.things) do
                    if o.think == "monster" and not o.dead and not o.removed and o ~= th then
                        local oe = W.THING_SPR[o.dtype]
                        local rr = (oe and oe.r or 20) + ((isPlayer and W.RADIUS)
                            or (th and th.info and th.info.r) or 20)
                        if abs(o.x - t.x) < rr and abs(o.y - t.y) < rr then
                            if isPlayer then W.damageMobj(o, 10000, nil, "player")
                            else return false end
                        end
                    end
                end
                local ox, oy, oz
                if isPlayer then
                    ox, oy, oz = W.viewX, W.viewY, W.pz
                    W.viewX = t.x; W.viewY = t.y
                    W.pz = dz; W.momx = 0; W.momy = 0; W.momz = 0
                    W.viewZ = dz + (W.viewheight or 41)
                    W.viewAngle = math.rad(t.angle)
                    W.reactionTics = 18                       -- vanilla freeze
                    W.oldPX = W.viewX; W.oldPY = W.viewY; W.oldVZ = W.viewZ  -- no interp glide
                elseif th then
                    ox, oy, oz = th.x, th.y, th.z or dz
                    th.x = t.x; th.y = t.y; th.z = dz
                    th.angle = t.angle; th.movecount = 0; th.movedir = 8
                    th.reaction = 18
                end
                if ox then W.spawnFx("TFOG", "ABABCDEFGHIJ", 6, ox, oy, oz, { bright = true }) end
                W.spawnFx("TFOG", "ABABCDEFGHIJ", 6,
                    t.x + 20 * cos(math.rad(t.angle)), t.y + 20 * sin(math.rad(t.angle)),
                    dz, { bright = true })
                pcall(W.playSfx, "DSTELEPT")
                return true
            end
        end
    end
    return false
end

-- EV_LightTurnOn / TurnTagLightsOff / strobe-start on tagged sectors.
function W.evLightTurnOn(ld, amount)
    if not ld.tag or ld.tag == 0 then return end
    for i = 1, #W.map.sectors do
        local sec = W.map.sectors[i]
        if sec.tag == ld.tag then
            local si = i - 1
            if amount == "off" then
                sec.light = W.findMinLight(si, sec.light)
            elseif amount == "strobe" then
                W.spawnStrobe(si, sec, 35, false)          -- EV_StartLightStrobing: SLOWDARK
            elseif amount == 0 then
                local hi = 0
                W.eachNeighbor(si, function(o) if o.light > hi then hi = o.light end end)
                sec.light = hi
            else
                sec.light = amount
            end
        end
    end
end

-- P_ChangeSwitchTexture: flip a wall switch to its pressed variant; buttons (again)
-- schedule a revert. Scans the front side's top/mid/bottom for a known switch face.
function W.changeSwitch(ld, again)
    local fsd = W.map.sidedefs[ld.front + 1]; if not fsd then return end
    local snd = (ld.special == 11 or ld.special == 51) and "DSSWTCHX" or "DSSWTCHN"
    if not again then ld.special = 0 end
    for _, f in ipairs({ "upper", "mid", "lower" }) do
        local opp = W.SWITCH_PAIR[fsd[f]]
        if opp then
            pcall(W.playSfx, snd)
            if again then W.startButton(ld, fsd, f, fsd[f]) end
            fsd[f] = opp
            return
        end
    end
end

function W.startButton(ld, fsd, field, tex)
    W.buttons = W.buttons or {}
    for _, b in ipairs(W.buttons) do if b.ld == ld and b.field == field then return end end
    W.buttons[#W.buttons + 1] = { ld = ld, sd = fsd, field = field, tex = tex, timer = W.BUTTONTIME }
end

-- P_CrossSpecialLine: a thing's centre crossed a walk-trigger line.
function W.crossSpecialLine(ld, side, isPlayer, th)
    local c = W.CROSS_KIND[ld.special]; if not c then return end
    if not isPlayer then
        if c.monOnly then if c.ev ~= "tele" then return end
        elseif not c.mon then return end
    elseif c.monOnly then
        return
    end
    local ev = c.ev
    if ev == "door" then W.evDoDoor(ld, c.kind)
    elseif ev == "floor" then W.evDoFloor(ld, c.kind)
    elseif ev == "plat" then W.evDoPlat(ld, c.kind, 0)
    elseif ev == "ceil" then W.evDoCeiling(ld, c.kind)
    elseif ev == "stairs" then W.evBuildStairs(ld, c.kind)
    elseif ev == "tele" then W.evTeleport(ld, side, isPlayer, th)
    elseif ev == "light" then W.evLightTurnOn(ld, c.amount)
    elseif ev == "platstop" then W.evStopPlat(ld)
    elseif ev == "ceilstop" then W.evCeilStop(ld)
    elseif ev == "combo40" then W.evDoCeiling(ld, "raiseToHighest"); W.evDoFloor(ld, "lowerFloorToLowest")
    elseif ev == "exit" or ev == "secretexit" then W.exitLevel(ev == "secretexit")
    end
    if c.once then ld.special = 0 end
end

-- P_UseSpecialLine: the player pressed use on a special line. Returns true if the
-- line responded (so the caller stops looking). Manual doors, switches, exits.
function W.useSpecialLine(ld)
    local sp = ld.special
    if W.DOOR_SPECIALS[sp] then W.evVerticalDoor(ld); return true end
    local s = W.SWITCH_KIND[sp]; if not s then return false end
    local ev = s.ev
    if ev == "exit" or ev == "secretexit" then W.changeSwitch(ld, false); W.exitLevel(ev == "secretexit"); return true end
    local ok = false
    if ev == "floor" then ok = W.evDoFloor(ld, s.kind)
    elseif ev == "plat" then ok = W.evDoPlat(ld, s.kind, s.amount or 0)
    elseif ev == "door" then ok = W.evDoDoor(ld, s.kind)
    elseif ev == "ceil" then ok = W.evDoCeiling(ld, s.kind)
    elseif ev == "stairs" then ok = W.evBuildStairs(ld, s.kind)
    elseif ev == "lockeddoor" then ok = W.evDoLockedDoor(ld, s.kind, s.lock)
    elseif ev == "light" then W.evLightTurnOn(ld, s.amount); ok = true
    elseif ev == "donut" then ok = false                     -- donut movers not implemented
    end
    if ok then W.changeSwitch(ld, s.again or false) end
    return true
end

-- Called by the forward use ray when the player presses use on a special line.
function W.useSpecial(ld)
    if ld then W.useSpecialLine(ld) end
end

-- P_ShootSpecialLine: player gunfire impacts an impact-special line. Scans forward
-- for the nearest such line not hidden behind a closer solid wall, then triggers it.
function W.shootSpecialLine(x1, y1, ang, range)
    local dx, dy = cos(ang), sin(ang)
    local x2, y2 = x1 + dx * range, y1 + dy * range
    local V, LD = W.map.vertexes, W.map.linedefs
    local best, bestT, wallT = nil, 1e9, 1e9
    for _, ld in ipairs(LD) do
        local a = V[ld.v1 + 1]; local b = V[ld.v2 + 1]
        if a and b then
            local t, u = W.raySeg(x1, y1, x2, y2, a.x, a.y, b.x, b.y)
            if t and t >= 0 and t <= 1 and u >= 0 and u <= 1 then
                if W.SHOOT_KIND[ld.special] then
                    if t < bestT then best, bestT = ld, t end
                elseif ld.back == NONE and t < wallT then wallT = t end
            end
        end
    end
    if not best or bestT > wallT then return end
    local s = W.SHOOT_KIND[best.special]
    local ok = false
    if s.ev == "floor" then ok = W.evDoFloor(best, s.kind)
    elseif s.ev == "door" then ok = W.evDoDoor(best, s.kind)
    elseif s.ev == "plat" then ok = W.evDoPlat(best, s.kind, 0) end
    if ok then W.changeSwitch(best, s.again or false) end
end

-- Forward "use" ray (USERANGE 64): the nearest special line, unless a solid wall
-- is closer (cannot reach a door through a wall). Returns the linedef, or nil.
function W.useLine()
    local x1, y1 = W.viewX, W.viewY
    local x2, y2 = x1 + cos(W.viewAngle) * 64, y1 + sin(W.viewAngle) * 64
    local V, LD = W.map.vertexes, W.map.linedefs
    local best, bestT, wallT = nil, 1e9, 1e9
    for _, ld in ipairs(LD) do
        local a = V[ld.v1 + 1]; local b = V[ld.v2 + 1]
        if a and b then
            local t, u = W.raySeg(x1, y1, x2, y2, a.x, a.y, b.x, b.y)
            if t and t >= 0 and t <= 1 and u >= 0 and u <= 1 then
                if ld.special and ld.special ~= 0 and W.isUseSpecial(ld.special) then
                    if t < bestT then best, bestT = ld, t end
                elseif ld.back == NONE and t < wallT then
                    wallT = t                          -- solid wall blocks the use ray
                end
            end
        end
    end
    if best and bestT <= wallT then return best end
    return nil
end

-- Sector light effects (DOOM p_lights.c). Each thinker retimes a sector light
-- on the 35 Hz clock. STROBEBRIGHT=5, FASTDARK=15, SLOWDARK=35, GLOWSPEED=8.
function W.spawnStrobe(si, sec, darkT, sync)
    W.lightThinkers = W.lightThinkers or {}
    local dark = W.findMinLight(si, sec.light)
    if dark == sec.light then dark = 0 end
    W.lightThinkers[#W.lightThinkers + 1] = { kind = "strobe", sec = sec,
        bright = sec.light, dark = dark, brightT = 5, darkT = darkT or 15,
        count = sync and 1 or (1 + (W.pRandom() & 7)) }
end
function W.spawnLightFlash(si, sec)
    W.lightThinkers = W.lightThinkers or {}
    W.lightThinkers[#W.lightThinkers + 1] = { kind = "flash", sec = sec,
        bright = sec.light, dark = W.findMinLight(si, sec.light), count = 1 + (W.pRandom() & 63) }
end
function W.spawnGlow(si, sec)
    W.lightThinkers = W.lightThinkers or {}
    W.lightThinkers[#W.lightThinkers + 1] = { kind = "glow", sec = sec,
        maxl = sec.light, minl = W.findMinLight(si, sec.light), val = sec.light, dir = -1 }
end
-- T_FireFlicker (sector special 17): every 4 tics, max - (P_Random&3)*16.
function W.spawnFireFlicker(si, sec)
    W.lightThinkers = W.lightThinkers or {}
    W.lightThinkers[#W.lightThinkers + 1] = { kind = "fire", sec = sec,
        maxl = sec.light, minl = W.findMinLight(si, sec.light) + 16, count = 4 }
end
function W.lightTick(lt)
    if lt.kind == "strobe" then
        lt.count = lt.count - 1
        if lt.count <= 0 then
            if lt.sec.light == lt.dark then lt.sec.light = lt.bright; lt.count = lt.brightT
            else lt.sec.light = lt.dark; lt.count = lt.darkT end
        end
    elseif lt.kind == "flash" then
        lt.count = lt.count - 1
        if lt.count <= 0 then
            if lt.sec.light == lt.bright then lt.sec.light = lt.dark; lt.count = 1 + (W.pRandom() & 7)
            else lt.sec.light = lt.bright; lt.count = 1 + (W.pRandom() & 32) end
        end
    elseif lt.kind == "glow" then
        lt.val = lt.val + lt.dir * 8
        if lt.val <= lt.minl then lt.val = lt.minl; lt.dir = 1
        elseif lt.val >= lt.maxl then lt.val = lt.maxl; lt.dir = -1 end
        lt.sec.light = lt.val
    elseif lt.kind == "fire" then
        lt.count = lt.count - 1
        if lt.count <= 0 then
            local amount = (W.pRandom() & 3) * 16
            if lt.maxl - amount < lt.minl then lt.sec.light = lt.minl
            else lt.sec.light = lt.maxl - amount end
            lt.count = 4
        end
    end
end

-- P_PlayerInSpecialSector: damage / secret floors, only while grounded (the player
-- z equals the floor). radsuit (ironfeet) blocks nukage/slime damage.
function W.playerInSpecialSector()
    if W.playerDead then return end
    local sec = W.sectorAt(W.viewX, W.viewY); if not sec then return end
    local sp = sec.special or 0
    if sp == 0 then return end
    if W.pz - sec.floor > 1 then return end                  -- airborne: no floor contact
    local suit = W.powers and W.powers.radsuit
    local due = (W.levelTime & 0x1f) == 0
    if sp == 5 then
        if not suit and due then W.hurtPlayer(10) end
    elseif sp == 7 then
        if not suit and due then W.hurtPlayer(5) end
    elseif sp == 16 or sp == 4 then
        if (not suit or W.pRandom() < 5) and due then W.hurtPlayer(20) end
    elseif sp == 9 then
        W.secretCount = (W.secretCount or 0) + 1; sec.special = 0
        W.hudMsg = "A secret is revealed!"; W.hudMsgUntil = now() + 2.0
    elseif sp == 11 then
        if due then W.hurtPlayer(20) end
        if (W.health or 0) <= 10 then W.exitLevel() end
    end
end

-- One 35 Hz tic of every active special: movers, buttons, lights, damage floors.
function W.tickSpecials()
    for _, m in pairs(W.activeSectors) do
        if m.kind == "door" then W.doorThink(m)
        elseif m.kind == "floor" then W.floorThink(m)
        elseif m.kind == "plat" then W.platThink(m)
        elseif m.kind == "ceil" then W.ceilThink(m) end
    end
    if W.buttons then
        for i = #W.buttons, 1, -1 do
            local b = W.buttons[i]
            b.timer = b.timer - 1
            if b.timer <= 0 then
                if b.sd then b.sd[b.field] = b.tex end
                pcall(W.playSfx, "DSSWTCHN"); table.remove(W.buttons, i)
            end
        end
    end
    if W.lightThinkers then for _, lt in ipairs(W.lightThinkers) do W.lightTick(lt) end end
    W.playerInSpecialSector()
end

-- P_Ticker: ONE 35 Hz game tic. Everything gameplay-visible advances here so
-- every vanilla tic constant drops in verbatim; rendering interpolates the view
-- between tics (W.rSwap). Order matches vanilla: player, thinkers, specials.
function W.gameTic()
    W.oldPX = W.viewX; W.oldPY = W.viewY; W.oldVZ = W.viewZ   -- interp snapshot
    W.playerThink()
    W.updateActors()
    W.tickSpecials()
    W.updatePickups()
    W.stTicker()
end

-- Accumulate real time into 35 Hz tics and run the game clock. Bounded so a
-- long stall cannot spend the frame running hundreds of catch-up tics.
function W.runTics(dt)
    W.specAccum = (W.specAccum or 0) + dt
    local steps = 0
    while W.specAccum >= W.TIC and steps < 6 do
        W.specAccum = W.specAccum - W.TIC
        if W.gameState == "play" then
            if W.activeSectors then
                W.levelTime = (W.levelTime or 0) + 1
                W.gameTic()
            end
        elseif W.gameState == "intermission" then
            W.wiTicker()
        end
        steps = steps + 1
    end
    if W.specAccum > W.TIC * 6 then W.specAccum = 0 end
end

-- P_SpawnSpecials: after a map loads, arm sector-special thinkers, count secrets,
-- reset the tic clock, and cache the trigger-line list the movement code scans.
function W.spawnSpecials(map)
    W.levelTime = 0; W.specAccum = 0
    W.buttons = {}; W.lightThinkers = {}
    W.secretCount = 0; W.totalSecret = 0
    for i = 1, #map.sectors do
        local sec = map.sectors[i]; local si = i - 1
        local sp = sec.special or 0
        if sp == 1 then W.spawnLightFlash(si, sec)
        elseif sp == 2 then W.spawnStrobe(si, sec, 15, false)      -- fast strobe
        elseif sp == 3 then W.spawnStrobe(si, sec, 35, false)      -- slow strobe
        elseif sp == 4 then W.spawnStrobe(si, sec, 15, false)      -- strobe + 20% damage
        elseif sp == 8 then W.spawnGlow(si, sec)
        elseif sp == 9 then W.totalSecret = W.totalSecret + 1
        elseif sp == 10 then                                       -- door close in 30s
            sec.special = 0
            W.activeSectors[si] = { kind = "door", sec = sec, si = si, type = "normal",
                topheight = sec.ceil, speed = W.VDOORSPEED, dir = 0,
                topwait = W.VDOORWAIT, topcountdown = 30 * 35 }
        elseif sp == 12 then W.spawnStrobe(si, sec, 35, true)      -- sync slow
        elseif sp == 13 then W.spawnStrobe(si, sec, 15, true)      -- sync fast
        elseif sp == 14 then                                       -- door raise in 5 min
            sec.special = 0
            W.activeSectors[si] = { kind = "door", sec = sec, si = si, type = "raiseIn5",
                topheight = W.findLowestCeil(si) - 4, speed = W.VDOORSPEED, dir = 2,
                topwait = W.VDOORWAIT, topcountdown = 5 * 60 * 35 }
        elseif sp == 17 then W.spawnFireFlicker(si, sec) end
    end
    local tl = {}
    for _, ld in ipairs(map.linedefs) do if (ld.special or 0) ~= 0 then tl[#tl + 1] = ld end end
    map.triggerLines = tl
    -- Sector sound-adjacency graph for P_NoiseAlert: neighbours through every
    -- two-sided line, flagged when the line is ML_SOUNDBLOCK (0x40).
    local adj = {}
    for i = 1, #map.sectors do adj[i - 1] = {} end
    for _, ld in ipairs(map.linedefs) do
        if ld.front ~= NONE and ld.back ~= NONE then
            local fsd = map.sidedefs[ld.front + 1]
            local bsd = map.sidedefs[ld.back + 1]
            if fsd and bsd and fsd.sector ~= bsd.sector then
                local blocked = (ld.flags & 0x0040) ~= 0
                local fa = adj[fsd.sector]; if fa then fa[#fa + 1] = { s = bsd.sector, ld = ld, blk = blocked } end
                local ba = adj[bsd.sector]; if ba then ba[#ba + 1] = { s = fsd.sector, ld = ld, blk = blocked } end
            end
        end
    end
    map.soundAdj = adj
    W.soundValid = 0
    for i = 1, #map.sectors do
        map.sectors[i].soundTarget = nil
        map.sectors[i].soundValid = 0
        map.sectors[i].soundTraversed = 0
    end
end

-- P_NoiseAlert: flood the player's noise through connected sectors. Sound
-- passes any live opening; an ML_SOUNDBLOCK line eats one "block level" (sound
-- travels through at most one). Flooded sectors remember the noise-maker so
-- A_Look can wake on it. Iterative stack walk (deep maps recurse far).
function W.noiseAlert()
    local map = W.map; if not (map and map.soundAdj) then return end
    W.soundValid = (W.soundValid or 0) + 1
    local valid = W.soundValid
    local sec0 = W.sectorAt(W.viewX, W.viewY); if not sec0 then return end
    local si0
    for i = 1, #map.sectors do if map.sectors[i] == sec0 then si0 = i - 1; break end end
    if not si0 then return end
    local stack = { { si0, 0 } }
    while #stack > 0 do
        local e = table.remove(stack)
        local si, blocks = e[1], e[2]
        local sec = map.sectors[si + 1]
        if sec and not (sec.soundValid == valid and sec.soundTraversed <= blocks + 1) then
            sec.soundValid = valid
            sec.soundTraversed = blocks + 1
            sec.soundTarget = "player"
            for _, n in ipairs(map.soundAdj[si] or {}) do
                local osec = map.sectors[n.s + 1]
                if osec then
                    local opentop = min(sec.ceil, osec.ceil)
                    local openbot = max(sec.floor, osec.floor)
                    if opentop - openbot > 0 then            -- closed door stops sound
                        if n.blk then
                            if blocks == 0 then stack[#stack + 1] = { n.s, 1 } end
                        else
                            stack[#stack + 1] = { n.s, blocks }
                        end
                    end
                end
            end
        end
    end
end

-- Fire walk-over line specials whose linedef the actor's centre crossed (old->new).
function W.crossLines(ox, oy, nx, ny, isPlayer, th)
    if not (W.map and W.map.triggerLines) then return end
    if ox == nx and oy == ny then return end
    local V = W.map.vertexes
    for _, ld in ipairs(W.map.triggerLines) do
        if (ld.special or 0) ~= 0 and W.CROSS_KIND[ld.special] then
            local a = V[ld.v1 + 1]; local b = V[ld.v2 + 1]
            if a and b then
                local t, u = W.raySeg(ox, oy, nx, ny, a.x, a.y, b.x, b.y)
                if t and t >= 0 and t <= 1 and u >= 0 and u <= 1 then
                    local sd = pointOnLineSide(ox, oy, a.x, a.y, b.x - a.x, b.y - a.y)
                    W.crossSpecialLine(ld, sd, isPlayer, th)
                end
            end
        end
    end
end

----------------------------------------------------------------------
-- SECTION Ic: player inventory + pickups + actor spawn
-- Inventory persists across levels (DOOM G_PlayerFinishLevel keeps health/ammo/
-- weapons, clears keys/powers). Pickups are enriched map THINGS touched by radius.
----------------------------------------------------------------------
function W.newGame()
    W.skill = W.skill or 3               -- default Hurt Me Plenty; keep an explicit menu choice
    W.health = 100
    W.armor = 0; W.armorType = 0
    W.ammo = { bul = 50, shl = 0, rck = 0, cel = 0 }
    W.maxammo = { bul = 200, shl = 50, rck = 50, cel = 300 }
    W.weaponOwned = { [1] = true, [2] = true }
    W.curWeapon = 2; W.pendingWeapon = nil
    W.keys = { blue = false, yellow = false, red = false }
    W.keyForm = {}
    W.backpack = false
    W.powers = {}                           -- power -> tics remaining (huge = level-long)
    W.damageCount = 0; W.bonusCount = 0
    W.playerDead = false
    W.attacker = nil
    W.hudMsg = nil; W.hudMsgUntil = 0
    W.psp = { st = nil, tics = -1, sx = 1, sy = 32 }
    W.psf = { st = nil, tics = -1 }
    W.attackdown = false; W.refire = 0; W.extralight = 0
    W.fireArmed = false                     -- require one observed fire-release before autofire
    W.momx = 0; W.momy = 0; W.momz = 0; W.bob = 0
    W.viewheight = 41; W.dvh = 0
    W.reactionTics = 0
    W.didsecret = false
    W.rndIdx = 0
    W.stInit()
end

function W.finishLevel()                    -- between levels: keep gear, drop keys/powers
    W.keys = { blue = false, yellow = false, red = false }
    W.keyForm = {}
    W.powers = {}
    W.extralight = 0
    W.bonusCount = 0; W.damageCount = 0; W.hudMsg = nil
end

-- Skill 1..5 (ITYTD/HNTR/HMP/UV/Nightmare). W.skillBit maps to the DOOM thing
-- skill-flag bit a monster/item must carry to spawn at this skill (P_SpawnMapThing):
-- baby+easy need MTF_EASY(1), medium needs MTF_NORMAL(2), hard+nightmare need MTF_HARD(4).
W.SKILLNAME = { "I'm Too Young To Die", "Hey Not Too Rough", "Hurt Me Plenty", "Ultra-Violence", "Nightmare" }
function W.skillBit()
    local s = W.skill or 3
    if s <= 2 then return 1 elseif s == 3 then return 2 else return 4 end
end

function W.giveAmmo(at, clips)
    if not at then return false end
    if W.ammo[at] >= W.maxammo[at] then return false end
    local add = clips * W.CLIPAMMO[at]
    if W.skill == 1 or W.skill == 5 then add = add * 2 end   -- baby/nightmare: double ammo
    W.ammo[at] = min(W.ammo[at] + add, W.maxammo[at])
    return true
end

-- Apply a touched pickup; returns true if it did something (else it stays on the map).
function W.giveThing(th)
    local p = th.pk
    local k = p.k
    if k == "health" then
        if not p.always and W.health >= p.max then return false end
        W.health = min(W.health + p.amt, p.max); return true
    elseif k == "mega" then
        W.health = 200; W.armor = 200; W.armorType = 2; return true
    elseif k == "armor" then
        if p.pts <= W.armor then return false end
        W.armor = p.pts; W.armorType = p.atype; return true
    elseif k == "armorbonus" then
        if W.armor >= p.max then return false end
        W.armor = min(W.armor + p.amt, p.max)
        if W.armorType == 0 then W.armorType = 1 end
        return true
    elseif k == "ammo" then
        return W.giveAmmo(p.at, p.clips)
    elseif k == "backpack" then
        local took = false
        if not W.backpack then
            W.backpack = true
            for at, mx in pairs(W.maxammo) do W.maxammo[at] = mx * 2 end
            took = true
        end
        for at in pairs(W.ammo) do if W.giveAmmo(at, 1) then took = true end end
        return took
    elseif k == "weapon" then
        local gaveW = not W.weaponOwned[p.slot]
        if gaveW then W.weaponOwned[p.slot] = true; W.pendingWeapon = p.slot end
        local gaveA = p.at and W.giveAmmo(p.at, 2) or false
        return gaveW or gaveA
    elseif k == "key" then
        if W.keys[p.col] then return false end
        W.keys[p.col] = true; W.keyForm[p.col] = p.form; return true
    elseif k == "power" then
        if (W.powers[p.pw] or 0) > 0 and p.pw ~= "berserk" then return false end
        if p.heal then W.health = max(W.health, p.heal) end
        W.powers[p.pw] = (p.dur == -1) and 0x40000000 or p.dur
        return true
    end
    return false
end

-- End-of-frame item touch (DOOM P_TouchSpecialThing): radius overlap, give, remove.
function W.updatePickups()
    if not W.pickupThings then return end
    local px, py = W.viewX, W.viewY
    local bd = W.RADIUS + 20; local bd2 = bd * bd
    for _, th in ipairs(W.pickupThings) do
        if not th.removed then
            local dx = th.x - px; local dy = th.y - py
            if dx * dx + dy * dy <= bd2 and W.giveThing(th) then
                th.removed = true
                W.hudMsg = th.pk.msg; W.hudMsgUntil = now() + 2.5
                W.bonusCount = min(100, (W.bonusCount or 0) + 6)   -- BONUSADD
                if th.pk.count then W.itemCount = (W.itemCount or 0) + 1 end
                if th.pk.k == "weapon" then W.st.gotWeapon = true end  -- evil grin
                local kk = th.pk.k
                local sfx = (kk == "weapon") and "DSWPNUP"
                    or (kk == "power" or kk == "mega") and "DSGETPOW" or "DSITEMUP"
                pcall(W.playSfx, sfx)
            end
        end
    end
end

function W.selectSlot(n)
    local list = W.SLOTKEY[n]; if not list then return end
    if n == 1 and (W.powers.berserk or 0) ~= 0 then list = { 1, 8 } end  -- berserk: fist first
    local pick
    for _, s in ipairs(list) do if W.weaponOwned[s] then pick = s; break end end
    if not pick then return end
    if pick == W.curWeapon then                       -- same slot again: toggle the pair
        for _, s in ipairs(list) do
            if W.weaponOwned[s] and s ~= W.curWeapon then pick = s; break end
        end
    end
    if pick ~= W.curWeapon then W.pendingWeapon = pick end
end

-- Build the live-actor and pickup indices from the map THINGS (called per level).
-- Monsters/barrels get a .think tag + hp/z and enter W.thinkers (ticked once AI
-- lands); pickups get .pk and enter W.pickupThings; decor gets nothing. In place,
-- so renderThings/blocked keep reading the same table.
function W.spawnActors(map)
    W.thinkers = {}
    W.pickupThings = {}
    W.freeThingSlots = {}
    W.killCount = 0; W.itemCount = 0
    W.totalKills = 0; W.totalItems = 0
    -- Skill filter (P_SpawnMapThing): a thing spawns only if it is not multiplayer-
    -- only AND carries this skill's flag bit. Filtered things are marked removed so
    -- the renderer/collision/pickups all skip them (no frozen ghost monsters).
    local bit = W.skillBit()
    for _, th in ipairs(map.things) do
        local e = W.THING_SPR[th.dtype]
        if e then                                            -- only renderable/interactive things
            if (th.flags & 0x0010) == 0 and (th.flags & bit) ~= 0 then
                th.removed = false
                if e.kind == "monster" or e.spr == "BAR1" then
                    th.think = "monster"
                    th.info = W.MINFO[e.spr]
                    th.states = W.SSTATES[e.spr]
                    th.hp = (th.info and th.info.hp) or W.MONHP[e.spr] or 60
                    th.z = W.floorZFor((th.info and th.info.r) or e.r or 20, th.x, th.y)
                    th.dead = false
                    th.momx = 0; th.momy = 0
                    th.movedir = 8; th.movecount = 0
                    th.reaction = (W.skill == 5) and 0 or 8   -- info reactiontime (0 on NM)
                    th.threshold = 0
                    th.justhit = false; th.justattacked = false
                    th.ambush = (th.flags & 0x0008) ~= 0      -- deaf flag: sight-only wake
                    th.shadow = (th.dtype == 58)              -- spectre
                    th.target = nil; th.spr = nil; th.bright = false
                    if th.states then
                        -- spawn state set directly, no action (P_SpawnMobj semantics)
                        local st = th.states.stnd[1]
                        th.stkey = "stnd"; th.stidx = 1
                        th.frame = st.f; th.tics = st.t
                    else
                        th.frame = e.seq:sub(1, 1); th.tics = -1   -- statue species
                    end
                    if th.info and th.info.countkill then W.totalKills = W.totalKills + 1 end
                    W.thinkers[#W.thinkers + 1] = th
                elseif W.PICKUP[th.dtype] then
                    th.pk = W.PICKUP[th.dtype]
                    if th.pk.count then W.totalItems = W.totalItems + 1 end
                    W.pickupThings[#W.pickupThings + 1] = th
                end
            else
                th.removed = true                            -- mp-only or not on this skill: hide + inert
            end
        end
    end
end

----------------------------------------------------------------------
-- SECTION Id: actor tick (state machine, fx pool) + hitscan combat + weapons
-- Ported from DOOM p_pspr.c (weapons), p_map.c (P_LineAttack/P_RadiusAttack),
-- p_inter.c (P_DamageMobj), p_enemy.c/p_mobj.c (state frames + AI). Player weapons,
-- damage, pain/death animation, barrels, plus monster AI: A_Look sight/wakeup,
-- A_Chase 8-direction movement (P_NewChaseDir/P_Move with dropoff avoidance and
-- monster/player collision), and melee + hitscan attacks. Missile species walk up
-- and melee for now; their projectiles (imp/caco/baron fireballs) land in chunk 4.
----------------------------------------------------------------------
-- Spawn a short-lived cosmetic actor (puff/blood/fog/explosion) via the appended
-- thing pool so it draws + occludes like any billboard. frames = frame letters,
-- ftics = tics per frame (number or per-frame table). opts: bright, momz (u/tic),
-- startIdx (blood/melee-puff start mid-chain), spr required.
function W.spawnFx(spr, frames, ftics, x, y, z, opts)
    local idx = (#W.freeThingSlots > 0) and table.remove(W.freeThingSlots) or (#W.map.things + 1)
    local th = W.map.things[idx]
    if not th then th = {}; W.map.things[idx] = th end
    opts = opts or {}
    th.dtype = 30040; th.x = x; th.y = y; th.z = z; th.angle = 0; th.flags = 0
    th.think = "fx"; th.spr = spr; th.seq = frames; th.ftics = ftics
    th.frameIdx = opts.startIdx or 1
    th.frame = frames:sub(th.frameIdx, th.frameIdx)
    th.tics = (type(ftics) == "table") and ftics[th.frameIdx] or ftics
    th.bright = opts.bright or false
    th.momz = opts.momz or 0
    th.removed = false; th.dead = false; th.pk = nil; th._slot = idx
    th.info = nil; th.states = nil; th.proj = nil
    W.thinkers[#W.thinkers + 1] = th
end

-- One fx tic: rise/fall, then advance the frame chain; past the end -> removed.
function W.fxThink(th)
    if th.momz ~= 0 then th.z = th.z + th.momz end
    th.tics = th.tics - 1
    if th.tics > 0 then return end
    th.frameIdx = th.frameIdx + 1
    if th.frameIdx > #th.seq then th.removed = true; return end
    th.frame = th.seq:sub(th.frameIdx, th.frameIdx)
    th.tics = (type(th.ftics) == "table") and th.ftics[th.frameIdx] or th.ftics
end

-- P_SpawnMissile core: launch projectile kind from (x,y,z) at horizontal angle
-- ang (radians) with vertical momz (u/tic). owner ("player" or the firing
-- monster) is never hit by its own missile; a monster's missile also passes
-- through its own species (vanilla infighting rule). Plays the launch sound.
function W.spawnProjectile(kind, x, y, z, ang, momz, owner)
    local p = W.PROJ[kind]; if not p then return end
    local idx = (#W.freeThingSlots > 0) and table.remove(W.freeThingSlots) or (#W.map.things + 1)
    local th = W.map.things[idx]
    if not th then th = {}; W.map.things[idx] = th end
    th.dtype = 30040; th.x = x; th.y = y; th.z = z
    th.angle = ang * (180 / pi); th.flags = 0
    th.think = "proj"; th.st = "fly"; th.proj = p; th.owner = owner
    th.spr = p.flySpr; th.frameIdx = 1; th.frame = p.fly:sub(1, 1)
    th.tics = p.flyT; th.bright = true
    th.momx = cos(ang) * p.speed; th.momy = sin(ang) * p.speed; th.momz = momz or 0
    th.life = 20 * 35                                -- leak guard, tics (not vanilla)
    th.removed = false; th.dead = false; th.pk = nil; th._slot = idx
    th.info = nil; th.states = nil
    if p.seesfx then pcall(W.playSfx, p.seesfx) end
    W.thinkers[#W.thinkers + 1] = th
end

-- P_ExplodeMissile: stop, enter the explosion frames (first tics shortened by
-- P_Random&3 like vanilla), apply the direct-hit roll and any A_Explode splash.
-- The BFG ball defers its tracer spray to explosion frame 3 (S_BFGLAND3).
function W.projExplode(th, hit)
    local p = th.proj
    th.st = "boom"; th.momx = 0; th.momy = 0; th.momz = 0
    th.spr = p.boomSpr; th.seq = p.boom; th.frameIdx = 1; th.frame = p.boom:sub(1, 1)
    local t0 = (type(p.boomT) == "table") and p.boomT[1] or p.boomT
    t0 = t0 - (W.pRandom() & 3); if t0 < 1 then t0 = 1 end
    th.tics = t0
    th.sprayPend = p.spray or false
    if p.dsfx then pcall(W.playSfx, p.dsfx) end
    local dmg = (W.pRandom() % 8 + 1) * p.dmg
    if hit then W.damageMobj(hit, dmg, th, th.owner) end
    if (p.splash or 0) > 0 then W.radiusDamage(th.x, th.y, p.splash, p.splash, th, th.owner) end
end

-- A_BFGSpray: 40 tracer rays over a 90 degree cone from the SHOOTER toward where
-- the ball hit; each visible target takes the sum of 15 rolls of (P_Random&7)+1
-- and gets a BFE2 flash at 1/4 body height. Fires on explosion frame 3.
function W.bfgSpray(th)
    local ox, oy, oz = W.tgtPos(th.owner or "player")
    local sz = oz + 36
    local base = th.angle * (pi / 180)
    for i = 0, 39 do
        local an = base - pi / 4 + (pi / 2) * (i / 40)
        local _, tgt = W.aimLineAttack(th.owner or "player", ox, oy, sz, an, 1024)
        if tgt and tgt ~= "player" then
            local tx, ty, tz, hh = W.tgtPos(tgt)
            W.spawnFx("BFE2", "ABCD", 8, tx, ty, tz + hh / 4, { bright = true })
            local dmg = 0
            for _ = 1, 15 do dmg = dmg + (W.pRandom() & 7) + 1 end
            W.damageMobj(tgt, dmg, nil, th.owner)
        end
    end
end

-- Missile per-tic: animate, substep (<=8u) the move testing wall / thing /
-- player / floor-ceiling; explode on the first hit. A missile whose blocking
-- line fronts an F_SKY1 ceiling vanishes without exploding (vanilla sky hack).
function W.projThink(th)
    if th.st == "boom" then
        th.tics = th.tics - 1
        if th.tics <= 0 then
            th.frameIdx = th.frameIdx + 1
            if th.frameIdx > #th.seq then th.removed = true; return end
            th.frame = th.seq:sub(th.frameIdx, th.frameIdx)
            th.tics = (type(th.proj.boomT) == "table") and th.proj.boomT[th.frameIdx] or th.proj.boomT
            if th.frameIdx == 3 and th.sprayPend then th.sprayPend = false; W.bfgSpray(th) end
        end
        return
    end
    th.tics = th.tics - 1
    if th.tics <= 0 then
        th.frameIdx = (th.frameIdx % #th.proj.fly) + 1
        th.frame = th.proj.fly:sub(th.frameIdx, th.frameIdx); th.tics = th.proj.flyT
    end
    th.life = th.life - 1
    if th.life <= 0 then th.removed = true; return end
    local mx, my, mz = th.momx, th.momy, th.momz
    local hspeed = sqrt(mx * mx + my * my); if hspeed < 1 then hspeed = 1 end
    local steps = ceil(hspeed / 8)
    local sdt = 1 / steps
    local things = W.map.things
    local ownerSpr = (th.owner and th.owner ~= "player") and (th.owner.sprOv or (W.THING_SPR[th.owner.dtype] or {}).spr) or nil
    for _ = 1, steps do
        local ox, oy, oz = th.x, th.y, th.z
        local segdx, segdy = mx * sdt, my * sdt
        local seglen = sqrt(segdx * segdx + segdy * segdy); if seglen < 1e-4 then seglen = 1e-4 end
        local ndx, ndy = segdx / seglen, segdy / seglen
        local wd, wline = W.rayWallDist(ox, oy, ndx, ndy, seglen, oz)
        local hitThing, hitAlong = nil, min(seglen, wd)
        for _, o in ipairs(things) do
            local oe = W.THING_SPR[o.dtype]
            if oe and oe.r and o ~= th.owner and not o.dead and not o.removed and (o.flags & 0x0010) == 0
                and not (ownerSpr and oe.spr == ownerSpr) then       -- same species: fly through
                local rx, ry = o.x - ox, o.y - oy
                local along = rx * ndx + ry * ndy
                if along > 0 and along < hitAlong then
                    local perp = abs(rx * (-ndy) + ry * ndx)
                    local oz2 = o.z
                    local oh = (W.MINFO[oe.spr] and W.MINFO[oe.spr].h) or 64
                    if perp <= oe.r + th.proj.r
                        and (not oz2 or (oz + 8 >= oz2 and oz <= oz2 + oh)) then
                        hitThing = o; hitAlong = along
                    end
                end
            end
        end
        if th.owner ~= "player" then                     -- only monster missiles hit the player
            local rx, ry = W.viewX - ox, W.viewY - oy
            local along = rx * ndx + ry * ndy
            local pz0 = W.pz
            if along > 0 and along < hitAlong and oz + 8 >= pz0 and oz <= pz0 + W.PHEIGHT then
                local perp = abs(rx * (-ndy) + ry * ndx)
                if perp <= W.RADIUS + th.proj.r then hitThing = "player"; hitAlong = along end
            end
        end
        if hitThing then
            th.x = ox + ndx * hitAlong; th.y = oy + ndy * hitAlong
            th.z = oz + mz * sdt * (hitAlong / seglen)
            W.projExplode(th, hitThing); return
        end
        if wd < seglen then
            th.x = ox + ndx * wd; th.y = oy + ndy * wd
            th.z = oz + mz * sdt * (wd / seglen)
            -- sky hack: a missile that hits an upper wall fronting a sky ceiling vanishes
            if wline and wline.back ~= NONE and wline.front ~= NONE then
                local bsd = W.map.sidedefs[wline.back + 1]
                local bsec = bsd and W.map.sectors[bsd.sector + 1]
                local fsd = W.map.sidedefs[wline.front + 1]
                local fsec = fsd and W.map.sectors[fsd.sector + 1]
                local far = bsec
                if bsec and fsec then
                    -- pick whichever side the missile is NOT in as the far sector
                    local cur = W.sectorAt(ox, oy)
                    far = (cur == bsec) and fsec or bsec
                end
                if far and far.ceilTex == "F_SKY1" and th.z > far.ceil - 8 then
                    th.removed = true; return
                end
            end
            W.projExplode(th, nil); return
        end
        th.x = ox + segdx; th.y = oy + segdy; th.z = oz + mz * sdt
        local sec = W.sectorAt(th.x, th.y)
        if sec and th.z >= sec.ceil then
            if sec.ceilTex == "F_SKY1" then th.removed = true; return end
            W.projExplode(th, nil); return
        end
        if sec and th.z <= sec.floor then W.projExplode(th, nil); return end
    end
end

----------------------------------------------------------------------
-- Monster state machine core (P_SetMobjState). A thing's state = (chain key,
-- index) into W.SSTATES[species]; actions run on state ENTRY; a 0-tic state
-- falls straight through to the next. t=-1 freezes (corpse). Advancing past
-- the end: stnd/run loop, atk/pain fall back to run, die/xdie removes (barrel).
----------------------------------------------------------------------
function W.setMState(th, key, idx)
    local chains = th.states; if not chains then return end
    local ch = chains[key]
    if not ch and key == "xdie" then key = "die"; ch = chains.die end
    if not ch then return end
    while true do
        local st = ch[idx]
        if not st then
            if key == "die" or key == "xdie" then th.removed = true; th.think = nil; return end
            idx = 1; st = ch[1]
        end
        th.stkey = key; th.stidx = idx
        if st.f then th.frame = st.f end
        th.spr = st.s                       -- sprite prefix override (barrel BEXP) or nil
        th.bright = st.b or false
        th.tics = st.t
        if st.a then
            local fn = W.MACT[st.a]
            if fn then fn(th) end
            if th.removed or not th.think then return end
            if th.stkey ~= key or th.stidx ~= idx then return end   -- action switched state
        end
        if th.tics ~= 0 then return end
        idx = idx + 1
    end
end

function W.advMState(th)
    local ch = th.states and th.states[th.stkey]
    if not ch then return end
    local nidx = th.stidx + 1
    if not ch[nidx] then
        local k = th.stkey
        if k == "atk" or k == "pain" then W.setMState(th, "run", 1); return end
        if k == "die" or k == "xdie" then th.removed = true; th.think = nil; return end
        nidx = 1
    end
    W.setMState(th, th.stkey, nidx)
end

-- Target helpers: a monster's target is "player" or another live monster.
function W.tgtPos(t)
    if t == "player" or t == nil then return W.viewX, W.viewY, W.pz, W.PHEIGHT, W.RADIUS end
    local e = W.THING_SPR[t.dtype]
    local mi = t.info or (e and W.MINFO[e.spr])
    return t.x, t.y, t.z or 0, (mi and mi.h) or 56, (mi and mi.r) or (e and e.r) or 20
end

function W.tgtAlive(t)
    if t == "player" then return not W.playerDead end
    if type(t) ~= "table" then return false end
    return not (t.dead or t.removed)
end

function W.tgtShadow(t)
    if t == "player" then return (W.powers and (W.powers.invis or 0) ~= 0) and true or false end
    return type(t) == "table" and t.shadow or false
end

-- Straight-line distance from a monster to its target.
function W.distToTarget(th)
    local tx, ty = W.tgtPos(th.target)
    local dx, dy = tx - th.x, ty - th.y
    return sqrt(dx * dx + dy * dy)
end

-- P_CheckSight (linuxdoom p_sight.c), minus the BSP/REJECT acceleration: true iff
-- the 3D sight line from the looker eye (x1,y1,z1) to the target box (x2,y2,
-- zbot..ztop) is unobstructed. It traces the SLOPED line and keeps a vertical cone
-- [bottomslope, topslope]; at every two-sided line the trace crosses it raises the
-- floor slope / lowers the ceiling slope by the opening at that crossing (slope =
-- (open - z1)/frac, frac = fraction along the trace). A one-sided line, a closed
-- opening, or the cone pinching shut (topslope <= bottomslope) blocks sight. This
-- is why a monster in a pit or below a step can no longer "see" over the lip: the
-- flat-Z rayWallDist ignored the opening slope; this does not. See DoomSrc/p_sight.c.
function W.checkSight(x1, y1, z1, x2, y2, zbot, ztop)
    local topslope = ztop - z1
    local bottomslope = zbot - z1
    if topslope <= bottomslope then return false end
    local V, LD, SD, SE = W.map.vertexes, W.map.linedefs, W.map.sidedefs, W.map.sectors
    for _, ld in ipairs(LD) do
        local a = V[ld.v1 + 1]; local b = V[ld.v2 + 1]
        if a and b then
            local t, u = W.raySeg(x1, y1, x2, y2, a.x, a.y, b.x, b.y)
            if t and t > 1e-4 and t < 1 and u >= 0 and u <= 1 then   -- trace crosses this line
                if ld.back == NONE or ld.front == NONE then return false end   -- one-sided wall
                local fsd = SD[ld.front + 1]; local bsd = SD[ld.back + 1]
                local fsec = fsd and SE[fsd.sector + 1]; local bsec = bsd and SE[bsd.sector + 1]
                if not (fsec and bsec) then return false end
                local ff, bf, fc, bc = fsec.floor, bsec.floor, fsec.ceil, bsec.ceil
                if not (ff == bf and fc == bc) then                  -- a real step/lip here
                    local opentop = (fc < bc) and fc or bc
                    local openbottom = (ff > bf) and ff or bf
                    if openbottom >= opentop then return false end   -- closed
                    if ff ~= bf then
                        local slope = (openbottom - z1) / t
                        if slope > bottomslope then bottomslope = slope end
                    end
                    if fc ~= bc then
                        local slope = (opentop - z1) / t
                        if slope < topslope then topslope = slope end
                    end
                    if topslope <= bottomslope then return false end
                end
            end
        end
    end
    return true
end

-- P_CheckSight wrapper: can the monster see its target? Vanilla eye height is
-- z + 3/4 of the looker's height; the target's full body box is the aim window.
function W.monsterSees(th, tgt)
    tgt = tgt or th.target or "player"
    if not W.tgtAlive(tgt) then return false end
    local tx, ty, tz, hh = W.tgtPos(tgt)
    local dx, dy = tx - th.x, ty - th.y
    if dx * dx + dy * dy > W.SIGHT_RANGE * W.SIGHT_RANGE then return false end
    local mh = (th.info and th.info.h) or 56
    local z1 = (th.z or 0) + mh * 0.75
    return W.checkSight(th.x, th.y, z1, tx, ty, tz, tz + hh)
end

-- A_FaceTarget (WAD degrees). Aiming at a shadow target (spectre / blur-sphere
-- player) fuzzes the angle by (P_Random-P_Random)<<21 like vanilla.
function W.faceTarget(th)
    if not th.target then return end
    th.ambush = false
    local tx, ty = W.tgtPos(th.target)
    th.angle = atan(ty - th.y, tx - th.x) * (180 / pi)
    if W.tgtShadow(th.target) then
        th.angle = th.angle + (W.pRandom() - W.pRandom()) * (45 / 256)
    end
end

-- P_CheckMeleeRange: target within claw/bite reach and in sight.
-- Center-to-center: dist < MELEERANGE(64) - 20 + target radius.
function W.checkMeleeRange(th)
    if not th.target then return false end
    local _, _, _, _, tr = W.tgtPos(th.target)
    if W.distToTarget(th) >= 64 - 20 + tr then return false end
    return W.monsterSees(th)
end

-- P_CheckMissileRange: distance-scaled attack decision, with the vanilla
-- retaliation (just-hit) fast path and per-species range shaping.
function W.checkMissileRange(th)
    if not W.monsterSees(th) then return false end
    if th.justhit then th.justhit = false; return true end   -- fight back NOW
    if (th.reaction or 0) > 0 then return false end
    local dist = W.distToTarget(th) - 64
    if not (th.info and th.info.melee) then dist = dist - 128 end  -- no melee: fire more
    local e = W.THING_SPR[th.dtype]
    if e and e.spr == "HEAD" then dist = dist * 0.5 end
    if dist > 200 then dist = 200 end
    if W.pRandom() < dist then return false end
    return true
end

-- P_LookForPlayers (single player). allaround=false limits the wake to the 180
-- degree cone in front of the monster unless the player is within MELEERANGE.
function W.lookForPlayer(th, allaround)
    if W.playerDead then return false end
    if not W.checkSight(th.x, th.y, (th.z or 0) + ((th.info and th.info.h) or 56) * 0.75,
        W.viewX, W.viewY, W.pz, W.pz + W.PHEIGHT) then return false end
    if not allaround then
        local an = atan(W.viewY - th.y, W.viewX - th.x) * (180 / pi) - (th.angle or 0)
        an = (an + 180) % 360 - 180
        if an > 90 or an < -90 then                       -- behind its back
            local dx, dy = W.viewX - th.x, W.viewY - th.y
            if dx * dx + dy * dy > 64 * 64 then return false end
        end
    end
    th.target = "player"
    return true
end

-- Wake a monster into the hunt (see-you path): sight cry + run chain.
function W.wakeMonster(th)
    if not th.states or not th.states.run then return end
    local mi = th.info
    if mi and mi.sight and th.stkey == "stnd" then
        pcall(W.playSfx, W.sndPick(mi.sight, mi.sightN))
    end
    th.threshold = 0
    W.setMState(th, "run", 1)
end

-- Generalized P_CheckPosition for a monster's bounding box at (nx,ny). Returns
-- (blocked, tmfloor, tmdropoff, floatok): blocked if the box crosses a one-sided/
-- blocking/block-monsters line, the vertical opening is too short, the step up
-- exceeds MAXSTEP, it would stand over a dropoff > MAXSTEP (non-floaters only),
-- or it overlaps another solid thing or the player. Floaters skip the height/
-- step/dropoff gates. floatok = an opening tall enough exists, only the z gates
-- failed (P_Move nudges a floater vertically then). Crossed special lines are
-- collected into W.spechit (vanilla spechit[]) so a blocked monster can open a
-- manual door it walked into.
function W.monBlocked(th, nx, ny)
    local se = W.THING_SPR[th.dtype]
    local mi = th.info
    local R = (mi and mi.r) or (se and se.r) or 20
    local H = (mi and mi.h) or 56
    local bl, br, bb, bt = nx - R, nx + R, ny - R, ny + R
    local sec = W.sectorAt(nx, ny)
    if not sec then return true end
    local tmfloor, tmceil, tmdrop = sec.floor, sec.ceil, sec.floor
    local spechit = W.spechit
    if spechit then for i = #spechit, 1, -1 do spechit[i] = nil end
    else spechit = {}; W.spechit = spechit end
    local V, LD, SD, SE = W.map.vertexes, W.map.linedefs, W.map.sidedefs, W.map.sectors
    for _, ld in ipairs(LD) do
        local a = V[ld.v1 + 1]; local b = V[ld.v2 + 1]
        if a and b then
            local lminx = (a.x < b.x) and a.x or b.x; local lmaxx = (a.x < b.x) and b.x or a.x
            local lminy = (a.y < b.y) and a.y or b.y; local lmaxy = (a.y < b.y) and b.y or a.y
            if br > lminx and bl < lmaxx and bt > lminy and bb < lmaxy
                and boxOnLineSide(bl, br, bb, bt, a.x, a.y, b.x - a.x, b.y - a.y) == -1 then
                if ld.back == NONE or ld.front == NONE then return true end   -- one-sided
                if (ld.flags & 0x0001) ~= 0 then return true end             -- ML_BLOCKING
                if (ld.flags & 0x0002) ~= 0 then return true end             -- ML_BLOCKMONSTERS
                local fsd = SD[ld.front + 1]; local bsd = SD[ld.back + 1]
                local fsec = fsd and SE[fsd.sector + 1]
                local bsec = bsd and SE[bsd.sector + 1]
                if not (fsec and bsec) then return true end
                local ot = (fsec.ceil < bsec.ceil) and fsec.ceil or bsec.ceil
                local ob = (fsec.floor > bsec.floor) and fsec.floor or bsec.floor
                local lo = (fsec.floor < bsec.floor) and fsec.floor or bsec.floor
                if ot < tmceil then tmceil = ot end
                if ob > tmfloor then tmfloor = ob end
                if lo < tmdrop then tmdrop = lo end
                if (ld.special or 0) ~= 0 then spechit[#spechit + 1] = ld end
            end
        end
    end
    local floatok = (tmceil - tmfloor) >= H
    local feet = th.z or tmfloor
    if not (mi and mi.float) then
        if not floatok then return true, tmfloor, tmdrop, false end
        if tmfloor - feet > W.MAXSTEP then return true, tmfloor, tmdrop, floatok end
        if tmfloor - tmdrop > W.MAXSTEP then return true, tmfloor, tmdrop, floatok end
    else
        -- floaters still cannot pass a too-short opening at their current z
        if not floatok then return true, tmfloor, tmdrop, false end
        if feet + H > tmceil or feet < tmfloor - W.FLOATSPEED * 4 then
            return true, tmfloor, tmdrop, floatok
        end
    end
    for _, o in ipairs(W.map.things) do
        if o ~= th then
            local oe = W.THING_SPR[o.dtype]
            if oe and oe.r and (o.flags & 0x0010) == 0 and not o.dead and not o.removed then
                local rr = R + oe.r
                if abs(nx - o.x) < rr and abs(ny - o.y) < rr then return true, tmfloor, tmdrop, floatok end
            end
        end
    end
    local pr = R + W.RADIUS
    if abs(nx - W.viewX) < pr and abs(ny - W.viewY) < pr then return true, tmfloor, tmdrop, floatok end
    return false, tmfloor, tmdrop, floatok
end

-- P_Move: one step of info.speed along movedir via the box test. On a block:
-- floaters with a usable opening nudge vertically (FLOATSPEED); walkers that
-- crossed a manual-door line open it (spechit, special 1 only) and stall one
-- think. Walkers snap to the destination floor; success fires walk-over lines.
function W.pMove(th)
    if th.movedir == nil or th.movedir >= 8 then return false end
    local mi = th.info
    local sp = mi.speed or 8
    local nx = th.x + W.DIRX[th.movedir + 1] * sp
    local ny = th.y + W.DIRY[th.movedir + 1] * sp
    local blk, fz, _, floatok = W.monBlocked(th, nx, ny)
    if blk then
        if mi.float and floatok and fz then              -- adjust height through the opening
            if (th.z or 0) < fz then th.z = (th.z or 0) + W.FLOATSPEED
            else th.z = (th.z or 0) - W.FLOATSPEED end
            return true
        end
        local spechit = W.spechit
        if not spechit or #spechit == 0 then return false end
        th.movedir = 8
        local good = false
        for i = 1, #spechit do
            local ld = spechit[i]
            if ld.special == 1 then                      -- manual raise door: monsters may open
                W.evVerticalDoor(ld); good = true
            end
        end
        return good
    end
    local ox, oy = th.x, th.y
    th.x = nx; th.y = ny
    if not mi.float and fz then th.z = fz end
    W.crossLines(ox, oy, nx, ny, false, th)
    return true
end

-- P_TryWalk: a successful step also re-arms the heading commitment.
function W.tryWalk(th)
    if not W.pMove(th) then return false end
    th.movecount = W.pRandom() & 15
    return true
end

-- P_NewChaseDir: choose an 8-way heading toward the target, trying the direct
-- diagonal, then each axis (larger-delta first, with the vanilla 200/256 random
-- swap), the old heading, a randomized full sweep, then the turnaround.
function W.newChaseDir(th)
    local olddir = th.movedir or 8
    local turn = W.OPPOSITE[olddir]
    local tx, ty = W.tgtPos(th.target)
    local dxp, dyp = tx - th.x, ty - th.y
    local d1, d2 = 8, 8
    if dxp > 10 then d1 = 0 elseif dxp < -10 then d1 = 4 end          -- EAST / WEST
    if dyp < -10 then d2 = 6 elseif dyp > 10 then d2 = 2 end          -- SOUTH / NORTH
    if d1 ~= 8 and d2 ~= 8 then
        local idx = ((dyp < 0) and 2 or 0) + ((dxp > 0) and 1 or 0)
        th.movedir = W.DIAGS[idx + 1]
        if th.movedir ~= turn and W.tryWalk(th) then return end
    end
    if W.pRandom() > 200 or abs(dyp) > abs(dxp) then d1, d2 = d2, d1 end
    if d1 == turn then d1 = 8 end
    if d2 == turn then d2 = 8 end
    if d1 ~= 8 then th.movedir = d1; if W.tryWalk(th) then return end end
    if d2 ~= 8 then th.movedir = d2; if W.tryWalk(th) then return end end
    if olddir ~= 8 then th.movedir = olddir; if W.tryWalk(th) then return end end
    if (W.pRandom() & 1) ~= 0 then
        for t = 0, 7 do
            if t ~= turn then th.movedir = t; if W.tryWalk(th) then return end end
        end
    else
        for t = 7, 0, -1 do
            if t ~= turn then th.movedir = t; if W.tryWalk(th) then return end end
        end
    end
    if turn ~= 8 then th.movedir = turn; if W.tryWalk(th) then return end end
    th.movedir = 8      -- DI_NODIR: boxed in, stand and keep trying
end

-- Hitscan/missile source height: vanilla shootz = z + height/2 + 8.
function W.monShootZ(th)
    return (th.z or 0) + ((th.info and th.info.h or 56) * 0.5) + 8
end

-- P_SpawnMissile: from the monster at z+32 toward the target's feet; momz uses
-- the vanilla flight-time division; shadow targets fuzz the launch angle.
function W.spawnMonMissile(th, kind)
    local p = W.PROJ[kind]; if not p then return end
    local tx, ty, tz = W.tgtPos(th.target)
    local ang = atan(ty - th.y, tx - th.x)
    if W.tgtShadow(th.target) then ang = ang + (W.pRandom() - W.pRandom()) * (pi / 2048) end
    local dx, dy = tx - th.x, ty - th.y
    local flight = sqrt(dx * dx + dy * dy) / p.speed
    if flight < 1 then flight = 1 end
    W.spawnProjectile(kind, th.x, th.y, (th.z or 0) + 32, ang, (tz - (th.z or 0)) / flight, th)
end

----------------------------------------------------------------------
-- Monster action routines (p_enemy.c), dispatched by state entry via W.MACT.
----------------------------------------------------------------------
-- A_Look: wake on the sector's flooded sound target (AMBUSH monsters need
-- sight too) or on a player inside the 180 degree front cone.
function W.actLook(th)
    th.threshold = 0
    local sec = W.sectorAt(th.x, th.y)
    local targ = sec and sec.soundTarget
    local woke = false
    if targ and W.tgtAlive(targ) then
        th.target = targ
        if th.ambush then
            if W.monsterSees(th, targ) then woke = true end
        else
            woke = true
        end
    end
    if not woke and not W.lookForPlayer(th, false) then return end
    W.wakeMonster(th)
end

-- A_Chase: the full vanilla decision ladder, one call per run-state entry.
function W.actChase(th)
    local mi = th.info
    if (th.reaction or 0) > 0 then th.reaction = th.reaction - 1 end
    if (th.threshold or 0) > 0 then                       -- fixate on the current target
        if not W.tgtAlive(th.target) then th.threshold = 0
        else th.threshold = th.threshold - 1 end
    end
    if (th.movedir or 8) < 8 then                         -- turn toward movedir in 45s
        th.angle = (th.angle or 0) % 360
        th.angle = th.angle - (th.angle % 45)
        local delta = ((th.angle - th.movedir * 45) + 180) % 360 - 180
        if delta > 0 then th.angle = th.angle - 45
        elseif delta < 0 then th.angle = th.angle + 45 end
    end
    if not th.target or not W.tgtAlive(th.target) then
        if W.lookForPlayer(th, true) then return end
        W.setMState(th, "stnd", 1)                        -- nothing left to chase
        return
    end
    if th.justattacked then                               -- do not attack twice in a row
        th.justattacked = false
        if W.skill ~= 5 then W.newChaseDir(th) end
        return
    end
    if mi.melee and W.checkMeleeRange(th) then
        if mi.atksfx then pcall(W.playSfx, mi.atksfx) end
        W.setMState(th, "atk", 1)
        return
    end
    if mi.missile and (W.skill == 5 or (th.movecount or 0) <= 0) and W.checkMissileRange(th) then
        W.setMState(th, "atk", 1)
        th.justattacked = true
        return
    end
    th.movecount = (th.movecount or 0) - 1
    if th.movecount < 0 or not W.pMove(th) then
        W.newChaseDir(th)
    end
    if mi.act and W.pRandom() < 3 then                    -- occasional active grunt
        pcall(W.playSfx, mi.act)
    end
end

function W.actPosAttack(th)
    if not th.target then return end
    W.faceTarget(th)
    local base = (th.angle or 0) * (pi / 180)
    local sz = W.monShootZ(th)
    local slope = W.aimLineAttack(th, th.x, th.y, sz, base, 2048)
    pcall(W.playSfx, "DSPISTOL")
    local ang = base + (W.pRandom() - W.pRandom()) * (pi / 2048)
    W.lineAttack(th, th.x, th.y, sz, ang, 2048, slope, (W.pRandom() % 5 + 1) * 3)
end

function W.actSPosAttack(th)
    if not th.target then return end
    pcall(W.playSfx, "DSSHOTGN")
    W.faceTarget(th)
    local base = (th.angle or 0) * (pi / 180)
    local sz = W.monShootZ(th)
    local slope = W.aimLineAttack(th, th.x, th.y, sz, base, 2048)
    for _ = 1, 3 do
        local ang = base + (W.pRandom() - W.pRandom()) * (pi / 2048)
        W.lineAttack(th, th.x, th.y, sz, ang, 2048, slope, (W.pRandom() % 5 + 1) * 3)
    end
end

function W.actTroopAttack(th)
    if not th.target then return end
    W.faceTarget(th)
    if W.checkMeleeRange(th) then
        pcall(W.playSfx, "DSCLAW")
        W.damageMobj(th.target, (W.pRandom() % 8 + 1) * 3, th, th)
        return
    end
    W.spawnMonMissile(th, "TROOPSHOT")
end

function W.actSargAttack(th)
    if not th.target then return end
    W.faceTarget(th)
    if W.checkMeleeRange(th) then
        W.damageMobj(th.target, (W.pRandom() % 10 + 1) * 4, th, th)
    end
end

function W.actHeadAttack(th)
    if not th.target then return end
    W.faceTarget(th)
    if W.checkMeleeRange(th) then
        W.damageMobj(th.target, (W.pRandom() % 6 + 1) * 10, th, th)
        return
    end
    W.spawnMonMissile(th, "HEADSHOT")
end

function W.actBruisAttack(th)
    if not th.target then return end
    if W.checkMeleeRange(th) then
        pcall(W.playSfx, "DSCLAW")
        W.damageMobj(th.target, (W.pRandom() % 8 + 1) * 10, th, th)
        return
    end
    W.spawnMonMissile(th, "BRUISERSHOT")
end

function W.actScream(th)
    local mi = th.info
    if mi and mi.dsfx then pcall(W.playSfx, W.sndPick(mi.dsfx, mi.dsfxN)) end
    if not mi and th.states == W.SSTATES.BAR1 then pcall(W.playSfx, "DSBAREXP") end
end

function W.actXScream(th)
    pcall(W.playSfx, "DSSLOP")
end

function W.actPain(th)
    local mi = th.info
    if mi and mi.psfx then pcall(W.playSfx, mi.psfx) end
end

function W.actFall(th)
    -- vanilla clears MF_SOLID here; th.dead already stopped blocking at kill time
end

-- A_Explode (barrel): 128/128 splash credited to whoever killed the barrel.
function W.actExplode(th)
    W.radiusDamage(th.x, th.y, 128, 128, th, th.target)
end

-- A_BossDeath: on E1M8, when the last Baron dies, floor tag 666 lowers to the
-- lowest neighbour (opens the exit yard). Other boss maps need species that are
-- not simulated yet, so only the E1 gate is armed.
function W.actBossDeath(th)
    local nm = W.map and W.map.name or ""
    local ep, mp = nm:match("^E(%d)M(%d)$")
    if not (ep == "1" and mp == "8") then return end
    local e = W.THING_SPR[th.dtype]
    if not (e and e.spr == "BOSS") then return end
    if W.playerDead then return end
    for _, o in ipairs(W.thinkers) do
        if o ~= th and o.think == "monster" and not o.dead and not o.removed then
            local oe = W.THING_SPR[o.dtype]
            if oe and oe.spr == "BOSS" then return end     -- a Baron still lives
        end
    end
    W.evDoFloor({ tag = 666, front = NONE, back = NONE }, "lowerFloorToLowest")
end

W.MACT = {
    look = W.actLook, chase = W.actChase, face = W.faceTarget,
    posatk = W.actPosAttack, sposatk = W.actSPosAttack, troopatk = W.actTroopAttack,
    sargatk = W.actSargAttack, headatk = W.actHeadAttack, bruisatk = W.actBruisAttack,
    scream = W.actScream, xscream = W.actXScream, pain = W.actPain, fall = W.actFall,
    explode = W.actExplode, bossdeath = W.actBossDeath,
}

-- One monster tic: damage-thrust knockback (friction 0.90625, STOPSPEED 1/16),
-- then the state clock (t=-1 corpses never advance).
function W.monsterThink(th)
    if th.momx and (th.momx ~= 0 or th.momy ~= 0) then
        local nx, ny = th.x + th.momx, th.y + th.momy
        if not W.monBlocked(th, nx, ny) then th.x = nx; th.y = ny end
        th.momx = th.momx * 0.90625; th.momy = th.momy * 0.90625
        if th.momx > -0.0625 and th.momx < 0.0625 and th.momy > -0.0625 and th.momy < 0.0625 then
            th.momx = 0; th.momy = 0
        end
    end
    if not th.info then return end          -- statue species: renderable, no AI
    if th.tics == -1 then return end
    th.tics = (th.tics or 1) - 1
    if th.tics <= 0 then W.advMState(th) end
end

W.THINK = { monster = W.monsterThink, fx = W.fxThink, proj = W.projThink }

-- Advance every live thing one TIC; swap-remove finished ones (recycle slots).
function W.updateActors()
    local list = W.thinkers; if not list then return end
    for i = #list, 1, -1 do
        local th = list[i]
        if th.removed or not th.think then
            list[i] = list[#list]; list[#list] = nil
            if th.removed and th._slot then W.freeThingSlots[#W.freeThingSlots + 1] = th._slot end
        else
            local fn = W.THINK[th.think]; if fn then fn(th) end
        end
    end
end

-- Nearest bullet-stopping distance along a ray (blockmap-free). A one-sided line
-- always stops; a two-sided line stops only if the shot's z AT THE CROSSING
-- (shootZ + slope*dist) is outside its live opening, so sloped shots clear lips
-- and window sills exactly like PTR_ShootTraverse. Returns (dist, line).
function W.rayWallDist(x1, y1, dx, dy, range, shootZ, slope)
    slope = slope or 0
    local x2, y2 = x1 + dx * range, y1 + dy * range
    local V, LD, SD, SE = W.map.vertexes, W.map.linedefs, W.map.sidedefs, W.map.sectors
    local best, bestLd = range, nil
    for _, ld in ipairs(LD) do
        local a = V[ld.v1 + 1]; local b = V[ld.v2 + 1]
        if a and b then
            local t, u = W.raySeg(x1, y1, x2, y2, a.x, a.y, b.x, b.y)
            if t and t >= 0 and t <= 1 and u >= 0 and u <= 1 then
                local d = t * range
                if d < best then
                    local stops
                    if ld.back == NONE or ld.front == NONE then stops = true
                    else
                        local fsd = SD[ld.front + 1]; local bsd = SD[ld.back + 1]
                        local fsec = fsd and SE[fsd.sector + 1]; local bsec = bsd and SE[bsd.sector + 1]
                        if fsec and bsec then
                            local ot = min(fsec.ceil, bsec.ceil); local ob = max(fsec.floor, bsec.floor)
                            local zc = shootZ + slope * d
                            stops = (zc <= ob or zc >= ot)
                        else stops = true end
                    end
                    if stops then best = d; bestLd = ld end
                end
            end
        end
    end
    return best, bestLd
end

-- P_LineAttack: one hitscan ray from src ("player" or a monster). Walls stop it
-- (slope-aware); the nearest shootable thing before the wall takes the damage.
-- Monster shots can hit the player AND other monsters (infighting). Blood spawns
-- on flesh (state skips by damage size), rising puffs on walls (pulled back 4u,
-- melee puffs start at the small frame). Returns (victim or nil, distance).
function W.lineAttack(src, x1, y1, shootZ, ang, range, slope, dmg)
    slope = slope or 0
    local dx, dy = cos(ang), sin(ang)
    local wd = W.rayWallDist(x1, y1, dx, dy, range, shootZ, slope)
    local best, bestAlong = nil, wd
    for _, th in ipairs(W.map.things) do
        if th ~= src and th.think == "monster" and not th.dead and not th.removed
            and (th.flags & 0x0010) == 0 then
            local e = W.THING_SPR[th.dtype]
            if e and e.r then
                local rx, ry = th.x - x1, th.y - y1
                local along = rx * dx + ry * dy
                if along > 0 and along < bestAlong then
                    local perp = abs(rx * (-dy) + ry * dx)
                    if perp <= e.r then
                        local bz = shootZ + slope * along
                        local mi = th.info or W.MINFO[e.spr]
                        local oz, oh = th.z or 0, (mi and mi.h) or 56
                        if bz >= oz and bz <= oz + oh then
                            best = th; bestAlong = along
                        end
                    end
                end
            end
        end
    end
    if src ~= "player" and not W.playerDead then
        local rx, ry = W.viewX - x1, W.viewY - y1
        local along = rx * dx + ry * dy
        if along > 0 and along < bestAlong then
            local perp = abs(rx * (-dy) + ry * dx)
            if perp <= W.RADIUS then
                local bz = shootZ + slope * along
                if bz >= W.pz and bz <= W.pz + W.PHEIGHT then
                    best = "player"; bestAlong = along
                end
            end
        end
    end
    if best then
        local hx, hy = x1 + dx * bestAlong, y1 + dy * bestAlong
        local hz = shootZ + slope * bestAlong + (W.pRandom() - W.pRandom()) * (4 / 255)
        local noblood = best ~= "player" and best.info and best.info.noblood
        if noblood then
            W.spawnFx("PUFF", "ABCD", 4, hx, hy, hz, { bright = true, momz = 1 })
        else
            local startIdx = 1
            if dmg < 9 then startIdx = 3 elseif dmg <= 12 then startIdx = 2 end
            W.spawnFx("BLUD", "CBA", 8, hx, hy, hz, { momz = 2, startIdx = startIdx })
        end
        W.damageMobj(best, dmg, src, src)
    elseif wd < range then
        local pd = wd - 4; if pd < 1 then pd = 1 end       -- pull the puff off the wall
        local melee = range <= 65
        W.spawnFx("PUFF", "ABCD", 4, x1 + dx * pd, y1 + dy * pd,
            shootZ + slope * pd + (W.pRandom() - W.pRandom()) * (4 / 255),
            { bright = not melee, momz = 1, startIdx = melee and 3 or 1 })
    end
    return best, bestAlong
end

-- P_AimLineAttack: autoaim slope toward the nearest shootable thing under the
-- crosshair inside the +-100/160 vertical window; wall occlusion via the sloped
-- sight walk. Returns (slope, target); slope 0 when nothing is aimed at.
function W.aimLineAttack(src, x1, y1, shootZ, ang, range)
    local dx, dy = cos(ang), sin(ang)
    local bestAlong, slope, tgt = range, 0, nil
    for _, th in ipairs(W.map.things) do
        if th ~= src and th.think == "monster" and not th.dead and not th.removed
            and (th.flags & 0x0010) == 0 then
            local e = W.THING_SPR[th.dtype]
            if e and e.r then
                local rx, ry = th.x - x1, th.y - y1
                local along = rx * dx + ry * dy
                if along > 0 and along < bestAlong then
                    local perp = abs(rx * (-dy) + ry * dx)
                    if perp <= e.r then
                        local mi = th.info or W.MINFO[e.spr]
                        local oz, oh = th.z or 0, (mi and mi.h) or 56
                        local ts = (oz + oh - shootZ) / along
                        local bs = (oz - shootZ) / along
                        if ts > 100 / 160 then ts = 100 / 160 end
                        if bs < -100 / 160 then bs = -100 / 160 end
                        if ts > bs and W.checkSight(x1, y1, shootZ, th.x, th.y, oz, oz + oh) then
                            bestAlong = along; slope = (ts + bs) / 2; tgt = th
                        end
                    end
                end
            end
        end
    end
    if src ~= "player" and not W.playerDead then
        local rx, ry = W.viewX - x1, W.viewY - y1
        local along = rx * dx + ry * dy
        if along > 0 and along < bestAlong then
            local perp = abs(rx * (-dy) + ry * dx)
            if perp <= W.RADIUS then
                local ts = (W.pz + W.PHEIGHT - shootZ) / along
                local bs = (W.pz - shootZ) / along
                if ts > 100 / 160 then ts = 100 / 160 end
                if bs < -100 / 160 then bs = -100 / 160 end
                if ts > bs and W.checkSight(x1, y1, shootZ, W.viewX, W.viewY, W.pz, W.pz + W.PHEIGHT) then
                    slope = (ts + bs) / 2; tgt = "player"
                end
            end
        end
    end
    return slope, tgt
end

-- Player hitscan origin: vanilla shootz = feet + height/2 + 8.
function W.pShootZ() return W.pz + 36 end

-- P_BulletSlope: aim dead ahead at 1024, then retry ~5.6 degrees right/left.
function W.bulletSlope()
    local sz = W.pShootZ()
    local s, t = W.aimLineAttack("player", W.viewX, W.viewY, sz, W.viewAngle, 1024)
    if not t then
        s, t = W.aimLineAttack("player", W.viewX, W.viewY, sz, W.viewAngle + pi / 32, 1024)
        if not t then
            s, t = W.aimLineAttack("player", W.viewX, W.viewY, sz, W.viewAngle - pi / 32, 1024)
            if not t then s = 0 end
        end
    end
    W.bslope = s; W.linetarget = t
    return s, t
end

-- P_GunShot: one bullet at MISSILERANGE with the shared bullet slope.
function W.gunShot(accurate)
    local dmg = 5 * (W.pRandom() % 3 + 1)
    local ang = W.viewAngle
    if not accurate then ang = ang + (W.pRandom() - W.pRandom()) * (pi / 8192) end
    W.lineAttack("player", W.viewX, W.viewY, W.pShootZ(), ang, 2048, W.bslope or 0, dmg)
end

-- P_SpawnPlayerMissile: straight ahead from feet+32 with the 3-try autoaim.
function W.spawnPlayerMissile(kind)
    local slope, t = W.bulletSlope()
    if not t then slope = 0 end
    W.spawnProjectile(kind, W.viewX, W.viewY, W.pz + 32, W.viewAngle,
        slope * W.PROJ[kind].speed, "player")
end

-- P_DamageMobj: target is "player" or a thing. inflictor = what physically hit
-- (missile/attacker, thrust origin; nil for slime/crushers = no thrust), source
-- = who to blame (infighting retaliation + kill credit). Player gets armor
-- absorb, pain sound, damage flash and the same knockback thrust as monsters.
function W.damageMobj(target, dmg, inflictor, source)
    if target == "player" then
        if W.playerDead then return end
        if (W.powers.invuln or 0) ~= 0 and dmg < 1000 then return end
        if W.skill == 1 then dmg = floor(dmg / 2) end        -- sk_baby: half damage
        local absorb = 0
        if W.armor > 0 and W.armorType > 0 then
            absorb = min(W.armor, floor(dmg * ((W.armorType == 1) and (1 / 3) or (1 / 2))))
            W.armor = W.armor - absorb
            if W.armor <= 0 then W.armorType = 0 end
        end
        local d = dmg - absorb
        W.health = W.health - d
        W.damageCount = min(100, (W.damageCount or 0) + d)
        W.attacker = source
        pcall(W.playSfx, "DSPLPAIN")
        local inf = (type(inflictor) == "table") and inflictor
            or ((type(source) == "table") and source or nil)
        if inf then                                          -- knockback (rocket jumps!)
            local ang = atan(W.viewY - inf.y, W.viewX - inf.x)
            local thrust = dmg * 12.5 / 100
            W.momx = W.momx + cos(ang) * thrust
            W.momy = W.momy + sin(ang) * thrust
        end
        if W.health <= 0 then
            W.health = 0; W.playerDead = true; W.deadTimer = now()
            W.dropWeapon()
            pcall(W.playSfx, "DSPLDETH")
        end
        return
    end
    local th = target
    if type(th) ~= "table" or th.dead or th.removed then return end
    local mi = th.info
    local inf = (inflictor == "player" or source == "player") and "player"
        or ((type(inflictor) == "table") and inflictor
            or ((type(source) == "table") and source or nil))
    if inf then                                              -- damage thrust, mass-scaled
        local ix, iy
        if inf == "player" then ix, iy = W.viewX, W.viewY else ix, iy = inf.x, inf.y end
        local ang = atan(th.y - iy, th.x - ix)
        local thrust = dmg * 12.5 / ((mi and mi.mass) or 100)
        th.momx = (th.momx or 0) + cos(ang) * thrust
        th.momy = (th.momy or 0) + sin(ang) * thrust
    end
    th.hp = (th.hp or 0) - dmg
    if th.hp <= 0 then W.killMobj(th, source); return end
    if mi and W.pRandom() < (mi.pain or 0) then
        th.justhit = true                                    -- retaliate on the next chase
        W.setMState(th, "pain", 1)
    end
    th.reaction = 0                                          -- awake now
    if source and source ~= target and (th.threshold or 0) <= 0 then
        th.target = source                                   -- infighting: blame the shooter
        th.threshold = 100                                   -- BASETHRESHOLD
        if th.stkey == "stnd" and th.states and th.states.run then
            W.setMState(th, "run", 1)
        end
    end
end

-- P_KillMobj: gib below -spawnhealth, credit the kill, blame stored on the
-- corpse (a barrel's target is its killer, so A_Explode credits the chain).
function W.killMobj(th, source)
    th.dead = true
    th.target = source
    local mi = th.info
    if mi and mi.countkill then W.killCount = (W.killCount or 0) + 1 end
    if th.states then
        if th.states.xdie and mi and th.hp < -mi.hp then W.setMState(th, "xdie", 1)
        else W.setMState(th, "die", 1) end
    else
        th.think = nil                                       -- statue species: freeze
    end
end

function W.hurtPlayer(dmg) W.damageMobj("player", dmg, nil, nil) end

-- P_RadiusAttack: falloff = radius - (max(|dx|,|dy|) - target radius), LOS-gated
-- from the blast spot. spot (the exploding thing) is exempt; the SHOOTER is NOT
-- (self rockets hurt). source only sets blame for infighting/credit.
function W.radiusDamage(x, y, dmg, rad, spot, source)
    local function reach(tx, ty, tz)
        local ddx, ddy = tx - x, ty - y; local dd = sqrt(ddx * ddx + ddy * ddy)
        if dd <= 1 then return true end
        return W.rayWallDist(x, y, ddx / dd, ddy / dd, dd, tz) >= dd - 1
    end
    for _, th in ipairs(W.map.things) do
        if th ~= spot and th.think == "monster" and not th.dead and not th.removed then
            local e = W.THING_SPR[th.dtype]
            if e and e.r then
                local dist = max(abs(th.x - x), abs(th.y - y)) - e.r
                if dist < 0 then dist = 0 end
                if dist < rad and reach(th.x, th.y, (th.z or 0) + 28) then
                    W.damageMobj(th, rad - dist, spot, source)
                end
            end
        end
    end
    local pdist = max(abs(W.viewX - x), abs(W.viewY - y)) - W.RADIUS
    if pdist < 0 then pdist = 0 end
    if pdist < rad and reach(W.viewX, W.viewY, W.pz + 28) then
        W.damageMobj("player", rad - pdist, spot, source)
    end
end

-- Best owned weapon that has ammo (P_CheckAmmo preference order, with the
-- shareware plasma/BFG and commercial SSG gates), for auto-switch on empty.
function W.bestWeapon()
    local ammo, owned = W.ammo, W.weaponOwned
    if owned[6] and ammo.cel > 0 and W.gameMode ~= "shareware" then return 6 end
    if owned[9] and ammo.shl > 2 and W.gameMode == "commercial" then return 9 end
    if owned[4] and ammo.bul > 0 then return 4 end
    if owned[3] and ammo.shl > 0 then return 3 end
    if ammo.bul > 0 then return 2 end
    if owned[8] then return 8 end
    if owned[5] and ammo.rck > 0 then return 5 end
    if owned[7] and ammo.cel > 40 and W.gameMode ~= "shareware" then return 7 end
    return 1
end

----------------------------------------------------------------------
-- Player weapon psprites (p_pspr.c). Two layers: W.psp (the gun) and W.psf
-- (the muzzle flash), each a named state in W.WSTATES with a tic countdown.
-- Actions run on state entry; a 0-tic state falls through (chaingun refire).
----------------------------------------------------------------------
function W.setPsprite(layer, stname)
    while true do
        if not stname then layer.st = nil; layer.tics = -1; return end
        local s = W.WSTATES[stname]
        if not s then layer.st = nil; layer.tics = -1; return end
        layer.st = stname
        layer.tics = s.t
        if s.a then
            local fn = W.PACT[s.a]
            if fn then fn(layer, s) end
            if layer.st ~= stname then return end   -- action redirected the layer
        end
        if layer.tics ~= 0 then return end
        stname = s.nx
    end
end

-- P_CheckAmmo: enough for one shot? Else pick the fallback and start lowering.
function W.checkAmmo()
    local w = W.WEAPONS[W.curWeapon]
    if not w.ammo or W.ammo[w.ammo] >= (w.cost or 1) then return true end
    W.pendingWeapon = W.bestWeapon()
    W.setPsprite(W.psp, w.down)
    return false
end

-- P_FireWeapon: enter the attack chain and alert every monster in earshot.
function W.fireWeapon()
    if not W.checkAmmo() then return end
    W.setPsprite(W.psp, W.WEAPONS[W.curWeapon].atk)
    W.noiseAlert()
end

-- P_BringUpWeapon: swap to the pending weapon and raise it from the bottom.
function W.bringUpWeapon()
    local wnum = W.pendingWeapon or W.curWeapon
    W.curWeapon = wnum; W.pendingWeapon = nil
    if wnum == 8 then pcall(W.playSfx, "DSSAWUP") end
    W.psp.sy = 128
    W.setPsprite(W.psp, W.WEAPONS[wnum].up)
end

function W.dropWeapon()
    W.setPsprite(W.psp, W.WEAPONS[W.curWeapon].down)
end

-- Weapon action routines. layer = the psprite the state belongs to.
W.PACT = {}
W.PACT.ready = function(layer)
    if W.curWeapon == 8 and layer.st == "SAW" then pcall(W.playSfx, "DSSAWIDL") end
    if W.pendingWeapon or W.playerDead or W.health <= 0 then
        W.setPsprite(layer, W.WEAPONS[W.curWeapon].down)
        return
    end
    if W.fireHeld then
        -- rocket launcher + BFG do not autofire on a held button
        if not W.attackdown or (W.curWeapon ~= 5 and W.curWeapon ~= 7) then
            W.attackdown = true
            W.fireWeapon()
            return
        end
    else
        W.attackdown = false
    end
    local a = (W.levelTime % 64) * (TWO_PI / 64)          -- weapon bob (A_WeaponReady)
    layer.sx = 1 + W.bob * cos(a)
    local a2 = (W.levelTime % 32) * (TWO_PI / 64)
    layer.sy = 32 + W.bob * sin(a2)
end
W.PACT.lower = function(layer)
    layer.sy = layer.sy + 6                                -- LOWERSPEED
    if layer.sy < 128 then return end
    if W.playerDead or W.health <= 0 then
        layer.sy = 128
        W.setPsprite(layer, nil)                           -- dead: keep it down
        return
    end
    W.bringUpWeapon()
end
W.PACT.raise = function(layer)
    layer.sy = layer.sy - 6                                -- RAISESPEED
    if layer.sy > 32 then return end
    layer.sy = 32                                          -- WEAPONTOP
    W.setPsprite(layer, W.WEAPONS[W.curWeapon].ready)
end
W.PACT.refire = function(layer)
    if W.fireHeld and not W.pendingWeapon and not W.playerDead then
        W.refire = (W.refire or 0) + 1
        W.fireWeapon()
    else
        W.refire = 0
        W.checkAmmo()
    end
end
W.PACT.checkreload = function() W.checkAmmo() end
W.PACT.gunflash = function()
    W.setPsprite(W.psf, W.WEAPONS[W.curWeapon].flash)
end
W.PACT.light0 = function() W.extralight = 0 end
W.PACT.light1 = function() W.extralight = 16 end
W.PACT.light2 = function() W.extralight = 32 end
W.PACT.punch = function()
    local dmg = (W.pRandom() % 10 + 1) * 2
    if (W.powers.berserk or 0) ~= 0 then dmg = dmg * 10 end
    local ang = W.viewAngle + (W.pRandom() - W.pRandom()) * (pi / 8192)
    local slope, tgt = W.aimLineAttack("player", W.viewX, W.viewY, W.pShootZ(), ang, 64)
    local hit = W.lineAttack("player", W.viewX, W.viewY, W.pShootZ(), ang, 64, tgt and slope or 0, dmg)
    W.shootSpecialLine(W.viewX, W.viewY, W.viewAngle, 64)
    if hit then
        pcall(W.playSfx, "DSPUNCH")
        local tx, ty = W.tgtPos(hit)
        W.viewAngle = atan(ty - W.viewY, tx - W.viewX)     -- face the victim
    end
end
W.PACT.saw = function()
    local dmg = (W.pRandom() % 10 + 1) * 2
    local ang = W.viewAngle + (W.pRandom() - W.pRandom()) * (pi / 8192)
    -- meleerange+1 so the puff does not skip on the flat
    local slope, tgt = W.aimLineAttack("player", W.viewX, W.viewY, W.pShootZ(), ang, 65)
    local hit = W.lineAttack("player", W.viewX, W.viewY, W.pShootZ(), ang, 65, tgt and slope or 0, dmg)
    W.shootSpecialLine(W.viewX, W.viewY, W.viewAngle, 65)
    if not hit then pcall(W.playSfx, "DSSAWFUL"); return end
    pcall(W.playSfx, "DSSAWHIT")
    local tx, ty = W.tgtPos(hit)
    W.viewAngle = atan(ty - W.viewY, tx - W.viewX)
end
W.PACT.firepistol = function()
    pcall(W.playSfx, "DSPISTOL")
    W.ammo.bul = W.ammo.bul - 1
    W.setPsprite(W.psf, W.WEAPONS[2].flash)
    W.bulletSlope()
    W.gunShot(W.refire == 0)
    W.shootSpecialLine(W.viewX, W.viewY, W.viewAngle, 2048)
end
W.PACT.fireshotgun = function()
    pcall(W.playSfx, "DSSHOTGN")
    W.ammo.shl = W.ammo.shl - 1
    W.setPsprite(W.psf, W.WEAPONS[3].flash)
    W.bulletSlope()
    for _ = 1, 7 do W.gunShot(false) end
    W.shootSpecialLine(W.viewX, W.viewY, W.viewAngle, 2048)
end
W.PACT.fireshotgun2 = function()
    pcall(W.playSfx, "DSDSHTGN")
    W.ammo.shl = W.ammo.shl - 2
    W.setPsprite(W.psf, W.WEAPONS[9].flash)
    W.bulletSlope()
    for _ = 1, 20 do
        local dmg = 5 * (W.pRandom() % 3 + 1)
        local ang = W.viewAngle + (W.pRandom() - W.pRandom()) * (pi / 4096)
        W.lineAttack("player", W.viewX, W.viewY, W.pShootZ(), ang, 2048,
            (W.bslope or 0) + (W.pRandom() - W.pRandom()) * (32 / 65536), dmg)
    end
    W.shootSpecialLine(W.viewX, W.viewY, W.viewAngle, 2048)
end
W.PACT.opensg2 = function() pcall(W.playSfx, "DSDBOPN") end
W.PACT.loadsg2 = function() pcall(W.playSfx, "DSDBLOAD") end
W.PACT.closesg2 = function(layer)
    pcall(W.playSfx, "DSDBCLS")
    W.PACT.refire(layer)
end
W.PACT.firecgun = function(layer)
    pcall(W.playSfx, "DSPISTOL")
    if W.ammo.bul <= 0 then return end
    W.ammo.bul = W.ammo.bul - 1
    local w = W.WEAPONS[4]
    W.setPsprite(W.psf, (layer.st == "CHAIN1") and w.flash or w.flash2)
    W.bulletSlope()
    W.gunShot(W.refire == 0)
    W.shootSpecialLine(W.viewX, W.viewY, W.viewAngle, 2048)
end
W.PACT.firemissile = function()
    W.ammo.rck = W.ammo.rck - 1
    W.spawnPlayerMissile("ROCKET")
end
W.PACT.fireplasma = function()
    W.ammo.cel = W.ammo.cel - 1
    local w = W.WEAPONS[6]
    W.setPsprite(W.psf, ((W.pRandom() & 1) == 0) and w.flash or w.flash2)
    W.spawnPlayerMissile("PLASMA")
end
W.PACT.firebfg = function()
    W.ammo.cel = W.ammo.cel - 40
    W.spawnPlayerMissile("BFG")
end
W.PACT.bfgsound = function() pcall(W.playSfx, "DSBFG") end

-- P_MovePsprites: one tic of both layers.
function W.movePsprites()
    local p = W.psp
    if p.st and p.tics ~= -1 then
        p.tics = p.tics - 1
        if p.tics <= 0 then W.setPsprite(p, W.WSTATES[p.st].nx) end
    end
    local f = W.psf
    if f.st and f.tics ~= -1 then
        f.tics = f.tics - 1
        if f.tics <= 0 then W.setPsprite(f, W.WSTATES[f.st].nx) end
    end
end

-- Draw the view weapon + flash psprites with the vanilla R_DrawPSprite
-- transform: 320x168-view coordinates (BASEYCENTER 100), sprite offsets from
-- the WAD, scaled by viewH/168 and anchored to the view center/horizon. The
-- flash layer rides the gun's bob and draws fullbright.
function W.drawWeapon(sw, viewH)
    local S2 = viewH / 168
    local secl = W.sectorAt(W.viewX, W.viewY)
    local lgt = clamp(0.22 + 0.78 * (((secl and secl.light or 160) + (W.extralight or 0)) / 255), 0.10, 1.0)
    local baseTint = W.greyTint(lgt)
    local bobx, boby = W.psp.sx or 1, W.psp.sy or 32
    local function layer(ps)
        if not ps.st then return end
        local st = W.WSTATES[ps.st]; if not st then return end
        local lump = W.spriteFrameLump(st.spr, st.f, 1); if not lump then return end
        local meta = W.spriteTex(lump); if not (meta and meta.tex) then return end
        local x0 = W.centerX + (bobx - 160 - meta.xoff) * S2
        local y0 = W.horizon + (boby - meta.yoff - 100.5) * S2
        local uw, vh = 0.5 / meta.w, 0.5 / meta.h
        ImGui.AddImage(meta.tex, x0, y0, x0 + meta.w * S2, y0 + meta.h * S2,
            uw, vh, 1 - uw, 1 - vh, st.b and 0xFFFFFFFF or baseTint)
    end
    layer(W.psp)
    layer(W.psf)
end

----------------------------------------------------------------------
-- SECTION J: input, per-frame update, state machine
-- States: W.gameState in { "nowad","frontend","loading","play","error" } ("menu"
-- is a superseded safety-net render branch). Front-end sub-screens live in W.menu.screen.
-- (Separate from Phase-1 W.state, which stays the WAD container status.)
----------------------------------------------------------------------
W.VK = {
    W = 0x57, A = 0x41, S = 0x53, DK = 0x44, Q = 0x51, E = 0x45,
    LEFT = 0x25, UP = 0x26, RIGHT = 0x27, DOWN = 0x28,
    SPACE = 0x20, CTRL = 0x11, SHIFT = 0x10, ENTER = 0x0D, ESCAPE = 0x1B,
    M = 0x4D, BACKSPACE = 0x08, Y = 0x59, N = 0x4E,
    ONE = 0x31, TWO = 0x32, THREE = 0x33, FOUR = 0x34, FIVE = 0x35, SIX = 0x36, SEVEN = 0x37,
}
-- keys polled for rising-edge detection every frame (menu nav keys included)
W.trackVK = { W.VK.ENTER, W.VK.M, W.VK.BACKSPACE, W.VK.SPACE, W.VK.E,
    W.VK.ONE, W.VK.TWO, W.VK.THREE, W.VK.FOUR, W.VK.FIVE, W.VK.SIX, W.VK.SEVEN,
    W.VK.UP, W.VK.DOWN, W.VK.LEFT, W.VK.RIGHT, W.VK.ESCAPE, W.VK.Y, W.VK.N }

----------------------------------------------------------------------
-- Player think (p_user.c), all on the 35 Hz tic clock.
----------------------------------------------------------------------
-- P_Thrust: momentum impulse along angle. move is in vanilla cmd units
-- (forwardmove 25/50, sidemove 24/40); impulse = move*2048/65536 = move/32.
function W.thrust(angle, move)
    W.momx = W.momx + (move / 32) * cos(angle)
    W.momy = W.momy + (move / 32) * sin(angle)
end

-- P_MovePlayer: sample the held movement keys as this tic's command; thrust
-- applies only on the ground (no air control, momentum carries).
function W.movePlayerCmd()
    local run = kdown(W.VK.SHIFT)
    local fm = 0
    if kdown(W.VK.W) or kdown(W.VK.UP) then fm = fm + 1 end
    if kdown(W.VK.S) or kdown(W.VK.DOWN) then fm = fm - 1 end
    local sm = 0
    if kdown(W.VK.A) then sm = sm - 1 end
    if kdown(W.VK.DK) then sm = sm + 1 end
    W.cmdForward = fm * (run and 50 or 25)
    W.cmdSide = sm * (run and 40 or 24)
    W.onground = W.pz <= W.floorZAt(W.viewX, W.viewY) + 0.01
    if W.cmdForward ~= 0 and W.onground then W.thrust(W.viewAngle, W.cmdForward) end
    if W.cmdSide ~= 0 and W.onground then W.thrust(W.viewAngle - pi / 2, W.cmdSide) end
end

-- P_XYMovement: clamp to MAXMOVE (30/tic), substep halves above MAXMOVE/2,
-- blocked moves slide along the wall; ground friction 0.90625 with the
-- STOPSPEED no-input stop. Walk tops out ~8.3 u/tic, run ~15.6 (vanilla).
function W.playerXYMovement()
    if W.momx ~= 0 or W.momy ~= 0 then
        if W.momx > 30 then W.momx = 30 elseif W.momx < -30 then W.momx = -30 end
        if W.momy > 30 then W.momy = 30 elseif W.momy < -30 then W.momy = -30 end
        local xm, ym = W.momx, W.momy
        repeat
            local px, py
            if xm > 15 or ym > 15 or xm < -15 or ym < -15 then
                px = W.viewX + xm / 2; py = W.viewY + ym / 2
                xm = xm / 2; ym = ym / 2
            else
                px = W.viewX + xm; py = W.viewY + ym
                xm, ym = 0, 0
            end
            if not W.pTryMove(px, py) then
                W.slideMove()
                break
            end
        until xm == 0 and ym == 0
    end
    if not W.onground then return end                 -- no friction airborne
    if W.momx > -0.0625 and W.momx < 0.0625 and W.momy > -0.0625 and W.momy < 0.0625
        and (W.cmdForward or 0) == 0 and (W.cmdSide or 0) == 0 then
        W.momx = 0; W.momy = 0
    else
        W.momx = W.momx * 0.90625                     -- FRICTION 0xE800
        W.momy = W.momy * 0.90625
    end
end

-- P_ZMovement: smooth step-up eases the view down, gravity doubles on the
-- first airborne tic, hard landings (momz < -8) squat the view and grunt.
function W.playerZMovement()
    local floorz = W.floorZAt(W.viewX, W.viewY)
    if W.pz < floorz then                             -- stepped up: ease the view
        W.viewheight = W.viewheight - (floorz - W.pz)
        W.dvh = (41 - W.viewheight) / 8
    end
    W.pz = W.pz + W.momz
    if W.pz <= floorz then
        if W.momz < 0 then
            if W.momz < -8 then
                W.dvh = W.momz / 8                    -- squat on hard landing
                pcall(W.playSfx, "DSOOF")
            end
            W.momz = 0
        end
        W.pz = floorz
    else
        if W.momz == 0 then W.momz = -2 else W.momz = W.momz - 1 end
    end
    local sec = W.sectorAt(W.viewX, W.viewY)
    if sec and W.pz + W.PHEIGHT > sec.ceil then       -- ceiling clip
        W.pz = sec.ceil - W.PHEIGHT
        if W.momz > 0 then W.momz = 0 end
    end
end

-- P_CalcHeight: momentum bob (cap MAXBOB 16) on a 20-tic sine, viewheight
-- easing back to 41 after squats/step-ups; airborne uses raw viewheight.
function W.calcHeight()
    W.bob = (W.momx * W.momx + W.momy * W.momy) / 4
    if W.bob > 16 then W.bob = 16 end
    local sec = W.sectorAt(W.viewX, W.viewY)
    if not W.onground then
        W.viewZ = W.pz + W.viewheight
        if sec and W.viewZ > sec.ceil - 4 then W.viewZ = sec.ceil - 4 end
        return
    end
    local bobz = (W.bob / 2) * sin((W.levelTime % 20) * (TWO_PI / 20))
    if not W.playerDead and W.dvh ~= 0 then
        W.viewheight = W.viewheight + W.dvh
        if W.viewheight > 41 then W.viewheight = 41; W.dvh = 0 end
        if W.viewheight < 20.5 then
            W.viewheight = 20.5
            if W.dvh <= 0 then W.dvh = 0.03 end
        end
        if W.dvh ~= 0 then W.dvh = W.dvh + 0.25 end
    end
    W.viewZ = W.pz + W.viewheight + bobz
    if sec and W.viewZ > sec.ceil - 4 then W.viewZ = sec.ceil - 4 end
end

-- Power countdown; a power at 0 is gone (berserk/allmap are level-long).
function W.tickPowers()
    for pw, t in pairs(W.powers) do
        if t > 0 then
            W.powers[pw] = t - 1
            if W.powers[pw] <= 0 then W.powers[pw] = nil end
        end
    end
end

-- P_DeathThink: sink the view, coast the corpse, turn to face the killer
-- (damage flash fades once facing), USE restarts the level.
function W.deathThink()
    W.movePsprites()
    W.cmdForward = 0; W.cmdSide = 0
    if W.viewheight > 6 then W.viewheight = W.viewheight - 1 end
    if W.viewheight < 6 then W.viewheight = 6 end
    W.onground = W.pz <= W.floorZAt(W.viewX, W.viewY) + 0.01
    W.playerXYMovement()
    W.playerZMovement()
    W.viewZ = W.pz + W.viewheight
    local att = W.attacker
    if att and type(att) == "table" then
        local ang = atan(att.y - W.viewY, att.x - W.viewX)
        local delta = angNorm(ang - W.viewAngle)
        local step = pi / 36                              -- ANG5 per tic
        if abs(delta) < step then
            W.viewAngle = ang
            if (W.damageCount or 0) > 0 then W.damageCount = W.damageCount - 1 end
        elseif delta > 0 then W.viewAngle = W.viewAngle + step
        else W.viewAngle = W.viewAngle - step end
    elseif (W.damageCount or 0) > 0 then
        W.damageCount = W.damageCount - 1
    end
    if W.usePressed then
        W.usePressed = false
        if now() - (W.deadTimer or 0) > 1.0 then
            W.newGame(); W.startMap(W.map and W.map.name)
        end
    end
end

-- P_PlayerThink: one player tic (movement, z, view, use, psprites, powers).
function W.playerThink()
    if W.playerDead then W.deathThink(); return end
    if (W.reactionTics or 0) > 0 then
        W.reactionTics = W.reactionTics - 1               -- post-teleport freeze
        W.cmdForward = 0; W.cmdSide = 0
    else
        W.movePlayerCmd()
    end
    W.playerXYMovement()
    W.playerZMovement()
    W.calcHeight()
    W.unstick()                              -- safety net, inert in normal play
    if W.usePressed then
        W.usePressed = false
        local l = W.useLine()
        if l then W.useSpecialLine(l) end
    end
    W.movePsprites()
    W.tickPowers()
    if (W.damageCount or 0) > 0 then W.damageCount = W.damageCount - 1 end
    if (W.bonusCount or 0) > 0 then W.bonusCount = W.bonusCount - 1 end
end

function W.update(dt, menuOpen)
    W.updateWipe(dt)                             -- advance the screen melt (over any state)
    -- World is frozen (no input, no move) while the menu is open or a wipe plays.
    if W.gameState == "play" and not menuOpen and not W.wipe.active then
        -- fire input: held state; the psprite ready/refire actions consume it.
        -- Check LCTRL/RCTRL specifically (LMB via ImGui). NOTE: the generic
        -- VK_CONTROL (0x11) is deliberately NOT polled - it is held/latched by
        -- all sorts of other software and was the reason LCTRL/RCTRL were added.
        -- A real Ctrl press still registers as 0xA2/0xA3, so nothing is lost.
        local md = false; local mok, mr = pcall(ImGui.IsMouseDown, 0); if mok then md = mr end
        local rawFire = kdown(0xA2) or kdown(0xA3) or md
        -- Arming guard: a fire source that reads "held" from the very first frame
        -- (a stuck/latched key or a garbage ImGui mouse state on some builds) must
        -- NOT autofire the pistol at spawn. Require the input to be observed
        -- RELEASED at least once before it can fire; a real tap arms it instantly.
        if not rawFire then W.fireArmed = true end
        W.fireHeld = rawFire and (W.fireArmed == true)

        if not W.playerDead then
            -- per-frame turning for latency; vanilla rates (6-tic slow ramp, run doubles)
            local turn = 0
            if kdown(W.VK.LEFT) then turn = turn + 1 end
            if kdown(W.VK.RIGHT) then turn = turn - 1 end
            if turn ~= 0 then
                W.turnHeld = (W.turnHeld or 0) + dt
                local rate
                if W.turnHeld < 6 * W.TIC then rate = W.TURNSLOW
                elseif kdown(W.VK.SHIFT) then rate = W.TURNFAST
                else rate = W.TURNNORM end
                W.viewAngle = W.viewAngle + turn * rate * dt
            else
                W.turnHeld = 0
            end
            if W.mouseLook then
                -- GTA's raw mouse-look input (INPUT_LOOK_LR): no cursor warp, reads 0
                -- unfocused. Read the DISABLED control (all controls are suppressed).
                local ok, look = pcall(Natives.InvokeFloat, 0x11E65974A982637C, 0, 1)
                if ok and look then W.viewAngle = W.viewAngle - look * W.LOOKSENS end
            end
            W.viewAngle = angNorm(W.viewAngle)
        end

        -- edges consumed by the next tic
        if kpressed(W.VK.SPACE) or kpressed(W.VK.E) then W.usePressed = true end
        if kpressed(W.VK.ONE) then W.selectSlot(1) end
        if kpressed(W.VK.TWO) then W.selectSlot(2) end
        if kpressed(W.VK.THREE) then W.selectSlot(3) end
        if kpressed(W.VK.FOUR) then W.selectSlot(4) end
        if kpressed(W.VK.FIVE) then W.selectSlot(5) end
        if kpressed(W.VK.SIX) then W.selectSlot(6) end
        if kpressed(W.VK.SEVEN) then W.selectSlot(7) end
        W.useHint = W.useLine()              -- HUD prompt scan

        W.runTics(dt)                        -- 35 Hz: player, actors, psprites, specials

        if kpressed(W.VK.M) then W.mouseLook = not W.mouseLook; pcall(W.saveSettings) end
        if kpressed(W.VK.BACKSPACE) or kpressed(W.VK.ESCAPE) then    -- pause -> front-end main
            W.menu.fromPlay = true; W.menu.screen = "main"; W.menu.cursor = 1
            W.gameState = "frontend"; pcall(W.playSfx, "DSSWTCHN")
        end
    elseif W.gameState == "intermission" and not menuOpen then
        -- edge-detected (never held-repeat), and no generic VK_CONTROL, so a
        -- stuck fire source cannot auto-skip the intermission. W.firePrevWi is
        -- seeded true on entry to swallow the held shot that flipped the exit.
        local md = false; local mok, mr = pcall(ImGui.IsMouseDown, 0); if mok then md = mr end
        local fire = kdown(0xA2) or kdown(0xA3) or md
        if (fire and not W.firePrevWi) or kpressed(W.VK.SPACE) or kpressed(W.VK.E)
            or kpressed(W.VK.ENTER) then
            W.wiAccel = true
        end
        W.firePrevWi = fire
        W.runTics(dt)
    elseif W.gameState == "frontend" and not menuOpen then
        if not W.menu.fromPlay then                  -- fresh menu: attract level behind the buttons
            if W.menu.screen ~= "title" and not W.attractOn then W.startAttract() end
            if W.attractOn then W.updateAttractCam(dt) end
        end
        W.updateFrontend(dt)
    elseif not menuOpen and not BLAD_MODE
        and (W.gameState == "nowad" or W.gameState == "error" or W.gameState == "menu") then
        -- These screens have no DOOM menu to quit from; ESC/Backspace closes
        -- the overlay (the Play Doom button reopens it).
        if kpressed(W.VK.ESCAPE) or kpressed(W.VK.BACKSPACE) then
            W.playOn = false; W.active = false
        end
    end
end

-- Optional: stop WASD from also driving the GTA player while walking.
function W.suppressGameInput()
    if W.nativesOk == false then return end
    local ok = pcall(function()
        Natives.InvokeVoid(0x5F4B6931816E599B, 0) -- DISABLE_ALL_CONTROL_ACTIONS(PLAYER)
        Natives.InvokeVoid(0x5F4B6931816E599B, 1) -- DISABLE_ALL_CONTROL_ACTIONS(FRONTEND)
    end)
    if not ok then W.nativesOk = false end
end

-- Which IWAD flavour is loaded? Gates SSG/plasma/BFG auto-select + WI layout.
function W.detectGameMode()
    local hasMapxx, hasE2 = false, false
    for _, m in ipairs(W.mapList or {}) do
        if m:match("^MAP%d%d$") then hasMapxx = true end
        if m:match("^E[2-9]M%d$") then hasE2 = true end
    end
    if hasMapxx then W.gameMode = "commercial"
    elseif hasE2 then W.gameMode = "registered"
    else W.gameMode = "shareware" end
end

-- Load a map and drop the player at its start.
function W.startMap(name)
    if not W.gameMode then W.detectGameMode() end
    W.gameState = "loading"
    W.pendingMap = name
    local m = W.loadMap(name)
    if not m then W.gameState = "error"; return end
    if W.spawnPlayer(m) then W.gameState = "play" end
    -- Defer music start to the present thread (onPresent services W.musPending):
    -- MCI open/stop must share one thread or a present-thread stop cannot reach a
    -- device opened on the menu thread. startMap can run from the menu (map picker).
    if W.gameState == "play" and W.map then W.musPending = W.map.name end
end

----------------------------------------------------------------------
-- SECTION K: HUD + frame render
----------------------------------------------------------------------
-- Vanilla status bar (st_stuff.c): STBAR background, STTNUM big numbers with
-- STTPRCNT, STARMS + STYSNUM/STGNUM arms grid, STKEYS pips, the STYSNUM ammo
-- table and the STF* face widget, all at their 320x200 coordinates scaled by
-- sh/200 and centered (black wings on widescreen).
W.ST_FACES = nil
function W.stInit()
    W.st = { faceIndex = 0, faceCount = 0, priority = 0, oldHealth = -1,
        gotWeapon = false, lastAttackDown = -1, rnd = 0 }
    if not W.ST_FACES then
        local f = {}
        for p = 0, 4 do
            local base = p * 8
            f[base + 0] = "STFST" .. p .. "0"; f[base + 1] = "STFST" .. p .. "1"
            f[base + 2] = "STFST" .. p .. "2"
            f[base + 3] = "STFTR" .. p .. "0"; f[base + 4] = "STFTL" .. p .. "0"
            f[base + 5] = "STFOUCH" .. p; f[base + 6] = "STFEVL" .. p
            f[base + 7] = "STFKILL" .. p
        end
        f[40] = "STFGOD0"; f[41] = "STFDEAD0"
        W.ST_FACES = f
    end
end

-- ST_calcPainOffset: 5 health tiers of 8 faces each.
function W.stPainOffset()
    local h = W.health or 0
    if h > 100 then h = 100 end
    return floor((100 - h) * 5 / 101) * 8
end

-- ST_updateFaceWidget, one tic. Priorities: dead(9) > evil grin(8) > hit(7) >
-- own hurt(6) > rampage(5) > god(4) > look-about(0). The vanilla OUCH check
-- (health INCREASED by 20+, a famous inversion) is kept as-is.
function W.stTicker()
    local st = W.st; if not st then return end
    st.rnd = W.pRandom()
    if st.priority < 10 and (W.health or 0) <= 0 then
        st.priority = 9; st.faceIndex = 41; st.faceCount = 1
    end
    if st.priority < 9 and (W.bonusCount or 0) > 0 and st.gotWeapon then
        st.gotWeapon = false
        st.priority = 8; st.faceCount = 2 * 35
        st.faceIndex = W.stPainOffset() + 6                -- evil grin
    end
    if st.priority < 8 and (W.damageCount or 0) > 0
        and W.attacker and type(W.attacker) == "table" then
        st.priority = 7
        if (W.health or 0) - st.oldHealth > 20 then
            st.faceCount = 35; st.faceIndex = W.stPainOffset() + 5   -- ouch
        else
            local bad = atan(W.attacker.y - W.viewY, W.attacker.x - W.viewX)
            local diff = angNorm(bad - W.viewAngle)
            st.faceCount = 35
            if abs(diff) < pi / 4 then
                st.faceIndex = W.stPainOffset() + 7        -- head-on: rampage face
            elseif diff < 0 then
                st.faceIndex = W.stPainOffset() + 3        -- attacker right: turn right
            else
                st.faceIndex = W.stPainOffset() + 4        -- attacker left: turn left
            end
        end
    end
    if st.priority < 7 and (W.damageCount or 0) > 0 then
        if (W.health or 0) - st.oldHealth > 20 then
            st.priority = 7; st.faceCount = 35
            st.faceIndex = W.stPainOffset() + 5            -- ouch
        else
            st.priority = 6; st.faceCount = 35
            st.faceIndex = W.stPainOffset() + 7            -- pain grimace
        end
    end
    if st.priority < 6 then
        if W.attackdown then
            if st.lastAttackDown == -1 then st.lastAttackDown = 2 * 35
            else
                st.lastAttackDown = st.lastAttackDown - 1
                if st.lastAttackDown == 0 then
                    st.priority = 5; st.faceCount = 1; st.lastAttackDown = 1
                    st.faceIndex = W.stPainOffset() + 7    -- rampage
                end
            end
        else
            st.lastAttackDown = -1
        end
    end
    if st.priority < 5 and (W.powers.invuln or 0) ~= 0 then
        st.priority = 4; st.faceIndex = 40; st.faceCount = 1
    end
    if st.faceCount <= 0 then                              -- look about
        st.faceIndex = W.stPainOffset() + st.rnd % 3
        st.faceCount = 17                                  -- ST_STRAIGHTFACECOUNT
        st.priority = 0
    end
    st.faceCount = st.faceCount - 1
    st.oldHealth = W.health or 0
end

-- One status-bar patch at 320x200 coords (patch offsets honoured).
function W.stPatchXY(name, x, y, S, xb, top)
    local wpx, hpx, lo, to = W.patchSize(name)
    local handle = W.menuTex(name)
    if not (handle and wpx) then return false end
    local px = xb + (x - (lo or 0)) * S
    local py = top + (y - 168 - (to or 0)) * S
    ImGui.AddImage(handle, px, py, px + wpx * S, py + hpx * S, 0, 0, 1, 1, 0xFFFFFFFF)
    return true
end

-- Right-justified number: digits drawn leftward ending at x (STlib_drawNum).
function W.stNumR(prefix, x, y, n, S, xb, top)
    n = floor(n or 0); if n < 0 then n = 0 end
    local s = tostring(n)
    local xx = x
    for i = #s, 1, -1 do
        local nm = prefix .. s:sub(i, i)
        local dw = W.patchSize(nm) or 4
        xx = xx - dw
        W.stPatchXY(nm, xx, y, S, xb, top)
    end
end

function W.drawStatusBar(sw, sh)
    local S = sh / 200
    local barW = 320 * S
    local xb = (sw - barW) * 0.5
    local top = sh - 32 * S
    rectf(0, top, sw, sh, 0, 0, 0, 255)                    -- widescreen wings
    if not W.stPatchXY("STBAR", 0, 168, S, xb, top) then   -- background
        rectf(xb, top, xb + barW, sh, 24, 22, 28, 255)     -- fallback while baking
    end
    W.stPatchXY("STARMS", 104, 168, S, xb, top)
    -- big ammo counter (blank for fist/saw)
    local ak = W.WEAPONS[W.curWeapon or 2] and W.WEAPONS[W.curWeapon or 2].ammo
    if ak then W.stNumR("STTNUM", 44, 171, W.ammo[ak], S, xb, top) end
    -- health / armor percents (the % sign sits AT the coordinate)
    W.stPatchXY("STTPRCNT", 90, 171, S, xb, top)
    W.stNumR("STTNUM", 90, 171, W.health, S, xb, top)
    W.stPatchXY("STTPRCNT", 221, 171, S, xb, top)
    W.stNumR("STTNUM", 221, 171, W.armor, S, xb, top)
    -- arms grid: yellow owned, grey not
    for i = 2, 7 do
        local gx = 111 + ((i - 2) % 3) * 12
        local gy = 172 + floor((i - 2) / 3) * 10
        W.stPatchXY((W.weaponOwned[i] and "STYSNUM" or "STGNUM") .. i, gx, gy, S, xb, top)
    end
    -- face
    local fname = W.ST_FACES and W.ST_FACES[W.st and W.st.faceIndex or 0]
    if fname then W.stPatchXY(fname, 143, 168, S, xb, top) end
    -- keys (cards 0-2, skulls 3-5)
    local slot = 0
    for _, col in ipairs({ "blue", "yellow", "red" }) do
        if W.keys and W.keys[col] then
            local idx = slot + ((W.keyForm[col] == "skull") and 3 or 0)
            W.stPatchXY("STKEYS" .. idx, 239, 171 + slot * 10, S, xb, top)
        end
        slot = slot + 1
    end
    -- ammo table: current + max per type
    local rows = { { "bul", 173 }, { "shl", 179 }, { "rck", 185 }, { "cel", 191 } }
    for _, r in ipairs(rows) do
        W.stNumR("STYSNUM", 288, r[2], W.ammo[r[1]], S, xb, top)
        W.stNumR("STYSNUM", 314, r[2], W.maxammo[r[1]], S, xb, top)
    end
end

function W.drawHUD(sw, sh)
    W.drawStatusBar(sw, sh)
    -- palette flashes over the 3D view (red damage tiers, gold bonus, radsuit
    -- green, invulnerability wash), from the vanilla (count+7)>>3 tiering
    local dc = W.damageCount or 0
    local bc = W.bonusCount or 0
    if dc > 0 then
        local tier = min(floor((dc + 7) / 8), 8)
        rectf(0, 0, sw, W.viewH, 255, 2, 3, floor(tier * 28))
    elseif bc > 0 then
        local tier = min(floor((bc + 7) / 8), 4)
        rectf(0, 0, sw, W.viewH, 215, 186, 69, floor(tier * 25))
    elseif (W.powers.radsuit or 0) > 4 * 32
        or ((W.powers.radsuit or 0) > 0 and ((W.powers.radsuit or 0) & 8) ~= 0) then
        rectf(0, 0, sw, W.viewH, 0, 256 / 3, 0, 32)
    end
    if (W.powers.invuln or 0) > 4 * 32
        or ((W.powers.invuln or 0) > 0 and ((W.powers.invuln or 0) & 8) ~= 0) then
        rectf(0, 0, sw, W.viewH, 220, 220, 255, 26)        -- INVERSECOLORMAP stand-in
    end
    -- "use" prompt when facing a door / switch (not vanilla, kept for usability)
    local hint = W.useHint
    if hint then
        local sp = hint.special
        local label = (sp == 11 or sp == 51) and "SPACE: EXIT"
            or W.DOOR_SPECIALS[sp] and "SPACE: OPEN" or "SPACE: USE"
        ImGui.AddText(W.centerX - 34, W.horizon + 16, label, 245, 230, 140, 255)
    end
    -- pickup / locked-door message, vanilla top-left in the hu_font (ImGui text
    -- only while the glyphs bake or if the WAD lacks the STCFN lumps)
    local m = (W.hudMsgUntil and now() < W.hudMsgUntil) and W.hudMsg or nil
    if m then
        local mS = sh / 200
        local fw = W.fontLineWidth(m, mS)
        if fw then W.drawFontLine(m, floor(2 * mS), floor(2 * mS), mS, 255)
        else ImGui.AddText(4, 2, m, 245, 235, 150, 255) end
    end
    if W.playerDead then
        ImGui.AddText(floor(W.centerX - 78), floor(W.viewH * 0.46), "press USE to restart", 210, 190, 120, 255)
    end
end

----------------------------------------------------------------------
-- SECTION W: intermission screen (wi_stuff.c)
--
-- After a level exits: "<name> FINISHED" with KILLS/ITEMS/SECRET percentages
-- counting up (+2/tic, pistol tick every 4th, shotgun blast on each finished
-- row), TIME vs PAR, then (Doom 1) the episode map with splats on completed
-- levels and the blinking you-are-here arrow, then the next level loads.
-- Graphics are the WAD's own WI* patches through the shared menuTex pipeline.
----------------------------------------------------------------------
-- Episode map node coordinates (wi_stuff.c lnodes, 320x200 space).
W.WI_LNODES = {
    [1] = { {185,164},{148,143},{69,122},{209,102},{116,89},{166,55},{71,56},{135,29},{71,24} },
    [2] = { {254,25},{97,50},{188,64},{128,78},{214,92},{133,130},{208,136},{148,140},{235,158} },
    [3] = { {156,168},{48,154},{174,95},{265,75},{130,48},{279,23},{198,48},{140,25},{281,136} },
}
-- E1 background animation spots (10 looping 3-frame WIA000xx anims, 11 tics).
W.WI_ANIMS1 = { {224,104},{184,160},{112,136},{72,112},{88,96},{64,48},{192,40},{136,16},{80,16},{64,24} }

function W.wiStart(wm)
    W.wi = {
        wm = wm, state = "stats", bcnt = 0,
        cntKills = -1, cntItems = -1, cntSecret = -1, cntTime = -1, cntPar = -1,
        spState = 1, cntPause = 35, showCnt = 0, noCnt = 0,
    }
    W.wiAccel = false
    W.firePrevWi = true            -- swallow the held fire that flipped the exit switch
    W.gameState = "intermission"
    if W.musicOn then W.musPending = (W.gameMode == "commercial") and "D_DM2INT" or "D_INTER" end
end

-- WI_Ticker (35 Hz). One press jumps the counters to their totals, the next
-- advances to the map page / next level.
function W.wiTicker()
    local wi = W.wi; if not wi then return end
    local wm = wi.wm
    wi.bcnt = wi.bcnt + 1
    local accel = W.wiAccel; W.wiAccel = false
    if wi.state == "stats" then
        local kMax = floor(wm.kills * 100 / wm.maxkills)
        local iMax = floor(wm.items * 100 / wm.maxitems)
        local sMax = floor(wm.secrets * 100 / wm.maxsecret)
        if accel and wi.spState ~= 10 then
            wi.cntKills = kMax; wi.cntItems = iMax; wi.cntSecret = sMax
            wi.cntTime = wm.time; wi.cntPar = wm.par or 0
            pcall(W.playSfx, "DSBAREXP")
            wi.spState = 10
            accel = false
        end
        local s = wi.spState
        if s == 2 then
            wi.cntKills = ((wi.cntKills < 0) and 0 or wi.cntKills) + 2
            if (wi.bcnt & 3) == 0 then pcall(W.playSfx, "DSPISTOL") end
            if wi.cntKills >= kMax then
                wi.cntKills = kMax; pcall(W.playSfx, "DSBAREXP"); wi.spState = 3
            end
        elseif s == 4 then
            wi.cntItems = ((wi.cntItems < 0) and 0 or wi.cntItems) + 2
            if (wi.bcnt & 3) == 0 then pcall(W.playSfx, "DSPISTOL") end
            if wi.cntItems >= iMax then
                wi.cntItems = iMax; pcall(W.playSfx, "DSBAREXP"); wi.spState = 5
            end
        elseif s == 6 then
            wi.cntSecret = ((wi.cntSecret < 0) and 0 or wi.cntSecret) + 2
            if (wi.bcnt & 3) == 0 then pcall(W.playSfx, "DSPISTOL") end
            if wi.cntSecret >= sMax then
                wi.cntSecret = sMax; pcall(W.playSfx, "DSBAREXP"); wi.spState = 7
            end
        elseif s == 8 then
            if (wi.bcnt & 3) == 0 then pcall(W.playSfx, "DSPISTOL") end
            wi.cntTime = ((wi.cntTime < 0) and 0 or wi.cntTime) + 3
            if wi.cntTime >= wm.time then wi.cntTime = wm.time end
            wi.cntPar = ((wi.cntPar < 0) and 0 or wi.cntPar) + 3
            if wi.cntPar >= (wm.par or 0) then
                wi.cntPar = wm.par or 0
                if wi.cntTime >= wm.time then
                    pcall(W.playSfx, "DSBAREXP"); wi.spState = 9
                end
            end
        elseif s == 10 then
            if accel then
                pcall(W.playSfx, "DSSGCOCK")
                if wm.epsd and W.gameMode ~= "commercial" then
                    wi.state = "next"; wi.showCnt = 4 * 35     -- SHOWNEXTLOCDELAY
                else
                    wi.state = "nostate"; wi.noCnt = 10
                end
            end
        elseif (s % 2) == 1 then
            wi.cntPause = wi.cntPause - 1
            if wi.cntPause <= 0 then wi.spState = s + 1; wi.cntPause = 35 end
        end
    elseif wi.state == "next" then
        wi.showCnt = wi.showCnt - 1
        if wi.showCnt <= 0 or accel then wi.state = "nostate"; wi.noCnt = 10 end
    elseif wi.state == "nostate" then
        wi.noCnt = wi.noCnt - 1
        if wi.noCnt <= 0 then
            W.wi = nil
            W.worldDone(wm)
        end
    end
end

-- One WI patch at 320x200 coords with its own offsets applied.
function W.wiPatch(name, x, y, S, xb)
    local wpx, hpx, lo, to = W.patchSize(name)
    local handle = W.menuTex(name)
    if not (handle and wpx) then return false, 0, 0 end
    local px = xb + (x - (lo or 0)) * S
    local py = (y - (to or 0)) * S
    ImGui.AddImage(handle, px, py, px + wpx * S, py + hpx * S, 0, 0, 1, 1, 0xFFFFFFFF)
    return true, wpx, hpx
end

-- Right-justified WINUM number ending at x; minDigits pads with zeros.
function W.wiNumR(x, y, n, S, xb, minDigits)
    if n == nil or n < 0 then return x end
    n = floor(n)
    local s = tostring(n)
    while #s < (minDigits or 1) do s = "0" .. s end
    local xx = x
    for i = #s, 1, -1 do
        local nm = "WINUM" .. s:sub(i, i)
        local dw = W.patchSize(nm) or 11
        xx = xx - dw
        W.wiPatch(nm, xx, y, S, xb)
    end
    return xx
end

-- Percent: digits end at x, the % sign sits at x (WI_drawPercent).
function W.wiPercent(x, y, p, S, xb)
    if p == nil or p < 0 then return end
    W.wiPatch("WIPCNT", x, y, S, xb)
    W.wiNumR(x, y, p, S, xb)
end

-- Time as M:SS ending at x; an hour or more draws the SUCKS patch instead.
function W.wiTime(x, y, t, S, xb)
    if t == nil or t < 0 then return end
    if t >= 3600 then
        local wpx = W.patchSize("WISUCKS")
        if wpx then W.wiPatch("WISUCKS", x - wpx, y, S, xb) end
        return
    end
    local xx = W.wiNumR(x, y, t % 60, S, xb, 2)
    local cw = W.patchSize("WICOLON")
    if cw then xx = xx - cw; W.wiPatch("WICOLON", xx, y, S, xb) end
    if t >= 60 then W.wiNumR(xx, y, floor(t / 60), S, xb) end
end

-- Level-name patch (WILVxy / CWILVxx), centered. Returns its height.
function W.wiLevelName(idx, y, S, xb)
    if idx == nil then return 0 end
    local wm = W.wi and W.wi.wm
    local name
    if wm and wm.epsd and W.gameMode ~= "commercial" then
        name = "WILV" .. (wm.epsd - 1) .. idx
    else
        name = ("CWILV%02d"):format(idx)
    end
    local wpx, hpx = W.patchSize(name)
    if not wpx then
        W.bigText((W.gameMode == "commercial") and ("MAP" .. (idx + 1)) or ("LEVEL " .. (idx + 1)),
            xb + 160 * S, y * S + 8, 2.0, 235, 60, 50, 255)
        return 12
    end
    W.wiPatch(name, (320 - wpx) / 2, y, S, xb)
    return hpx
end

function W.wiDrawBackground(sw, sh, S, xb)
    rectf(0, 0, sw, sh, 0, 0, 0, 255)
    local wm = W.wi and W.wi.wm
    local bg
    if W.gameMode == "commercial" or not (wm and wm.epsd) then bg = "INTERPIC"
    else bg = "WIMAP" .. min(wm.epsd - 1, 2) end
    local handle = W.menuTex(bg)
    if handle then
        ImGui.AddImage(handle, xb, 0, xb + 320 * S, 200 * S, 0, 0, 1, 1, 0xFFFFFFFF)
    end
    -- E1 animated background overlays
    if wm and wm.epsd == 1 and W.gameMode ~= "commercial" then
        local bcnt = W.wi.bcnt
        for i, loc in ipairs(W.WI_ANIMS1) do
            local frame = floor(bcnt / 11 + i * 2) % 3
            W.wiPatch(("WIA0%02d%02d"):format(i - 1, frame), loc[1], loc[2], S, xb)
        end
    end
end

function W.wiDrawOnNode(idx, patch, S, xb)
    local wm = W.wi and W.wi.wm
    local ep = wm and wm.epsd
    local nodes = ep and W.WI_LNODES[ep]
    local n = nodes and nodes[idx + 1]
    if not n then return end
    W.wiPatch(patch, n[1], n[2], S, xb)
end

function W.wiDraw(sw, sh)
    local wi = W.wi; if not wi then return end
    local wm = wi.wm
    local S = sh / 200
    local xb = (sw - 320 * S) * 0.5
    W.bakeUsed = 0
    W.wiDrawBackground(sw, sh, S, xb)
    if wi.state == "stats" then
        -- "<level> FINISHED"
        local h = W.wiLevelName(wm.lastIdx, 2, S, xb)
        local fw, fh = W.patchSize("WIF")
        if fw then W.wiPatch("WIF", (320 - fw) / 2, 2 + (5 * h) / 4, S, xb) end
        -- stat rows
        local nh = select(2, W.patchSize("WINUM0")) or 12
        local lh = floor((3 * nh) / 2)
        W.wiPatch("WIOSTK", 50, 50, S, xb)
        W.wiPercent(320 - 50, 50, wi.cntKills, S, xb)
        W.wiPatch("WIOSTI", 50, 50 + lh, S, xb)
        W.wiPercent(320 - 50, 50 + lh, wi.cntItems, S, xb)
        W.wiPatch("WISCRT2", 50, 50 + 2 * lh, S, xb)
        W.wiPercent(320 - 50, 50 + 2 * lh, wi.cntSecret, S, xb)
        -- time / par
        W.wiPatch("WITIME", 16, 168, S, xb)
        W.wiTime(160 - 16, 168, wi.cntTime, S, xb)
        if wm.par then
            W.wiPatch("WIPAR", 160 + 16, 168, S, xb)
            W.wiTime(320 - 16, 168, wi.cntPar, S, xb)
        end
    elseif wi.state == "next" or wi.state == "nostate" then
        if wm.epsd and W.gameMode ~= "commercial" and W.WI_LNODES[wm.epsd] then
            for i = 0, wm.lastIdx or 0 do W.wiDrawOnNode(i, "WISPLAT", S, xb) end
            if W.didsecret then W.wiDrawOnNode(8, "WISPLAT", S, xb) end
            if wm.nextIdx and (wi.bcnt & 31) < 20 then
                W.wiDrawOnNode(wm.nextIdx, "WIURH0", S, xb)
            end
        end
        if wm.next then
            local ew, eh = W.patchSize("WIENTER")
            if ew then W.wiPatch("WIENTER", (320 - ew) / 2, 2, S, xb) end
            W.wiLevelName(wm.nextIdx, 2 + (5 * (eh or 16)) / 4, S, xb)
        end
    end
end

----------------------------------------------------------------------
-- SECTION M: audio (MUS -> MIDI music, DMX -> WAV sound effects)
--
-- DOOM music lumps are stored in id's MUS format (a compact event stream).
-- They are converted, once, to a Standard MIDI File on disk and played through
-- the OS media control interface (MCI) "sequencer" device. MciSendString only
-- reports success/failure (not the device's play position), and the sequencer
-- has no built-in loop, so looping is driven off the wall clock (ImGui.GetTime)
-- against the track's computed duration. Every MCI call is routed through W.mci
-- (pcall + boolean), so a missing or unavailable sequencer degrades to silence,
-- never a crash. Sound effects are DMX (DSxxx) PCM lumps converted to WAV and
-- played with Utils.PlaySound. All binary is written via io.open("wb").
--
-- Endianness: the MIDI container is BIG-endian (">"); MUS headers and WAV/RIFF
-- are LITTLE-endian ("<").
----------------------------------------------------------------------

-- Pick the music lump for a map. Returns (ordinal, name) or nil (stay silent).
function W.musicLumpFor(mapName)
    mapName = trimName(mapName)
    local cand
    if mapName:match("^D_") then
        cand = mapName                       -- direct lump (D_INTER between levels)
    elseif mapName == "VICTORY" then
        cand = "D_VICTOR"
    elseif mapName:match("^E%dM%d$") then
        cand = "D_" .. mapName
    elseif mapName:match("^MAP%d%d$") then
        cand = W.MUS_DOOM2[mapName]
    end
    if cand and W.lumpIndex and W.lumpIndex[cand] then
        local ord = W.lumpIndex[cand][1]
        if ord and #W.lumpBytes(ord) > 0 then return ord, cand end
    end
    -- Fallbacks: the intro track, then the first non-empty D_ lump in the wad.
    if W.lumpIndex and W.lumpIndex.D_INTRO then
        local ord = W.lumpIndex.D_INTRO[1]
        if ord and #W.lumpBytes(ord) > 0 then return ord, "D_INTRO" end
    end
    if W.lumps then
        for i, L in ipairs(W.lumps) do
            if L.name:match("^D_") and L.size and L.size > 0 then
                return i, L.name
            end
        end
    end
    return nil
end

-- Core MUS -> MIDI conversion. May return nil on any structural problem; the
-- public W.mus2midi wraps this in pcall so a truncated/garbage lump is silent.
-- volScale (0..1) multiplies note-on velocities so the music-volume slider can
-- attenuate the whole track at conversion time (MCI's sequencer has no live
-- volume command, so volume is baked into the cached .mid per level).
function W._mus2midi(mus, volScale)
    volScale = volScale or 1
    if type(mus) ~= "string" or #mus < 4 then return nil end
    -- Passthrough: a lump that is already a Standard MIDI File is returned as-is
    -- (0 = unknown exact length -> caller disables auto-loop for it).
    if mus:sub(1, 4) == "MThd" then return mus, 0 end
    if #mus < 16 or mus:sub(1, 4) ~= "MUS\26" then return nil end
    local scoreLen   = string.unpack("<I2", mus, 5)
    local scoreStart = string.unpack("<I2", mus, 7)
    local instrCnt   = string.unpack("<I2", mus, 13)
    if scoreStart < 16 + instrCnt * 2 then return nil end
    if scoreStart >= #mus then return nil end

    -- DIVISION=140, TEMPO=1000000us/qtr => 140*1e6/1e6 = 140 MIDI ticks/sec, so
    -- one MUS tick maps 1:1 to one MIDI tick and deltas need no scaling.
    local DIVISION, TEMPO = 140, 1000000

    local pos = scoreStart + 1
    local scoreEnd = scoreStart + scoreLen
    if scoreLen == 0 or scoreEnd > #mus then scoreEnd = #mus end
    if scoreEnd > #mus then scoreEnd = #mus end

    -- MUS channel -> MIDI channel; MUS 15 (percussion) -> MIDI 9, 9..14 -> 10..15.
    local function midiChan(m)
        if m == 15 then return 9
        elseif m < 9 then return m
        else return m + 1 end
    end

    -- MIDI variable-length quantity (7 bits/byte, high bit = "more follow").
    local function writeVLQ(v)
        v = v & 0x0FFFFFFF
        local out = { v & 0x7F }
        v = v >> 7
        while v > 0 do table.insert(out, 1, (v & 0x7F) | 0x80); v = v >> 7 end
        for i = 1, #out do out[i] = string.char(out[i]) end
        return table.concat(out)
    end

    local trk = {}
    local queuedTicks = 0
    local totalTicks = 0
    local vol = {}
    for c = 0, 15 do vol[c] = 127 end

    -- Prefix the pending inter-event delay to each emitted MIDI event, then reset.
    local function emit(bytes)
        trk[#trk + 1] = writeVLQ(queuedTicks) .. bytes
        queuedTicks = 0
    end

    -- MUS delay is a big-endian 7-bit VLQ (high bit = "more follow").
    local function readDelay()
        local d = 0
        repeat
            local b = mus:byte(pos); pos = pos + 1
            if not b then return d, true end
            d = d * 128 + (b & 0x7F)
        until (b & 0x80) == 0
        return d, false
    end

    while pos <= scoreEnd do
        local ev = mus:byte(pos); pos = pos + 1
        if not ev then break end
        local last  = (ev & 0x80) ~= 0
        local etype = (ev >> 4) & 0x07
        local mch   = ev & 0x0F
        local ch    = midiChan(mch)
        local stop  = false

        if etype == 0 then                    -- release note (1 byte)
            local nb = mus:byte(pos); pos = pos + 1
            if not nb then break end
            emit(string.char(0x80 | ch, nb & 0x7F, 0))
        elseif etype == 1 then                -- play note (1 or 2 bytes)
            local nb = mus:byte(pos); pos = pos + 1
            if not nb then break end
            local n = nb & 0x7F
            if (nb & 0x80) ~= 0 then
                local vb = mus:byte(pos); pos = pos + 1
                if not vb then break end
                vol[mch] = vb & 0x7F
            end
            local vel = vol[mch]
            if volScale < 1 then
                vel = floor(vel * volScale)
                if vel < 1 and vol[mch] > 0 and volScale > 0 then vel = 1 end   -- keep the note audible
            end
            emit(string.char(0x90 | ch, n, vel))
        elseif etype == 2 then                -- pitch bend (1 byte)
            local b = mus:byte(pos); pos = pos + 1
            if not b then break end
            local wheel = b * 64              -- 0..16320, b=128 -> center 8192
            emit(string.char(0xE0 | ch, wheel & 0x7F, (wheel >> 7) & 0x7F))
        elseif etype == 3 then                -- system event (1 byte, ctrl 10..14)
            local sc = mus:byte(pos); pos = pos + 1
            if not sc then break end
            local cc = ({ [10] = 120, [11] = 123, [12] = 126, [13] = 127, [14] = 121 })[sc]
            if cc then emit(string.char(0xB0 | ch, cc, 0)) end
        elseif etype == 4 then                -- change controller (2 bytes)
            local cnum = mus:byte(pos); pos = pos + 1
            if not cnum then break end
            local cvb = mus:byte(pos); pos = pos + 1
            if not cvb then break end
            local cval = cvb & 0x7F
            if cnum == 0 then
                emit(string.char(0xC0 | ch, cval))    -- instrument -> program change
            else
                local cc = ({ [1] = 0, [2] = 1, [3] = 7, [4] = 10, [5] = 11,
                    [6] = 91, [7] = 93, [8] = 64, [9] = 67 })[cnum]
                if cc then emit(string.char(0xB0 | ch, cc, cval)) end
            end
        elseif etype == 6 then                -- score end (0 bytes)
            stop = true
        else                                  -- 5 or 7 = unused/malformed
            return nil
        end

        if stop then break end

        if last then
            local d, eof = readDelay()
            queuedTicks = queuedTicks + d
            totalTicks  = totalTicks + d
            if eof then break end
        end
    end

    -- Track data: tempo meta at delta 0, all converted events, end-of-track meta.
    local trackData = "\0\255\81\3" .. string.pack(">I4", TEMPO):sub(2)
        .. table.concat(trk)
        .. writeVLQ(0) .. "\255\47\0"
    local midi = "MThd" .. string.pack(">I4I2I2I2", 6, 0, 1, DIVISION)
        .. "MTrk" .. string.pack(">I4", #trackData) .. trackData
    return midi, totalTicks / DIVISION
end

-- Public MUS -> MIDI. Returns (midiBytes, totalSeconds) or nil. Never throws.
function W.mus2midi(mus, volScale)
    local ok, midi, secs = pcall(W._mus2midi, mus, volScale)
    if not ok then return nil end
    return midi, secs
end

-- Send one MCI command. Returns false (never throws) if MCI is unavailable or
-- the command failed; only an explicit false result counts as failure.
function W.mci(cmd)
    if not (Utils and Utils.MciSendString) then return false end
    local ok, res = pcall(Utils.MciSendString, cmd)
    if not ok then return false end
    return res ~= false
end

-- Settings persistence: a tiny key=value text file in Lua/DoomWad, loaded once
-- at boot and rewritten on every options change (so mouselook/music/volumes
-- stick between sessions with no manual save, like the host's saveable toggles).
-- Best-effort; a missing/garbage file just leaves the init defaults in place.
function W.settingsFile()
    if W.settingsPath ~= nil then return W.settingsPath end
    W.settingsPath = false
    local rok, root = pcall(FileMgr.GetMenuRootPath)
    if rok and root and root ~= "" then
        root = tostring(root)
        pcall(FileMgr.CreateDir, root .. "/Lua/DoomWad")
        W.settingsPath = root .. "/Lua/DoomWad/settings.cfg"
    end
    return W.settingsPath
end

function W.loadSettings()
    if W.settingsLoaded then return end
    W.settingsLoaded = true
    local path = W.settingsFile(); if not path then return end
    local ook, f = pcall(io.open, path, "r"); if not ook or not f then return end
    local rok, data = pcall(f.read, f, "*a"); pcall(f.close, f)
    if not rok or type(data) ~= "string" then return end
    for k, v in data:gmatch("([%w_]+)%s*=%s*([^\r\n]+)") do
        v = v:gsub("%s+$", "")
        if k == "mouselook" then W.mouseLook = (v == "1" or v == "true")
        elseif k == "music" then W.musicOn = not (v == "0" or v == "false")
        elseif k == "looksens" then W.LOOKSENS = clamp(tonumber(v) or W.LOOKSENS, 0.02, 0.5)
        elseif k == "musicvol" then W.musicVol = clamp(floor(tonumber(v) or 15), 0, 15)
        elseif k == "sfxvol" then W.sfxVol = clamp(floor(tonumber(v) or 15), 0, 15) end
    end
end

-- Write current settings. Called on every options change (cheap, ~5 short lines).
function W.saveSettings()
    local path = W.settingsFile(); if not path then return end
    local body = table.concat({
        "mouselook=" .. (W.mouseLook and "1" or "0"),
        "music=" .. (W.musicOn and "1" or "0"),
        ("looksens=%.3f"):format(W.LOOKSENS or 0.1),
        "musicvol=" .. tostring(W.musicVol or 15),
        "sfxvol=" .. tostring(W.sfxVol or 15),
    }, "\n") .. "\n"
    local ook, f = pcall(io.open, path, "w"); if not ook or not f then return end
    pcall(f.write, f, body); pcall(f.close, f)
end

-- Ensure the on-disk cache directory exists (textures, music and sfx share it).
-- The directory is PER-WAD: cache/<size>-<crc> from W.wadFingerprint, because
-- every cached file is named after its lump and different wads reuse the same
-- lump names; a shared directory would serve the previous wad's baked assets
-- after a wad switch. Returns true if a cache path is available.
function W.ensureCacheDir()
    if W.cacheDir then return true end
    local rok, root = pcall(FileMgr.GetMenuRootPath)
    if rok and root and root ~= "" then
        root = tostring(root)
        local dir = root .. "/Lua/DoomWad/cache/" .. (W.wadFp or "shared")
        pcall(FileMgr.CreateDir, root .. "/Lua/DoomWad")
        pcall(FileMgr.CreateDir, root .. "/Lua/DoomWad/cache")
        pcall(FileMgr.CreateDir, dir)
        W.cacheDir = dir
    end
    return W.cacheDir ~= nil
end

-- Convert (if needed), cache, and start the music for a map. No-op if music is
-- off or nothing suitable is found. Any prior track is closed first.
function W.playMusic(mapName)
    W.musReq = mapName                        -- remembered so a volume change can restart it
    if not W.musicOn then return end
    W.stopMusic()
    if not W.ensureCacheDir() then return end
    local ord, name = W.musicLumpFor(mapName)
    if not ord then return end
    -- Volume is baked into the .mid, so cache per (track, volume): a level plays
    -- silently at vol 0, at full velocity at vol 15. The file name carries the vol.
    local vol = clamp(floor(W.musicVol or 15), 0, 15)
    local volScale = vol / 15
    local key = name .. "_v" .. vol
    local path = W.cacheDir .. "/mus_" .. key:gsub("[^%w_%-]", "_") .. ".mid"
    local exists = false
    if FileMgr and FileMgr.DoesFileExist then
        local dok, de = pcall(FileMgr.DoesFileExist, path)
        if dok and de then exists = true end
    end
    -- Convert + cache once per (track, volume). If the .mid is already on disk and
    -- we know its duration, skip the (re)conversion entirely.
    W.musLenByName = W.musLenByName or {}
    local secs = W.musLenByName[key]
    if not (exists and secs) then
        local bytes = W.lumpBytes(ord)
        if #bytes < 4 then return end
        local head = bytes:sub(1, 4)
        local midi
        if head == "MThd" then
            midi, secs = bytes, 0             -- already a MIDI (custom PWAD; not scaled)
        elseif head == "MUS\26" then
            midi, secs = W.mus2midi(bytes, volScale)
        else
            return                            -- unknown music format -> silence
        end
        if not midi then return end
        if not exists then
            if not W.writeBytes(path, midi) then return end   -- io.open "wb"
        end
        W.musLenByName[key] = secs
    end
    local mp = path:gsub("/", "\\")           -- MCI prefers backslash paths
    W.musAlias = W.musAlias or "doommus"
    W.mci('close ' .. W.musAlias)             -- clear any stale alias
    if not W.mci('open "' .. mp .. '" type sequencer alias ' .. W.musAlias) then return end
    -- Unload protection, three layers (periodic keep-alive MCI commands are NOT
    -- an option: each play command costs a lagspike and degrades playback, per
    -- in-game testing): (1) PRIMARY - on unload, the teardown present frames
    -- deliver the stop via serviceStop (see the ON_UNLOAD handler); (2) a host
    -- script, when present, stops the music from its own present-thread tick
    -- the moment our liveness feature leaves the registry; (3) last resort -
    -- the play below is BOUNDED to the track length, never unbounded, so even a
    -- fully orphaned sequencer runs out at the end of the current track. The
    -- bound rides on the same play command the track start and each loop
    -- already issue, costing zero extra MCI traffic.
    W.musBoundMs = nil
    if secs and secs > 0.5 and W.mci('set ' .. W.musAlias .. ' time format milliseconds') then
        -- The bound must stay INSIDE the media: 'play to' past the sequence
        -- length fails with MCIERR_OUTOFRANGE (verified against winmm; a +1000
        -- overshoot here was the silent-music bug). Undershoot by 500ms; the
        -- wall-clock loop reseek replays from the start anyway.
        local b = floor(secs * 1000) - 500
        if b > 1000 then W.musBoundMs = b end
    end
    local playCmd = 'play ' .. W.musAlias
    if W.musBoundMs then playCmd = playCmd .. ' to ' .. W.musBoundMs end
    local played = W.mci(playCmd)
    if not played and W.musBoundMs then
        -- Never let the bound break playback: fall back to an unbounded play
        -- (the host watchdog still stops it on unload).
        W.musBoundMs = nil
        played = W.mci('play ' .. W.musAlias)
    end
    if W.stopDiag and Logger and Logger.LogInfo then
        pcall(Logger.LogInfo, ("[DOOMWAD] playMusic(%s): lump=%s secs=%s bound=%s played=%s"):format(
            tostring(mapName), tostring(name), tostring(secs), tostring(W.musBoundMs), tostring(played)))
    end
    if not played then W.mci('close ' .. W.musAlias); return end
    W.musTrack = name
    W.musLen = secs or 0
    W.musStart = now()
    W.musPlaying = true
    W.stopRetries = 0            -- cancel any pending stop retries now that we are playing
end

-- Duration-based loop: MCI cannot report play position, so re-seek+play just
-- before the computed track length elapses. Called every frame (even paused).
function W.updateMusic()
    if not W.musPlaying then return end
    if not W.musicOn then W.requestStop("musicoff"); return end
    if W.musLen and W.musLen > 0.5 then
        if now() - W.musStart >= W.musLen - 0.15 then
            W.mci('seek ' .. W.musAlias .. ' to start')
            local playCmd = 'play ' .. W.musAlias
            if W.musBoundMs then playCmd = playCmd .. ' to ' .. W.musBoundMs end
            W.mci(playCmd)
            W.musStart = now()
        end
    end
end

-- Stop + close the current track. Safe to call at any time (degrades silently
-- when MCI is unavailable). Clears the playing state either way. Logs the raw
-- MciSendString results to cherax.log (W.stopDiag) so the stop can be diagnosed
-- in-game, since MCI behaviour cannot be verified headlessly.
function W.stopMusic(tag)
    local a = W.musAlias or "doommus"
    local ok1, r1, ok2, r2 = false, nil, false, nil
    if Utils and Utils.MciSendString then
        ok1, r1 = pcall(Utils.MciSendString, "stop " .. a)
        ok2, r2 = pcall(Utils.MciSendString, "close " .. a)
    end
    if W.stopDiag and Logger and Logger.LogInfo then
        pcall(Logger.LogInfo, ("[DOOMWAD] stopMusic(%s): stop(ok=%s r=%s) close(ok=%s r=%s)"):format(
            tostring(tag), tostring(ok1), tostring(r1), tostring(ok2), tostring(r2)))
    end
    W.musPlaying = false
    W.musTrack = nil
    W.musStart = 0
    W.musLen = 0
end

-- Request a stop with a retry window: a single MCI stop/close can be missed
-- depending on the device/thread state in-game, so W.serviceStop re-sends it for
-- a number of frames. This is why the manual "disable music" (which retries every
-- frame) worked while the old one-shot toggle-off/unload stops did not.
function W.requestStop(tag)
    W.stopRetries = 30
    W.stopMusic(tag)
end

-- Re-send stop/close for the remaining retry window. Called every frame from the
-- top of onPresent, whether or not the feature is enabled.
function W.serviceStop()
    if (W.stopRetries or 0) <= 0 then return end
    W.stopRetries = W.stopRetries - 1
    local a = W.musAlias or "doommus"
    if Utils and Utils.MciSendString then
        pcall(Utils.MciSendString, "stop " .. a)
        pcall(Utils.MciSendString, "close " .. a)
    end
end

-- Core DMX (DSxxx) -> WAV conversion. May return nil on a malformed lump.
-- volScale (0..1) attenuates the 8-bit PCM around its unsigned midpoint (128),
-- baked in per (sfx, volume) so the sound-volume slider works with Utils.PlaySound
-- (which takes no volume argument).
function W._dmx2wav(bytes, volScale)
    volScale = volScale or 1
    if type(bytes) ~= "string" or #bytes < 8 then return nil end
    local formatNum   = string.unpack("<I2", bytes, 1)
    local sampleRate  = string.unpack("<I2", bytes, 3)
    local sampleCount = string.unpack("<I4", bytes, 5)
    -- Vanilla DMX pads 16 samples of lead-in and 16 of trail; strip them when the
    -- count is large enough, else fall back to the whole payload.
    local dataOfs, dataLen
    if formatNum == 3 and sampleCount > 32 then
        dataOfs, dataLen = 8 + 16, sampleCount - 32
    else
        dataOfs, dataLen = 8, sampleCount
    end
    if dataLen < 0 then dataLen = 0 end
    if dataOfs > #bytes then return nil end
    if dataOfs + dataLen > #bytes then dataLen = #bytes - dataOfs end
    if dataLen < 0 then dataLen = 0 end
    local pcm = bytes:sub(dataOfs + 1, dataOfs + dataLen)
    if volScale < 1 and #pcm > 0 then                      -- attenuate around midpoint 128
        local out = {}
        for i = 1, #pcm do
            local v = 128 + floor((pcm:byte(i) - 128) * volScale + 0.5)
            if v < 0 then v = 0 elseif v > 255 then v = 255 end
            out[i] = string.char(v)
        end
        pcm = table.concat(out)
    end
    if sampleRate <= 0 then sampleRate = 11025 end
    -- 8-bit WAV PCM is UNSIGNED, exactly like DMX, so no sample conversion.
    local byteRate = sampleRate                            -- blockAlign(1) * rate
    local fmt = string.pack("<I2I2I4I4I2I2", 1, 1, sampleRate, byteRate, 1, 8)
    local pad = (#pcm % 2 == 1) and "\0" or ""             -- RIFF word-align
    local riff = "WAVE"
        .. "fmt " .. string.pack("<I4", 16) .. fmt
        .. "data" .. string.pack("<I4", #pcm) .. pcm .. pad
    return "RIFF" .. string.pack("<I4", #riff) .. riff
end

-- Public DMX -> WAV. Returns wavBytes or nil. Never throws.
function W.dmx2wav(bytes, volScale)
    local ok, wav = pcall(W._dmx2wav, bytes, volScale)
    if not ok then return nil end
    return wav
end

-- Convert (if needed), cache, and play a DOOM sound effect lump one-shot.
-- Cached per (sfx, volume); silent at vol 0.
function W.playSfx(name)
    local vol = clamp(floor(W.sfxVol or 15), 0, 15)
    if vol <= 0 then return end
    if not W.ensureCacheDir() then return end
    local ord = W.lumpIndex and W.lumpIndex[name] and W.lumpIndex[name][1]
    if not ord then return end
    local path = W.cacheDir .. "/sfx_" .. name:gsub("[^%w_%-]", "_") .. "_v" .. vol .. ".wav"
    local exists = false
    if FileMgr and FileMgr.DoesFileExist then
        local dok, de = pcall(FileMgr.DoesFileExist, path)
        if dok and de then exists = true end
    end
    if not exists then
        local wav = W.dmx2wav(W.lumpBytes(ord), vol / 15)
        if not wav then return end
        if not W.writeBytes(path, wav) then return end     -- io.open "wb"
    end
    if Utils and Utils.PlaySound then
        pcall(Utils.PlaySound, path:gsub("/", "\\"), false)
    end
end

----------------------------------------------------------------------
-- SECTION L: overlay window + event/tab wiring
--
-- Every primitive draws into the current window's draw list, so the whole frame
-- lives inside one fullscreen borderless input-transparent window.
----------------------------------------------------------------------
----------------------------------------------------------------------
-- SECTION N: front-end menu (title / main / skill select / options) + screen melt
-- Doom-style menu shown while gameState=="frontend". Graphics are the WAD's own
-- menu patch lumps (M_DOOM, M_SKULL1/2, M_JKILL, ...) baked to PNG + uploaded like
-- sprites, with an AddText fallback while a patch bakes or if the WAD lacks it. The
-- screen melt (f_wipe.c "Melt") slides a pre-baked TITLEPIC down in vertical strips
-- over the live game frame, revealing the new map from the top.
----------------------------------------------------------------------
W.MENU_MAIN = {
    { patch = "M_NGAME",  text = "New Game",   act = "newgame" },
    { patch = "M_OPTION", text = "Options",    act = "options" },
    { patch = "M_RDTHIS", text = "Read This!", act = "readthis" },
    { patch = "M_QUITG",  text = "Quit Game",  act = "quit" },
}
W.SKILL_ITEMS = {
    { patch = "M_JKILL", text = "I'm Too Young To Die", skill = 1 },
    { patch = "M_ROUGH", text = "Hey, Not Too Rough",   skill = 2 },
    { patch = "M_HURT",  text = "Hurt Me Plenty",       skill = 3 },
    { patch = "M_ULTRA", text = "Ultra-Violence",       skill = 4 },
    { patch = "M_NMARE", text = "Nightmare!",           skill = 5 },
}
W.OPT_ITEMS = {
    { text = "Mouse Look",       opt = "mouselook" },
    { text = "Music",            opt = "music" },
    { text = "Music Volume",     opt = "musicvol", slider = true },
    { text = "Sound Volume",     opt = "sfxvol",   slider = true },
    { text = "Look Sensitivity", opt = "looksens" },
}

-- Menu patch lump -> RGBA (clone of W.spriteRGBA but keyed by the MAIN lump index).
function W.patchRGBA(name)
    local li = W.lumpIndex and W.lumpIndex[name]
    local data = W.lumpBytes(li and li[1]); if not data or #data < 8 then return nil end
    local w, h, cols = W.patchColumns(data); if not w then return nil end
    local total = w * h; local idx, alpha = {}, {}
    for k = 0, total - 1 do alpha[k] = 0 end
    for px = 0, w - 1 do
        local posts = cols[px]
        if posts then
            for _, post in ipairs(posts) do
                local pix, tp = post.pix, post.top
                for i = 1, #pix do
                    local sy = tp + (i - 1)
                    if sy >= 0 and sy < h then local kk = sy * w + px; idx[kk] = pix:byte(i); alpha[kk] = 255 end
                end
            end
        end
    end
    local out, pal = {}, W.pal
    for k = 0, total - 1 do
        if alpha[k] == 255 then
            local c = pal[idx[k]] or { 0, 0, 0 }
            out[k + 1] = string.char(c[1], c[2], c[3], 255)
        else out[k + 1] = "\0\0\0\0" end
    end
    return table.concat(out), w, h
end

-- Async GPU upload of a menu patch (cache key "MU:"), clone of W.spriteGpu.
function W.menuTex(name)
    if not (name and W.pal and W.cacheDir) then return nil end
    local key = "MU:" .. name
    W.texCache = W.texCache or {}
    local c = W.texCache[key]
    if c == nil then
        if (W.bakeUsed or 0) >= (W.BAKE_BUDGET or 4) then return nil end
        W.bakeUsed = (W.bakeUsed or 0) + 1
        local fn = key:gsub("[^%w_%-]", function(ch) return string.format("$%02X", ch:byte()) end) .. ".png"
        local path = W.cacheDir .. "/" .. fn
        local exists = false
        local dok, de = pcall(FileMgr.DoesFileExist, path); if dok then exists = de end
        if not exists then
            local rgba, w, h = W.patchRGBA(name)
            if not rgba then W.texCache[key] = { state = "fail" }; return nil end
            local pok, png = pcall(W.encodePNG, rgba, w, h)
            if not pok or not png then W.texCache[key] = { state = "fail" }; return nil end
            if not W.writeBytes(path, png) then W.texCache[key] = { state = "fail" }; return nil end
        end
        local id
        local lok, lid = pcall(Texture.LoadTexture, path); if lok then id = lid end
        if not id then W.texCache[key] = { state = "fail" }; return nil end
        W.texCache[key] = { id = id, state = "pending" }
        return nil
    end
    if c.state == "fail" then return nil end
    if c.state == "pending" then
        local vok, valid = pcall(Texture.IsTextureValid, c.id); if not (vok and valid) then return nil end
        local tok, tex = pcall(Texture.GetTexture, c.id); if not (tok and tex) then return nil end
        c.tex = tex; c.state = "ready"
    end
    if c.state == "ready" and c.tex then
        local gok, handle = pcall(function() return c.tex:GetCurrent() end)
        if gok and handle then return handle end
    end
    return nil
end

-- Patch pixel size + offsets (cheap 4-int header read, cached), independent of
-- the GPU bake. Returns w, h, leftoffset, topoffset.
function W.patchSize(name)
    W.patchWH = W.patchWH or {}
    local m = W.patchWH[name]
    if m == nil then
        local li = W.lumpIndex and W.lumpIndex[name]
        local data = W.lumpBytes(li and li[1])
        if not data or #data < 8 then W.patchWH[name] = false; return nil end
        local w, h, lo, to = string.unpack("<i2i2i2i2", data, 1)
        if w <= 0 or h <= 0 or w > 4096 or h > 4096 then W.patchWH[name] = false; return nil end
        m = { w = w, h = h, lo = lo, to = to }; W.patchWH[name] = m
    end
    if m == false then return nil end
    return m.w, m.h, m.lo, m.to
end

-- Draw a menu patch at Doom-space (dx,dy) scaled by S with left base xbase; falls
-- back to text while a patch bakes or if the WAD lacks it.
function W.drawPatch(name, text, dx, dy, S, xbase, sel)
    local x = floor(xbase + dx * S); local y = floor(dy * S)
    local w, h = W.patchSize(name)
    local handle = W.menuTex(name)
    if handle and w then
        ImGui.AddImage(handle, x, y, x + floor(w * S), y + floor(h * S), 0, 0, 1, 1, sel and 0xFFFFFFFF or 0xFFB4B4B4)
    elseif text then
        if sel then ImGui.AddText(x, y, text, 255, 240, 150, 255) else ImGui.AddText(x, y, text, 200, 200, 205, 255) end
    end
end

function W.drawSkull(dx, dy, S, xbase)
    local name = (floor(now() / (8 / 35)) % 2 == 0) and "M_SKULL1" or "M_SKULL2"
    local x = floor(xbase + (dx - 32) * S); local y = floor((dy - 5) * S)
    local w, h = W.patchSize(name)
    local handle = W.menuTex(name)
    if handle and w then ImGui.AddImage(handle, x, y, x + floor(w * S), y + floor(h * S), 0, 0, 1, 1, 0xFFFFFFFF)
    else ImGui.AddText(x, y, ">", 255, 120, 60, 255) end
end

function W.drawMenuList(items, dx, dy0, step, S, xbase)
    for i, it in ipairs(items) do
        local dy = dy0 + (i - 1) * step
        local sel = (W.menu.cursor == i)
        W.drawPatch(it.patch, it.text, dx, dy, S, xbase, sel)
        if sel then W.drawSkull(dx, dy, S, xbase) end
    end
end

function W.drawPatchFS(name, sw, sh)
    local handle = W.menuTex(name)
    if handle then ImGui.AddImage(handle, 0, 0, floor(sw), floor(sh), 0, 0, 1, 1, 0xFFFFFFFF); return end
    ImGui.AddRectFilled(0, 0, floor(sw), floor(sh), 18, 10, 12, 255)
    local S = sh / 200
    local w, h = W.patchSize("M_DOOM"); local dh = W.menuTex("M_DOOM")
    if dh and w then local x = floor((sw - w * S) / 2); ImGui.AddImage(dh, x, floor(20 * S), x + floor(w * S), floor((20 + h) * S), 0, 0, 1, 1, 0xFFFFFFFF)
    else ImGui.AddText(floor(sw * 0.5 - 60), floor(sh * 0.32), "D O O M", 235, 60, 50, 255) end
end

-- DOOM thermometer slider (m_menu.c M_DrawThermo): M_THERML end-cap, 16 M_THERMM
-- middle cells, M_THERMR end-cap, M_THERMO knob at dot*8. Falls back to a drawn
-- bar when the WAD lacks the lumps. val/maxv sets the knob position (0..maxv).
function W.drawThermo(dx, dy, S, xbase, val, maxv)
    local segW = W.patchSize("M_THERMM") or 8
    local drewLumps = W.stPatchThermoPart("M_THERML", dx, dy, S, xbase)
    if drewLumps then
        local xx = dx + segW
        for _ = 1, maxv do W.stPatchThermoPart("M_THERMM", xx, dy, S, xbase); xx = xx + segW end
        W.stPatchThermoPart("M_THERMR", xx, dy, S, xbase)
        W.stPatchThermoPart("M_THERMO", dx + segW + val * segW, dy, S, xbase)
    else
        -- fallback bar: a dark groove with a gold filled portion
        local x0 = floor(xbase + dx * S); local y0 = floor(dy * S)
        local w = floor(maxv * 8 * S); local h = floor(8 * S)
        ImGui.AddRectFilled(x0, y0, x0 + w, y0 + h, 40, 36, 44, 255)
        ImGui.AddRectFilled(x0, y0, x0 + floor(w * val / maxv), y0 + h, 200, 170, 90, 255)
    end
end

-- draw one thermometer patch at doom-space (dx,dy); returns true if it drew a lump
function W.stPatchThermoPart(name, dx, dy, S, xbase)
    local w, h = W.patchSize(name)
    local handle = W.menuTex(name)
    if not (handle and w) then return false end
    local x = floor(xbase + dx * S); local y = floor(dy * S)
    ImGui.AddImage(handle, x, y, x + floor(w * S), y + floor(h * S), 0, 0, 1, 1, 0xFFFFFFFF)
    return true
end

function W.drawOptions(sw, sh, S, xbase)
    ImGui.AddText(floor(xbase + 100 * S), floor(18 * S), "OPTIONS", 235, 210, 120, 255)
    for i, it in ipairs(W.OPT_ITEMS) do
        local dy = 44 + (i - 1) * 18; local sel = (W.menu.cursor == i)
        local x = floor(xbase + 60 * S); local y = floor(dy * S)
        local r, g, b = 200, 200, 205; if sel then r, g, b = 255, 240, 150 end
        if it.slider then
            ImGui.AddText(x, y, it.text, r, g, b, 255)
            local v = (it.opt == "musicvol") and (W.musicVol or 15) or (W.sfxVol or 15)
            W.drawThermo(150, dy + 3, S, xbase, clamp(floor(v), 0, 15), 15)
        else
            local val
            if it.opt == "mouselook" then val = W.mouseLook and "ON" or "OFF"
            elseif it.opt == "music" then val = W.musicOn and "ON" or "OFF"
            else val = string.format("%.2f", W.LOOKSENS or 0.1) end
            ImGui.AddText(x, y, it.text .. ":  " .. val, r, g, b, 255)
        end
        if sel then W.drawSkull(60, dy, S, xbase) end
    end
    ImGui.AddText(floor(xbase + 40 * S), floor(150 * S), "Left/Right adjust, Enter toggle, Esc back", 170, 170, 180, 220)
end

function W.drawFrontend(sw, sh)
    W.bakeUsed = 0                                   -- per-frame menu bake budget (play uses setupView)
    local S = sh / 200
    local xbase = (sw - 320 * S) * 0.5
    local scr = W.menu.screen
    if scr == "title" then
        W.drawPatchFS("TITLEPIC", sw, sh)
        if floor(now() * 2) % 2 == 0 then
            W.bigText("PRESS ENTER OR SPACE", sw * 0.5, sh * 0.52, 2.5, 255, 235, 130, 255)
        end
        return
    end
    -- main/skill/options draw over the live attract render (renderBody), no opaque fill
    if scr == "main" then
        W.drawPatch("M_DOOM", "DOOM", 94, 2, S, xbase, false)
        W.drawMenuList(W.MENU_MAIN, 97, 64, 16, S, xbase)
        if W.status == "level complete" then ImGui.AddText(floor(xbase + 100 * S), floor(150 * S), "Level complete!", 150, 235, 150, 255) end
    elseif scr == "skill" then
        W.drawPatch("M_NEWG", "NEW GAME", 96, 14, S, xbase, false)
        W.drawPatch("M_SKILL", "Choose Skill:", 54, 38, S, xbase, false)
        W.drawMenuList(W.SKILL_ITEMS, 48, 63, 16, S, xbase)
        if W.menu.nmConfirm then
            ImGui.AddRectFilled(0, floor(sh * 0.40), floor(sw), floor(sh * 0.68), 8, 6, 10, 235)
            W.drawMsgLines(W.STR.NIGHTMARE, sw * 0.5, sh * 0.43, 12 * S, 235, 120, 90, 255)
        end
    elseif scr == "options" then
        W.drawOptions(sw, sh, S, xbase)
    elseif scr == "readthis" then
        W.drawPatchFS("HELP1", sw, sh)
    elseif scr == "quit" then
        local msg = (W.QUITMSGS[W.quitMsgIdx or 1] or W.QUITMSGS[1]) .. "\n\n" .. W.STR.DOSY
        W.drawMsgLines(msg, sw * 0.5, sh * 0.42, 12 * S, 235, 210, 120, 255)
    end
end

function W.firstMap()
    local list = W.mapList or {}
    for _, m in ipairs(list) do if m == "E1M1" then return m end end
    for _, m in ipairs(list) do if m == "MAP01" then return m end end
    return list[1]
end

-- Large centered text. Uses SetWindowFontScale (CalcTextSize is read at the same
-- scale so centering stays correct); degrades to a width estimate if unavailable.
function W.bigText(text, cx, cy, scale, r, g, b, a)
    pcall(ImGui.SetWindowFontScale, scale)
    local tw, th = #text * 7 * scale, 13 * scale
    local cok, a1, a2 = pcall(ImGui.CalcTextSize, text)
    if cok then
        if type(a1) == "number" then tw = a1; if type(a2) == "number" then th = a2 end
        elseif type(a1) == "table" then tw = a1.x or tw; th = a1.y or th end
    end
    ImGui.AddText(floor(cx - tw / 2), floor(cy - th / 2), text, r, g, b, a)
    pcall(ImGui.SetWindowFontScale, 1.0)
end

-- hu_font (STCFNxxx) glyph lump name for a character byte, or nil for space and
-- anything the font lacks. The WAD font covers ASCII 33..95 (caps + punctuation)
-- only, so lowercase is uppercased first - exactly vanilla M_WriteText.
function W.fontLumpName(b)
    if b >= 97 and b <= 122 then b = b - 32 end
    if b < 33 or b > 95 then return nil end
    return string.format("STCFN%03d", b)
end

-- Screen-pixel width of one line in the hu_font at scale S (space/unknown glyph
-- advances 4 units, matching vanilla). Calling this also kicks the glyph bakes;
-- returns nil while any needed glyph is not yet GPU-ready so the caller can fall
-- back to plain ImGui text for the frame instead of drawing a gap-toothed line.
function W.fontLineWidth(line, S)
    local w, ready = 0, true
    for i = 1, #line do
        local nm = W.fontLumpName(line:byte(i))
        local pw = nm and W.patchSize(nm)
        if pw then
            w = w + pw
            if not W.menuTex(nm) then ready = false end
        else
            w = w + 4
        end
    end
    if not ready then return nil end
    return w * S
end

-- Draw one line in the hu_font, top-left anchored at (x,y), scale S, alpha a.
-- Glyph patches carry their own (red) palette colors, so no color tint applies.
function W.drawFontLine(line, x, y, S, a)
    local tint = (((a or 255) & 0xFF) << 24) | 0xFFFFFF
    for i = 1, #line do
        local nm = W.fontLumpName(line:byte(i))
        local pw, ph, plo, pto = nil, nil, nil, nil
        if nm then pw, ph, plo, pto = W.patchSize(nm) end
        local handle = pw and W.menuTex(nm)
        if handle then
            local gx = x - (plo or 0) * S; local gy = y - (pto or 0) * S
            ImGui.AddImage(handle, floor(gx), floor(gy),
                floor(gx + pw * S), floor(gy + ph * S), 0, 0, 1, 1, tint)
            x = x + pw * S
        else
            x = x + (pw or 4) * S
        end
    end
end

-- Draw a possibly multi-line string (\n separated) centered on cx, lines stacked
-- downward from y0. Used for the verbatim DOOM prompts (NIGHTMARE / quit taunts).
-- Rendered with the WAD's own hu_font like vanilla; the r/g/b ImGui text is only
-- the fallback while the glyphs bake or when the WAD lacks the STCFN lumps.
function W.drawMsgLines(text, cx, y0, lh, r, g, b, a)
    local S = lh / 12                       -- vanilla steps 12 doom-units per line
    local y = y0
    for line in (text .. "\n"):gmatch("(.-)\n") do
        local fw = (#line > 0) and W.fontLineWidth(line, S) or 0
        if fw then
            if fw > 0 then W.drawFontLine(line, floor(cx - fw / 2), floor(y), S, a) end
        else
            local w = #line * 7                       -- default-font width estimate
            local cok, a1 = pcall(ImGui.CalcTextSize, line)
            if cok then if type(a1) == "number" then w = a1 elseif type(a1) == "table" then w = a1.x or w end end
            ImGui.AddText(floor(cx - w / 2), floor(y), line, r, g, b, a)
        end
        y = y + lh
    end
end

-- Attract background: load the first map and pose a camera at the player start so
-- the menu (main/skill/options) renders over a live, slowly panning view of the
-- level instead of a black fill. Monsters/items are spawned (skill-filtered) so the
-- scene looks lived-in; they are NOT ticked (no AI) - the pan supplies the motion.
function W.startAttract()
    W.attractOn = true                       -- mark attempted so we do not reload every frame
    if not (W.mapList and #W.mapList > 0 and W.loadMap) then return end
    local nm = W.firstMap(); if not nm then return end
    local m = W.loadMap(nm); if not m then return end
    W.map = m
    W.activeSectors = {}
    local ax, ay, aang = 0, 0, 0
    for _, th in ipairs(m.things) do if th.dtype == 1 then ax, ay, aang = th.x, th.y, math.rad(th.angle); break end end
    W.attractCam = { x = ax, y = ay, ang = aang, t = 0 }
    W.viewX = ax; W.viewY = ay; W.viewAngle = aang
    W.pz = W.floorZAt(ax, ay)
    W.attractCam.baseZ = W.pz + W.EYE
    W.viewZ = W.attractCam.baseZ
    pcall(W.spawnActors, m)                  -- render a populated scene (static, not ticked)
end

function W.updateAttractCam(dt)
    local c = W.attractCam; if not c then return end
    c.t = c.t + dt
    c.ang = c.ang - dt * 0.12                 -- slow left pan
    W.viewX = c.x; W.viewY = c.y
    W.viewAngle = c.ang
    W.viewZ = (c.baseZ or W.EYE) + sin(c.t * 0.8) * 2   -- gentle bob
end

function W.launchGame(skill)
    W.skill = skill
    W.menu.fromPlay = false; W.menu.nmConfirm = false
    W.attractOn = false                             -- real map takes over; reload attract next visit
    W.newGame()
    pcall(W.playSfx, "DSPISTOL")
    W.startWipe("TITLEPIC")                          -- melt the title away over the first game frame
    W.startMap(W.firstMap())
end

function W.menuSelect()
    local m = W.menu
    if m.screen == "main" then
        local act = W.MENU_MAIN[m.cursor].act
        if act == "newgame" then m.screen = "skill"; m.cursor = 3; pcall(W.playSfx, "DSPISTOL")
        elseif act == "options" then m.screen = "options"; m.cursor = 1; pcall(W.playSfx, "DSPISTOL")
        elseif act == "readthis" then m.screen = "readthis"; pcall(W.playSfx, "DSPISTOL")
        elseif act == "quit" then
            m.screen = "quit"
            W.quitMsgIdx = (W.quitMsgIdx or 0) % #W.QUITMSGS + 1   -- rotate the taunt (endmsg[])
            pcall(W.playSfx, "DSSWTCHN")
        end
    elseif m.screen == "skill" then
        local it = W.SKILL_ITEMS[m.cursor]
        if it.skill == 5 then m.nmConfirm = true; pcall(W.playSfx, "DSSWTCHN") else W.launchGame(it.skill) end
    end
end

function W.menuBack()
    local m = W.menu
    if m.screen == "main" then
        if m.fromPlay and W.map then W.gameState = "play"
        else m.screen = "title"; m.fromPlay = false; W.attractOn = false end
        pcall(W.playSfx, "DSSWTCHX")
    else
        m.screen = "main"; m.cursor = 1; pcall(W.playSfx, "DSSWTCHN")
    end
end

-- Restart the currently-playing track at the new music volume (the volume is
-- baked into the cached .mid, so a change means a re-convert + replay). Deferred
-- to the present thread via musPending so every MCI call shares one thread.
function W.reapplyMusicVol()
    if W.musPlaying and W.musReq then W.musPending = W.musReq end
end

function W.optionAdjust(it, dir)
    if it.opt == "mouselook" then W.mouseLook = not W.mouseLook; pcall(W.playSfx, "DSPISTOL")
    elseif it.opt == "music" then
        W.musicOn = not W.musicOn
        if not W.musicOn then pcall(W.requestStop, "opt") elseif W.gameState == "play" and W.map then W.musPending = W.map.name end
        pcall(W.playSfx, "DSPISTOL")
    elseif it.opt == "musicvol" then
        W.musicVol = clamp((W.musicVol or 15) + dir, 0, 15)
        W.reapplyMusicVol(); pcall(W.playSfx, "DSPISTOL")
    elseif it.opt == "sfxvol" then
        W.sfxVol = clamp((W.sfxVol or 15) + dir, 0, 15)
        pcall(W.playSfx, "DSPISTOL")             -- audible preview at the new level
    elseif it.opt == "looksens" then
        W.LOOKSENS = clamp((W.LOOKSENS or 0.1) + dir * 0.02, 0.02, 0.5); pcall(W.playSfx, "DSSTNMOV")
    end
    pcall(W.saveSettings)                        -- auto-save on every change
end

function W.updateFrontend(dt)
    local m = W.menu
    local scr = m.screen
    if scr == "title" then
        if kpressed(W.VK.ENTER) or kpressed(W.VK.SPACE) then m.screen = "main"; m.cursor = 1; pcall(W.playSfx, "DSPISTOL") end
        return
    end
    if scr == "quit" then
        if kpressed(W.VK.Y) then
            -- Host mode: Quit fully unloads CheraxDoom back to GTA (same path the
            -- host's Stop button drives). Standalone closes the overlay too; the
            -- next Play Doom click reopens on the title screen.
            if BLAD_MODE then W.hostShutdown()
            else
                W.playOn = false; W.active = false
                m.screen = "title"; m.fromPlay = false; W.attractOn = false
                pcall(W.requestStop, "quit"); pcall(W.playSfx, "DSSWTCHX")
            end
        elseif kpressed(W.VK.N) or kpressed(W.VK.ESCAPE) or kpressed(W.VK.BACKSPACE) then m.screen = "main"; pcall(W.playSfx, "DSSWTCHX") end
        return
    end
    if scr == "readthis" then
        if kpressed(W.VK.ENTER) or kpressed(W.VK.SPACE) or kpressed(W.VK.ESCAPE) or kpressed(W.VK.BACKSPACE) then m.screen = "main"; pcall(W.playSfx, "DSSWTCHX") end
        return
    end
    if scr == "skill" and m.nmConfirm then
        if kpressed(W.VK.Y) then W.launchGame(5)
        elseif kpressed(W.VK.N) or kpressed(W.VK.ESCAPE) then m.nmConfirm = false; pcall(W.playSfx, "DSSWTCHX") end
        return
    end
    local list = (scr == "main" and W.MENU_MAIN) or (scr == "skill" and W.SKILL_ITEMS) or (scr == "options" and W.OPT_ITEMS)
    if not list then return end
    if kpressed(W.VK.DOWN) then m.cursor = (m.cursor % #list) + 1; pcall(W.playSfx, "DSPSTOP") end
    if kpressed(W.VK.UP) then m.cursor = ((m.cursor - 2) % #list) + 1; pcall(W.playSfx, "DSPSTOP") end
    if scr == "options" then
        if kpressed(W.VK.LEFT) then W.optionAdjust(list[m.cursor], -1)
        elseif kpressed(W.VK.RIGHT) or kpressed(W.VK.ENTER) then W.optionAdjust(list[m.cursor], 1) end
    elseif kpressed(W.VK.ENTER) then W.menuSelect() end
    if kpressed(W.VK.ESCAPE) or kpressed(W.VK.BACKSPACE) then W.menuBack() end
end

-- Screen melt (f_wipe.c "Melt"): the outgoing title texture slides down in strips
-- over the live incoming game frame. y[] is a virtual 200-tall per-column offset.
function W.startWipe(name)
    local wp = W.wipe
    wp.texName = name; wp.active = true; wp.acc = 0
    local y = wp.y
    y[1] = -(W.pRandom() % 16)
    for c = 2, wp.cols do
        local v = y[c - 1] + ((W.pRandom() % 3) - 1)
        if v > 0 then v = 0 elseif v < -15 then v = -15 end
        y[c] = v
    end
end

function W.updateWipe(dt)
    local wp = W.wipe
    if not wp.active then return end
    wp.acc = wp.acc + dt
    local step, H, y = 1 / 35, 200, wp.y
    while wp.acc >= step do
        wp.acc = wp.acc - step
        local anyWork = false
        for c = 1, wp.cols do
            local v = y[c]
            if v < 0 then y[c] = v + 1; anyWork = true
            elseif v < H then
                local d = (v < 16) and (v + 1) or 8
                if v + d >= H then d = H - v end
                y[c] = v + d; anyWork = true
            end
        end
        if not anyWork then wp.active = false; break end
    end
end

function W.drawWipe(sw, sh)
    local wp = W.wipe
    if not wp.active then return end
    local handle = wp.texName and W.menuTex(wp.texName)
    local cols, y = wp.cols, wp.y
    for c = 0, cols - 1 do
        local u0 = c / cols; local u1 = (c + 1) / cols
        local x0 = floor(u0 * sw); local x1 = floor(u1 * sw)
        local dy = floor(y[c + 1] / 200 * sh)
        if handle then
            ImGui.AddImage(handle, x0, dy, x1, dy + floor(sh), u0, 0.0, u1, 1.0, 0xFFFFFFFF)
        elseif dy > 0 then                           -- no title texture: black curtain fallback
            ImGui.AddRectFilled(x0, 0, x1, dy, 8, 6, 10, 255)
        end
    end
end

-- View interpolation: the sim runs at 35 Hz; the renderer swaps in a position
-- lerped between the last two tics (angle stays live for mouse latency) and
-- restores the sim values afterwards, even if the body errors.
function W.rSwap()
    if W.gameState ~= "play" or not W.oldPX then return end
    local a = clamp((W.specAccum or 0) / W.TIC, 0, 1)
    W.simVX, W.simVY, W.simVZ = W.viewX, W.viewY, W.viewZ
    W.viewX = W.oldPX + (W.viewX - W.oldPX) * a
    W.viewY = W.oldPY + (W.viewY - W.oldPY) * a
    W.viewZ = W.oldVZ + (W.viewZ - W.oldVZ) * a
end

function W.rRestore()
    if W.simVX then
        W.viewX, W.viewY, W.viewZ = W.simVX, W.simVY, W.simVZ
        W.simVX = nil
    end
end

function W.render()
    local sok, sw, sh = pcall(ImGui.GetDisplaySize)
    if not sok or not sw or sw < 16 or sh < 16 then return end
    ImGui.SetNextWindowPos(0, 0, ImGuiCond.Always)
    ImGui.SetNextWindowSize(sw, sh, ImGuiCond.Always)
    ImGui.Begin("##DoomWadOverlay", true, W.OVERLAY_FLAGS)
    -- Draw the body under pcall so a mid-frame error can never skip ImGui.End():
    -- an unbalanced Begin/End would desync the shared ImGui window stack and
    -- corrupt Cherax's own overlay/menu on later frames.
    W.rSwap()
    local bok, berr = pcall(W.renderBody, sw, sh)
    W.rRestore()
    ImGui.End()
    if not bok then Logger.LogError("[DOOMWAD] render body: " .. tostring(berr)) end
end

function W.renderBody(sw, sh)
    local gs = W.gameState
    if gs == "play" then
        W.setupView(sw, sh)
        W.drawBackground()                                  -- safety fill under planes/sky
        if W.map and W.map.usesSky then W.drawSky() end     -- sky over the ceiling region
        if W.map and W.map.rootNode then W.renderNode(W.map.rootNode) end  -- walls + plane capture
        W.drawPlanes()                                      -- fill the floor/ceiling gaps
        W.renderThings()                                    -- billboards over walls+planes (drawseg-clipped)
        W.drawWeapon(sw, W.viewH)                            -- view weapon over the world, under HUD
        W.drawHUD(sw, sh)
        if W.menuOpen then
            ImGui.AddText(floor(sw * 0.5 - 120), 8, "PAUSED - CLOSE MENU TO PLAY", 240, 220, 90, 255)
        end
    elseif gs == "intermission" then
        W.wiDraw(sw, sh)
    elseif gs == "frontend" then
        -- Button screens render over a live view: the attract level (fresh menu) or
        -- the frozen game (pause). The title screen keeps its full-screen TITLEPIC.
        if W.menu.screen ~= "title" and W.map and W.map.rootNode then
            ImGui.AddRectFilled(0, 0, floor(sw), floor(sh), 8, 6, 10, 255)  -- opaque base (covers HUD strip)
            W.setupView(sw, sh)
            W.drawBackground()
            if W.map.usesSky then W.drawSky() end
            W.renderNode(W.map.rootNode)
            W.drawPlanes()
            W.renderThings()
            ImGui.AddRectFilled(0, 0, floor(sw), floor(sh), 0, 0, 0, 100)   -- dim for menu legibility
        elseif W.menu.screen ~= "title" then
            ImGui.AddRectFilled(0, 0, floor(sw), floor(sh), 12, 10, 14, 255) -- fallback bg (no map yet)
        end
        W.drawFrontend(sw, sh)
    elseif gs == "menu" then
        ImGui.AddText(12, 12, "WAD loaded. Pick a map in the DOOM WAD tab. " .. tostring(W.status),
            200, 200, 205, 255)
    elseif gs == "loading" then
        ImGui.AddText(12, 12, "Loading " .. tostring(W.pendingMap or "") .. "...", 235, 220, 120, 255)
    elseif gs == "error" then
        ImGui.AddText(12, 12, "ERROR: " .. tostring(W.status), 235, 80, 70, 255)
        ImGui.AddText(12, 30, "Pick another wad or map in the DOOM WAD tab. ESC closes DOOM.", 200, 200, 205, 255)
    else
        ImGui.AddText(12, 12, "No WAD loaded. Open the DOOM WAD tab and use Download DOOM1.WAD,", 200, 200, 205, 255)
        ImGui.AddText(12, 30, "or drop a .wad in Cherax/Lua/DoomWad and press Scan. ESC closes DOOM.", 200, 200, 205, 255)
    end

    W.drawWipe(sw, sh)                           -- screen-melt overlay (over the live play frame)

    -- framerate counter (top-right), colour-coded
    local fps = floor((W.fps or 0) + 0.5)
    local fr, fg, fb = 90, 230, 110
    if fps < 30 then fr, fg, fb = 235, 70, 60 elseif fps < 60 then fr, fg, fb = 235, 210, 70 end
    ImGui.AddText(sw - 92, 6, string.format("FPS %d", fps), fr, fg, fb, 255)
end

-- Probe common locations for a shareware/retail wad. Best-effort: the tab also
-- lets the user pick one by hand. Fills W.wadCandidates.
function W.scanWads()
    local out, seen = {}, {}
    local function add(p)
        local k = p and p:lower()
        if p and p ~= "" and not seen[k] then seen[k] = true; out[#out + 1] = p end
    end
    -- Last-resort probe names for when FindFiles is unavailable or empty. This
    -- is NOT a filter: any .wad FindFiles returns is listed, whatever its name
    -- (openWad validates the IWAD/PWAD magic).
    local names = { "DOOM1.WAD", "DOOM.WAD", "DOOM2.WAD", "freedoom1.wad", "freedoom2.wad" }
    -- FindFiles' extension matching is finicky (dot-prefixed, case-sensitive;
    -- "" = every file), so query each spelling PLUS "" and keep anything that
    -- ends in .wad, case-insensitive, regardless of which query surfaced it.
    local exts = { ".wad", ".WAD", "" }
    local dirs = {}
    local rok, root = pcall(FileMgr.GetMenuRootPath)
    if rok and root and root ~= "" then
        -- Known-good FindFiles callers pass all-backslash directories with a
        -- trailing separator; a mixed-separator path can enumerate nothing.
        root = tostring(root):gsub("/", "\\")
        if root:sub(-1) == "\\" then root = root:sub(1, -2) end
        -- The Cherax root folder is cleared on update, so persistent user files
        -- live under Lua/. Prefer Lua/DoomWad, then Lua, before the volatile root.
        dirs[#dirs + 1] = root .. "\\Lua\\DoomWad\\"
        dirs[#dirs + 1] = root .. "\\Lua\\"
        dirs[#dirs + 1] = root .. "\\DoomWad\\"
        dirs[#dirs + 1] = root .. "\\"
        pcall(FileMgr.CreateDir, root .. "\\Lua\\DoomWad")   -- ensure a home for the wad + future cache
    end
    dirs[#dirs + 1] = ""   -- current working dir: name probes only (FindFiles chokes on ".")
    local hits = 0         -- FindFiles results seen (scan diagnostic, shown in the tab)
    local calls = 0        -- FindFiles calls that returned a usable container
    local function accept(f, d)
        f = tostring(f or "")
        if f:lower():sub(-4) ~= ".wad" then return end
        -- FindFiles may return bare names or full paths; accept whichever
        -- form actually exists so we never list an unopenable candidate.
        local full = d .. f
        local aok, ex = pcall(FileMgr.DoesFileExist, full)
        if aok and ex then add(full)
        else
            local bok, bex = pcall(FileMgr.DoesFileExist, f)
            if bok and bex then add(f) end
        end
    end
    for _, d in ipairs(dirs) do
        if FileMgr and FileMgr.FindFiles and d ~= "" then
            for _, ext in ipairs(exts) do
                local fok, list = pcall(FileMgr.FindFiles, d, ext, false)
                if fok and list ~= nil then
                    if type(list) == "table" then
                        calls = calls + 1
                        for _, f in ipairs(list) do hits = hits + 1; accept(f, d) end
                    else
                        -- sol2 may hand back a userdata container: length and
                        -- indexing go through metamethods, so probe via pcall.
                        local lok, ln = pcall(function() return #list end)
                        if lok and type(ln) == "number" then
                            calls = calls + 1
                            for i = 1, ln do
                                local gok, f = pcall(function() return list[i] end)
                                if gok and f then hits = hits + 1; accept(f, d) end
                            end
                        end
                    end
                end
            end
        end
        for _, n in ipairs(names) do
            local dok, ex = pcall(FileMgr.DoesFileExist, d .. n)
            if dok and ex then add(d .. n) end
        end
    end
    W.scanNote = string.format("FindFiles: %d usable calls, %d entries, %d wads listed", calls, hits, #out)
    W.wadCandidates = out
    return out
end

-- Put one wad path straight into the tab's candidate list (no folder scan),
-- deduped case-insensitively. Used by the shareware download button.
function W.addWadCandidate(p)
    if not p or p == "" then return end
    W.wadCandidates = W.wadCandidates or {}
    local k = p:lower()
    for _, q in ipairs(W.wadCandidates) do if q:lower() == k then return end end
    W.wadCandidates[#W.wadCandidates + 1] = p
end

-- Auto-load a wad + a starting map on first enable so the user can just walk.
function W.autoLoad()
    if W.autoTried then return end
    W.autoTried = true
    if W.wad then return end
    W.scanWads()
    local cand = W.wadCandidates and W.wadCandidates[1]
    if not cand then return end
    if not W.openWad(cand) then return end
    W.mapList = W.listMaps()
    W.menu.screen = "title"; W.menu.cursor = 1
    W.gameState = "frontend"                 -- land on the Doom title screen, not straight into a map
end

-- Fetch DOOM1.WAD (shareware IWAD) into Lua/DoomWad: the host-mode first-run
-- flow, and the standalone tab's download button (W.dlForce, which skips the
-- "some other wad already exists" early-out so DOOM1.WAD itself is fetched).
-- Async, driven from onPresent: returns "busy" while the transfer is in flight,
-- "done" once a wad is on disk (downloaded now OR already present), "failed" on a
-- hard error. Cherax's libcurl exposes no FOLLOWLOCATION, so we hit the final
-- raw.githubusercontent.com host directly (the github.com/raw path 302-redirects).
function W.ensureWadDownload()
    if W.dlDone then return "done" end
    if W.dlFailed then return "failed" end
    if not W.dlTarget then
        local rok, root = pcall(FileMgr.GetMenuRootPath)
        if not (rok and root and root ~= "") then W.dlFailed = true; return "failed" end
        root = tostring(root)
        pcall(FileMgr.CreateDir, root .. "/Lua/DoomWad")
        W.dlTarget = root .. "/Lua/DoomWad/DOOM1.WAD"
    end
    -- Respect a wad the user already placed (theirs, or ours from a prior run).
    if not W.dlChecked then
        W.dlChecked = true
        local dok, de = pcall(FileMgr.DoesFileExist, W.dlTarget)
        if dok and de then W.dlDone = true; return "done" end
        if not W.dlForce then
            -- Host boot flow only: any wad already on disk counts as done. The
            -- tab button (dlForce) always fetches DOOM1.WAD itself, no scan.
            local cands = W.scanWads()
            if cands and cands[1] then W.dlDone = true; return "done" end
        end
    end
    -- A finished transfer passed the cheap checks: pump the pinned-SHA-256
    -- verification, one ~96 KB slice per frame (hashing all 4.2 MB of pure Lua
    -- in one go would stall the present thread for a second or more). Accept the
    -- body only on an exact digest match; anything else counts as a failed
    -- attempt and rotates to the next source.
    if W.dlVerify then
        local v = W.dlVerify
        local ok = pcall(function()
            local stop = min(v.pos + 98303, #v.body)   -- 96 KB, 64-byte aligned
            W.sha256Feed(v.st, string.sub(v.body, v.pos, stop))
            v.pos = stop + 1
        end)
        if not ok then W.dlVerify = nil; return W.wadRetry() end
        if v.pos <= #v.body then return "busy" end
        local dok, digest = pcall(W.sha256Done, v.st)
        local body = v.body
        W.dlVerify = nil
        if dok and digest == WAD_SHA256 then
            if W.writeBytes(W.dlTarget, body) then W.dlDone = true; return "done" end
        end
        return W.wadRetry()   -- digest mismatch (or disk write failed)
    end
    -- Download sources. HTTPS host first; a plain-HTTP mirror is the fallback.
    -- Cherax's curl exposes NO TLS options (no verify/revoke/CAINFO), so a broken
    -- Windows schannel ("AcquireCredentialsHandle failed / Local Security Authority
    -- cannot be contacted") sinks EVERY HTTPS attempt - an HTTP URL skips the TLS
    -- handshake entirely and works anyway. Both serve the byte-identical 4.2 MB
    -- shareware IWAD; because HTTP is unauthenticated the body is only trusted
    -- after it matches the pinned exact size + SHA-256 (see WAD_SHA256).
    W.WAD_URLS = W.WAD_URLS or { WAD_URL, "http://distro.ibiblio.org/slitaz/sources/packages/d/doom1.wad" }
    W.dlIdx = W.dlIdx or 1
    W.dlTries = W.dlTries or 0
    W.dlMaxTries = W.dlMaxTries or 6            -- ~3 passes over the source list before giving up
    -- Kick a fresh attempt (a new handle each time; a reused handle can hold bad state).
    if not W.dlHandle then
        if now() < (W.dlNextTry or 0) then return "busy" end     -- honor the retry cooldown
        local url = W.WAD_URLS[W.dlIdx]
        local ok = pcall(function()
            local h = Curl.Easy()
            h:Setopt(eCurlOption.CURLOPT_URL, url)
            h:Setopt(eCurlOption.CURLOPT_USERAGENT, "CheraxDoom-WAD")
            h:Perform()
            W.dlHandle = h
        end)
        if not ok or not W.dlHandle then W.dlHandle = nil; return W.wadRetry() end
        W.dlStart = now()
    end
    -- Poll the in-flight transfer.
    local fin = false
    pcall(function() fin = W.dlHandle:GetFinished() end)
    if not fin then
        if (now() - (W.dlStart or 0)) > 60 then W.dlHandle = nil; return W.wadRetry() end
        return "busy"
    end
    local code, body
    pcall(function() code, body = W.dlHandle:GetResponse() end)
    W.dlHandle = nil
    local magic = (type(body) == "string") and body:sub(1, 4) or ""
    if code == eCurlCode.CURLE_OK and type(body) == "string" and #body == WAD_SIZE
        and magic == "IWAD" then
        -- Cheap checks pass; hand the body to the sliced SHA-256 verify above.
        W.dlVerify = { body = body, pos = 1, st = W.sha256New() }
        return "busy"
    end
    return W.wadRetry()
end

-- Record a failed attempt, rotate to the next source, and either schedule a retry
-- after a short cooldown or give up once the attempt cap is reached.
function W.wadRetry()
    W.dlTries = (W.dlTries or 0) + 1
    W.dlIdx = (W.dlIdx or 1) + 1
    if W.dlIdx > #W.WAD_URLS then W.dlIdx = 1 end
    if W.dlTries >= (W.dlMaxTries or 6) then W.dlFailed = true; return "failed" end
    W.dlNextTry = now() + 2.5
    return "busy"
end

-- Minimal boot overlay drawn while the host-mode wad download is in flight (or on
-- failure). Mirrors W.render's single-window structure so the ImGui stack stays
-- balanced; the normal renderer takes over once the wad is ready.
function W.drawBootProgress(st)
    local sok, sw, sh = pcall(ImGui.GetDisplaySize)
    if not sok or not sw or sw < 16 or sh < 16 then return end
    ImGui.SetNextWindowPos(0, 0, ImGuiCond.Always)
    ImGui.SetNextWindowSize(sw, sh, ImGuiCond.Always)
    ImGui.Begin("##DoomWadOverlay", true, W.OVERLAY_FLAGS)
    pcall(function()
        ImGui.AddRectFilled(0, 0, floor(sw), floor(sh), 8, 6, 10, 255)
        local cx, cy = floor(sw * 0.5 - 150), floor(sh * 0.5 - 8)
        if st == "failed" then
            ImGui.AddText(cx, cy, "DOOM1.WAD download failed.", 235, 80, 70, 255)
            ImGui.AddText(cx, cy + 18, "Check your connection, or drop DOOM1.WAD in", 200, 200, 205, 255)
            ImGui.AddText(cx, cy + 34, "Cherax/Lua/DoomWad and reopen DOOM.", 200, 200, 205, 255)
        else
            local txt
            if W.dlVerify then
                local pct = floor(100 * (W.dlVerify.pos - 1) / max(1, #W.dlVerify.body))
                txt = "Verifying DOOM1.WAD... " .. pct .. "%"
            else
                local n = W.dlTries or 0
                txt = "Downloading DOOM1.WAD..." .. ((n > 0) and (" (retry " .. n .. ")") or "")
            end
            ImGui.AddText(cx, cy, txt, 235, 220, 120, 255)
        end
    end)
    ImGui.End()
end

-- Host mode: unload this script (stop music first). Both the hidden shutdown
-- feature (host OnClick) and DOOM's own in-game Quit route here. The unload is
-- DEFERRED a few frames: MCI only answers on the present thread (stop/close sent
-- from the OnClick or unload threads return false per the in-game log), and an
-- immediate SetShouldUnload would kill the present-thread retry window before it
-- ever delivered the stop. So request the stop, mark shutdown pending, and let
-- onPresent service the stop first; it calls SetShouldUnload when the countdown
-- runs out, which marks THIS script done and returns the player to GTA.
function W.hostShutdown()
    pcall(W.requestStop, "shutdown")
    if not SetShouldUnload then return end
    W.unloadIn = W.unloadIn or 10        -- frames of present-thread stop retries
end

function W.init()
    W.OVERLAY_FLAGS = 0
    pcall(function()
        W.OVERLAY_FLAGS = ImGuiWindowFlags.NoTitleBar | ImGuiWindowFlags.NoResize
            | ImGuiWindowFlags.NoMove | ImGuiWindowFlags.NoScrollbar
            | ImGuiWindowFlags.NoScrollWithMouse | ImGuiWindowFlags.NoCollapse
            | ImGuiWindowFlags.NoBackground | ImGuiWindowFlags.NoSavedSettings
            | ImGuiWindowFlags.NoBringToFrontOnFocus
            | ImGuiWindowFlags.NoFocusOnAppearing | ImGuiWindowFlags.NoInputs
            | ImGuiWindowFlags.NoNav
    end)
    -- Player physics constants (vanilla units; movement itself is momentum
    -- + friction on the 35 Hz tic clock, see W.playerXYMovement). Turn rates
    -- are the BAM angleturn {320,640,1280}<<16 per tic as radians/second.
    W.EYE = 41; W.RADIUS = 16; W.MAXSTEP = 24; W.PHEIGHT = 56
    W.NEARZ = 4; W.HFOV = pi / 2
    W.MAXMOVE = 30                       -- momentum clamp, units/tic
    W.TURNSLOW = (320 / 65536) * TWO_PI * 35
    W.TURNNORM = (640 / 65536) * TWO_PI * 35
    W.TURNFAST = (1280 / 65536) * TWO_PI * 35
    W.FLOATSPEED = 4                     -- cacodemon vertical adjust, units/tic
    W.LOOKSENS = 0.1                     -- mouse turn sensitivity (GTA INPUT_LOOK_LR -> radians)
    -- Phase-4 visplane (textured floors/ceilings) + sky constants.
    W.ROWSTEP = 2          -- plane row granularity (1=full res, 2=half draws)
    W.FLAT_TILE = 8        -- flats baked tiled NxN (8 => 512x512); 1 uv unit = 64*8 world units
    W.PLANE_BUDGET = 3200  -- max plane image/solid draws per frame; degrade past this
    W.PLANE_FOG = 0.00072  -- distance-diminish rate (shared by walls, planes, sprites)
    W.SKY_DIR = -1         -- sky scroll sign (-1 locks sky to world motion; flip if wrong)
    W.PLANECOL = { floor = { 70, 54, 40 }, ceil = { 40, 42, 52 } } -- fallback tones (no flat/tex)
    -- Phase-5 sprite (billboard THINGS) constants.
    W.SPRITE_MAXDIST = 4000; W.SPRITE_MAXDIST2 = W.SPRITE_MAXDIST * W.SPRITE_MAXDIST
    W.SPRITE_MAX = 96          -- max sprites drawn/frame (nearest kept after far->near sort)
    W.SPRITE_BUDGET = 400      -- hard cap on AddImage/placeholder runs/frame
    W.SPRITE_PLACEHOLDER = true -- faint kind-colored rect while a sprite bakes
    W.DS_MAXSEGS = 2048        -- max silhouette-occluder segs recorded per frame
    -- Phase-6 enemy AI (p_enemy.c) constants.
    W.SIGHT_RANGE = 8192       -- perf guard only; vanilla sight is unbounded
    -- combat / weapon input state (inventory itself lives in W.newGame)
    W.psp = { st = nil, tics = -1, sx = 1, sy = 32 }
    W.psf = { st = nil, tics = -1 }
    W.attackdown = false; W.refire = 0; W.extralight = 0
    W.fireHeld = false; W.usePressed = false; W.fireArmed = false
    W.momx = 0; W.momy = 0; W.momz = 0; W.bob = 0
    W.pz = 0; W.viewheight = 41; W.dvh = 0
    W.reactionTics = 0; W.turnHeld = 0
    W.cmdForward = 0; W.cmdSide = 0
    W.stInit()
    -- camera / view state
    W.viewX = 0; W.viewY = 0; W.viewZ = W.EYE; W.viewAngle = 0
    W.active = false
    W.playOn = false          -- standalone launch flag (Play Doom button / Quit Game)
    W.mouseLook = false
    -- audio / music state (Section M). musicOn is a user toggle (default on);
    -- looping is duration-driven off now() since MCI cannot report position.
    -- musicVol/sfxVol are 0..15 (DOOM's range), baked into the cached MIDI/WAV.
    -- These defaults are overridden by W.loadSettings on first activation.
    W.musicOn = true
    W.musicVol = 15
    W.sfxVol = 15
    W.musPlaying = false
    W.musStart = 0
    W.musLen = 0
    W.musTrack = nil
    W.musAlias = "doommus"    -- MCI device alias
    W.musLenByName = {}       -- cached track duration in seconds, keyed by lump name
    W.stopRetries = 0         -- frames left to re-send the music stop (robust stop)
    W.musPending = nil        -- map name whose music start is deferred to the present thread
    W.stopDiag = true         -- log stop attempts to cherax.log (diagnose in-game)
    W.autoTried = false
    W.curKey = {}
    W.prevKey = {}
    W.fps = nil
    W.lastTime = nil
    W.state = W.state or "nowad"
    if not W.status or W.status == "" then W.status = "no wad loaded" end
    -- front-end menu + screen-melt state (SECTION N), built once and reused
    W.menu = { screen = "title", cursor = 1, nmConfirm = false, fromPlay = false }
    W.wipe = { active = false, cols = 160, acc = 0, texName = nil, y = {} }
    for i = 1, W.wipe.cols do W.wipe.y[i] = 0 end
    W.gameState = (W.wad and "frontend") or "nowad"
end

function W.onPresent()
    -- Re-send any pending music stop every frame, regardless of enabled state, so
    -- a toggle-off/unload stop that did not take is retried (mirrors the working
    -- per-frame manual-disable path).
    W.serviceStop()
    -- Deferred hostShutdown: keep only the stop retries running for a few frames
    -- so the music stop lands on this thread, then actually unload.
    if W.unloadIn then
        W.unloadIn = W.unloadIn - 1
        if W.unloadIn <= 0 then
            W.unloadIn = nil
            if SetShouldUnload then pcall(SetShouldUnload) end
        end
        return
    end
    -- Standalone: service the tab's shareware-download button even while DOOM
    -- itself is closed (the click only arms it; the curl transfer polls here,
    -- and the finished wad goes straight onto the candidate list - no scan).
    if W.dlWanted then
        local st = W.ensureWadDownload()
        if st ~= "busy" then
            W.dlWanted = false
            if st == "done" and W.dlTarget then
                W.addWadCandidate(W.dlTarget)
                -- Nothing loaded yet: open the fresh wad right away so the
                -- overlay (open now or on the next Play click) lands on the
                -- title screen instead of the no-wad help text.
                if not W.wad and W.openWad(W.dlTarget) then
                    W.mapList = W.listMaps()
                    W.menu.screen = "title"; W.menu.cursor = 1
                    W.gameState = "frontend"
                end
            end
        end
    end
    -- Host mode runs unconditionally; standalone runs while the Play Doom
    -- button has it open (DOOM's own Quit Game closes it again).
    local enabled = BLAD_MODE or W.playOn or false
    if not enabled then
        -- Feature toggled off: request a stop with retries. Trigger only on the
        -- transition (musPlaying or active still set) so we do not spam forever.
        if W.musPlaying or W.active then
            if W.stopDiag and Logger and Logger.LogInfo then
                pcall(Logger.LogInfo, "[DOOMWAD] onPresent: feature disabled -> requestStop")
            end
            W.requestStop("disable")
        end
        W.active = false
        return
    end
    -- Host mode: pull the shareware IWAD into Lua/DoomWad on first run so the user
    -- drops straight into DOOM with nothing to place by hand. Hold here (drawing a
    -- progress overlay) until the wad is on disk, then fall through to the normal
    -- autoLoad below. A failure falls through too: the nowad screen and the DOOM
    -- WAD tab still let the user supply a wad by hand.
    if BLAD_MODE and not W.dlDone and not W.dlFailed then
        local st = W.ensureWadDownload()
        -- Only paint the boot overlay while still waiting/failed; on the frame the
        -- wad becomes ready, fall straight through to the normal renderer so we
        -- don't open the shared overlay window twice in one frame.
        if st ~= "done" then W.drawBootProgress(st); return end
    end

    if not W.active then
        W.active = true
        W.lastTime = now()
        pcall(W.loadSettings)                -- restore saved options before anything uses them
        pcall(W.autoLoad)
        -- Re-enable: autoLoad only runs once, so resume the already-loaded map's
        -- music (deferred to the musPending service below, on this present thread).
        if W.gameState == "play" and W.map and W.musicOn and not W.musPlaying then
            W.musPending = W.map.name
        end
    end

    -- Service a deferred music start on the present thread so every MCI open (and
    -- thus every stop) shares one thread. playMusic clears stopRetries.
    if W.musPending then
        local mn = W.musPending; W.musPending = nil
        pcall(W.playMusic, mn)
    end

    local t = now()
    local rawDt = t - (W.lastTime or t)
    W.lastTime = t
    if rawDt <= 0 then rawDt = 0.001 end
    local inst = 1 / rawDt
    W.fps = W.fps and (W.fps + (inst - W.fps) * 0.1) or inst
    local dt = rawDt
    if dt > 0.05 then dt = 0.05 end

    local menuOpen = false
    local mok, r = pcall(function() return GUI.IsOpen() end)
    if mok and r ~= nil then menuOpen = r end
    W.menuOpen = menuOpen

    -- Music loops off the wall clock and must keep running while the Cherax menu
    -- is open (world update/render are gated on menuOpen; music is not).
    pcall(W.updateMusic)

    -- refresh tracked keys for rising-edge detection
    local cur = W.curKey; local prev = W.prevKey
    for _, vk in ipairs(W.trackVK) do
        prev[vk] = cur[vk]
        cur[vk] = ((not menuOpen) and kdown(vk)) or false
    end

    if (W.gameState == "play" or W.gameState == "frontend") and not menuOpen then W.suppressGameInput() end

    local uok, uerr = pcall(W.update, dt, menuOpen)
    if not uok then Logger.LogError("[DOOMWAD] update: " .. tostring(uerr)) end
    local rok, rerr = pcall(W.render)
    if not rok then Logger.LogError("[DOOMWAD] render: " .. tostring(rerr)) end
end

-- one clickable row: prefer Selectable, fall back to Button, else static text
function W.uiRow(label)
    if ImGui.Selectable then local ok, r = pcall(ImGui.Selectable, label); return ok and r end
    if ImGui.Button then local ok, r = pcall(ImGui.Button, label); return ok and r end
    if ImGui.Text then ImGui.Text(label) end
    return false
end

function W.renderTab()
    if ClickGUI.RenderFeature then pcall(ClickGUI.RenderFeature, FEATURE_HASH) end
    if ImGui.Separator then ImGui.Separator() end
    if not ImGui.Text then return end
    ImGui.Text("Click Play Doom, then close the Cherax menu. Quit Game inside DOOM returns to GTA.")
    ImGui.Text("Plays any DOOM-format .wad (DOOM/DOOM2/TNT/Plutonia/FreeDoom).")
    ImGui.Text("Drop wads in Cherax/Lua/DoomWad (or Cherax/Lua), or use the download button below.")
    ImGui.Text("State: " .. tostring(W.gameState) .. "    " .. tostring(W.status or ""))
    if ImGui.Separator then ImGui.Separator() end

    -- WAD picker
    ImGui.Text("WAD: " .. tostring(W.wadPath or "(none)"))
    if W.uiRow("Scan for WAD files") then W.scanWads() end
    if W.uiRow("Download DOOM1.WAD (shareware, 4 MB)") then
        -- Arm/re-arm the async download; onPresent polls it and puts the wad
        -- straight onto the list below on success (no folder scan involved).
        W.dlWanted = true; W.dlForce = true
        W.dlDone = false; W.dlChecked = false; W.dlFailed = false
        W.dlTries = 0; W.dlIdx = 1; W.dlNextTry = 0; W.dlVerify = nil
    end
    if W.dlWanted then
        ImGui.Text(W.dlVerify and "Verifying DOOM1.WAD..." or "Downloading DOOM1.WAD...")
    elseif W.dlForce and W.dlFailed then
        ImGui.Text("Download failed. Check your connection and click again.")
    end
    if W.wadCandidates and #W.wadCandidates > 0 then
        for _, p in ipairs(W.wadCandidates) do
            if W.uiRow("Load: " .. p) then
                local opened = W.openWad(p)
                if opened then W.mapList = W.listMaps(); W.menu.screen = "title"; W.menu.cursor = 1 end
                W.gameState = opened and "frontend" or "error"
            end
        end
    end

    -- Difficulty (temporary dev selector; the real skill-select screen lands with
    -- the frontend menu). Cycling here sets W.skill for the next map launch.
    if W.mapList and #W.mapList > 0 then
        if ImGui.Separator then ImGui.Separator() end
        W.skill = W.skill or 3
        if W.uiRow("Skill: " .. (W.SKILLNAME[W.skill] or "?") .. "  (click to cycle)") then
            W.skill = (W.skill % 5) + 1
        end
    end

    -- Map picker (populated after a wad loads)
    if W.mapList and #W.mapList > 0 then
        if ImGui.Separator then ImGui.Separator() end
        ImGui.Text("Maps (" .. #W.mapList .. "):  skill = " .. (W.SKILLNAME[W.skill or 3] or "?"))
        for _, name in ipairs(W.mapList) do
            if W.uiRow(name) then W.newGame(); W.startMap(name) end
        end
    end

    -- Music controls (best-effort; MCI failures are swallowed by W.mci)
    if ImGui.Separator then ImGui.Separator() end
    if ImGui.Checkbox then
        local v, changed = ImGui.Checkbox("Music", W.musicOn)
        if changed then
            W.musicOn = v
            -- menu thread: request a retried stop, or defer the start to onPresent
            if not v then W.requestStop("music-cb")
            elseif W.gameState == "play" and W.map then W.musPending = W.map.name end
        end
    end
    if ImGui.Text then
        ImGui.Text("Now playing: " .. tostring(W.musTrack or "(none)"))
        -- (MIDI volume is not adjustable: the Windows MCI sequencer device has
        --  no volume command, so use your system volume mixer for the game.)
    end

    if ImGui.Separator then ImGui.Separator() end
    ImGui.Text("Controls:")
    ImGui.Text("Move: W/S or Up/Down      Strafe: A/D")
    ImGui.Text("Turn: Left/Right or Mouse (toggle with M)")
    ImGui.Text("Run: Shift                Back to map menu: Backspace")
end

W.init()

-- Inert test seam: only exposes internals when a harness sets __DOOMWAD_TEST.
-- Cherax never sets this global, so this is a no-op in production.
if rawget(_G, "__DOOMWAD_TEST") then _G.__DOOMWAD = W end

-- Standalone only: the Play Doom button is the launch switch and lives in the
-- tab; quitting from DOOM's own menu (or ESC on the no-wad/error screens) closes
-- it again. In host mode we auto-run, so neither the button nor the tab are
-- registered; the only UI is the fullscreen DOOM overlay window.
if (not BLAD_MODE) and FeatureMgr and FeatureMgr.AddFeature then
    pcall(FeatureMgr.AddFeature, FEATURE_HASH, "Play Doom",
        (eFeatureType and eFeatureType.Button) or 0,
        "Play DOOM in the overlay: click, then close the Cherax menu. Quit Game inside DOOM returns to GTA.",
        function() W.playOn = true end)
end

-- Register the hidden cross-script shutdown feature in ALL modes (was host-only).
-- The host resolves SHUTDOWN_HASH from the shared registry and OnClick()s it;
-- that callback runs in THIS script's state (via W.hostShutdown), so
-- SetShouldUnload marks this script for unload, never the host. It also serves
-- as a liveness heartbeat: a host script that sees it leave the registry stops
-- any still-playing music from its own live state, which covers a direct
-- uninject of this file even when it was not launched through the host. Never
-- RenderFeature'd, invisible.
if FeatureMgr and FeatureMgr.AddFeature and SHUTDOWN_HASH ~= 0 then
    local sf = FeatureMgr.AddFeature(SHUTDOWN_HASH, "CheraxDoom Shutdown",
        (eFeatureType and eFeatureType.Button) or 0,
        "Internal: unload CheraxDoom. Triggered by the host script, not for direct use.",
        function() W.hostShutdown() end)
    if sf then
        pcall(function() sf:SetVisible(false) end)
        pcall(function() sf:SetSaveable(false) end)
    end
end

if EventMgr and EventMgr.RegisterHandler then
    pcall(EventMgr.RegisterHandler, (eLuaEvent and eLuaEvent.ON_PRESENT) or 7, W.onPresent)
    -- On unload (uninject), stop the music via the TEARDOWN PRESENT FRAMES.
    -- The MCI device is only reachable from the thread that opened it (the
    -- present thread); every direct attempt from this unload thread fails
    -- (alias commands return false, 'stop all'/'close all' return true against
    -- an empty device view and silence nothing). But ON_PRESENT keeps firing
    -- for a few frames after this handler runs (verified in-game: an MCI stop
    -- from one of those frames returns true and the music dies), and
    -- W.serviceStop is the first thing onPresent does each frame. So arming
    -- the retry counter here is the entire fix; the next present frame sends
    -- stop+close from the right thread.
    pcall(EventMgr.RegisterHandler, (eLuaEvent and eLuaEvent.ON_UNLOAD) or 11, function()
        W.musPlaying = false; W.musTrack = nil
        W.stopRetries = 60
        if Utils and Utils.StopSound then pcall(Utils.StopSound) end
        -- Drop the hidden cross-script shutdown feature so no stale entry lingers
        -- in the shared registry for the next launch. (The host, if present, sees
        -- it vanish and also stops the music from its own present-thread tick.)
        if FeatureMgr and FeatureMgr.RemoveFeature then
            pcall(FeatureMgr.RemoveFeature, SHUTDOWN_HASH)
        end
        if W.stopDiag and Logger and Logger.LogInfo then
            pcall(Logger.LogInfo, "[DOOMWAD] ON_UNLOAD: stop delegated to teardown present frames")
        end
    end)
end

if (not BLAD_MODE) and ClickGUI and ClickGUI.AddTab then
    pcall(ClickGUI.AddTab, "DOOM WAD", W.renderTab)
end

if Logger and Logger.LogInfo then
    pcall(Logger.LogInfo, "[DOOMWAD] loaded (phase 3: textured BSP walls + on-disk PNG cache).")
end

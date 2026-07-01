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
    if not W.cacheDir then
        local rok, root = pcall(FileMgr.GetMenuRootPath)
        if rok and root and root ~= "" then
            root = tostring(root)
            W.cacheDir = root .. "/Lua/DoomWad/cache"
            pcall(FileMgr.CreateDir, root .. "/Lua/DoomWad")
            pcall(FileMgr.CreateDir, W.cacheDir)
        end
    end
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
    W.hudH = floor(sh * 0.10)              -- slim HUD strip at the bottom
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

-- Brightness scalar = sector light x distance diminish, with a side darken so
-- N-S walls read slightly darker than E-W ones (fake directional). Shared by the
-- flat-shaded path (as a color multiplier) and the textured path (as a grey tint).
function W.wallLight(sector, depth, seg)
    local lf = 0.22 + 0.78 * (sector.light / 255)
    local fog = clamp(1.0 - depth * W.PLANE_FOG, 0.26, 1.0)
    local br = clamp(lf * fog, 0.10, 1.15)
    local v1 = W.map.vertexes[seg.v1 + 1]
    local v2 = W.map.vertexes[seg.v2 + 1]
    if v1 and v2 and abs(v2.x - v1.x) < abs(v2.y - v1.y) then br = br * 0.86 end
    return br
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
                if solid then
                    texMid = W.getTex(sd.mid, false); dMid = sd.mid and W.texDefs[sd.mid]
                else
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
-- W.wallLight minus the seg side-darken so floors read with the walls).
function W.planeLight(light, rowDist)
    local lf = 0.22 + 0.78 * (light / 255)
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
    [2014] = { k = "health", amt = 1,   max = 200, always = true, msg = "Picked up a health bonus." },
    [2013] = { k = "health", amt = 100, max = 200, always = true, msg = "Supercharge!" },
    [83]   = { k = "mega", msg = "MegaSphere!" },
    [2018] = { k = "armor", pts = 100, atype = 1, msg = "Picked up the armor." },
    [2019] = { k = "armor", pts = 200, atype = 2, msg = "Picked up the MegaArmor!" },
    [2015] = { k = "armorbonus", amt = 1, max = 200, always = true, msg = "Picked up an armor bonus." },
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
    [2022] = { k = "power", pw = "invuln",  msg = "Invulnerability!" },
    [2023] = { k = "power", pw = "berserk", heal = 100, msg = "Berserk!" },
    [2024] = { k = "power", pw = "invis",   msg = "Partial Invisibility." },
    [2025] = { k = "power", pw = "radsuit", msg = "Radiation Shielding Suit." },
    [2026] = { k = "power", pw = "allmap",  msg = "Computer Area Map." },
    [2045] = { k = "power", pw = "infrared", msg = "Light Amplification Visor." },
}
W.KEYCOL = { blue = {80,120,255}, yellow = {255,220,60}, red = {255,70,60} }
W.WEAPNAME = { [1]="FIST", [2]="PISTOL", [3]="SHOTGUN", [4]="CHAINGUN",
    [5]="ROCKET", [6]="PLASMA", [7]="BFG9000", [8]="CHAINSAW", [9]="SSG" }
-- number key -> first OWNED slot in preference order (SSG over shotgun, saw over fist)
W.SLOTKEY = { [1]={8,1}, [2]={2}, [3]={9,3}, [4]={4}, [5]={5}, [6]={6}, [7]={7} }
-- HUD ammo key per weapon slot (stub until W.WEAPONS lands in the combat chunk)
W.HUDAMMOKEY = { [2]="bul", [3]="shl", [4]="bul", [5]="rck", [6]="cel", [7]="cel", [9]="shl" }
-- monster spawn HP by sprite prefix (full W.MOBJINFO lands with the AI chunk)
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

-- Monster behaviour by sprite prefix (info.c mobjinfo + a lean per-state frame map).
-- speed is units/SECOND; radius comes from W.THING_SPR[dtype].r. dmg/melee are
-- P_Random damage closures. fireAt = 1-based index in the atk frame string that
-- triggers the hit/shot. eye = attack/sight source height above the actor floor.
W.MOBJINFO = {
    POSS = { hp=20, speed=128, pain=200, eye=42, atk="hitscan", shots=1,
        dmg=function() return (W.pRandom()%5+1)*3 end,
        frames={ walk="AABBCCDD", pain="G", atk="EF", fireAt=2, death="HIJKL", xdeath="OPQRST" } },
    SPOS = { hp=30, speed=128, pain=170, eye=42, atk="hitscan", shots=3,
        dmg=function() return (W.pRandom()%5+1)*3 end,
        frames={ walk="AABBCCDD", pain="G", atk="EF", fireAt=2, death="HIJKL", xdeath="OPQRSTU" } },
    TROO = { hp=60, speed=96, pain=200, eye=42, atk="missile", proj="TROOPSHOT", mrange=64,
        melee=function() return (W.pRandom()%8+1)*3 end,
        frames={ walk="AABBCCDD", pain="H", atk="EFG", fireAt=3, death="IJKLM", xdeath="NOPQRS" } },
    SARG = { hp=150, speed=160, pain=180, eye=42, atk="melee", mrange=64,
        melee=function() return (W.pRandom()%10+1)*4 end,
        frames={ walk="AABBCCDD", pain="H", atk="EF", fireAt=2, death="IJKLMN" } },
    HEAD = { hp=400, speed=64, pain=128, eye=48, atk="missile", proj="HEADSHOT", float=true,
        melee=function() return (W.pRandom()%6+1)*10 end,
        frames={ walk="A", pain="D", atk="BC", fireAt=2, death="EFGHIJK" } },
    BOSS = { hp=1000, speed=96, pain=50, eye=48, atk="missile", proj="BRUISERSHOT", mrange=64,
        melee=function() return (W.pRandom()%8+1)*10 end,
        frames={ walk="AABBCCDD", pain="H", atk="EFG", fireAt=3, death="IJKLMNO" } },
}
W.BARREL = { hp=20, boomdmg=128, boomrad=128, frames={ boom="ABCDE" } }  -- BAR1 dtype 2035

-- 8-direction movement tables (p_enemy.c dirtype). movedir 0..7 = E,NE,N,NW,W,SW,S,SE;
-- 8 = DI_NODIR. DIRX/DIRY are unit steps; DIRDEG is the facing angle for sprite rotation.
W.DIRX = { 1, 0.7071, 0, -0.7071, -1, -0.7071, 0, 0.7071 }
W.DIRY = { 0, 0.7071, 1, 0.7071, 0, -0.7071, -1, -0.7071 }
W.DIRDEG = { 0, 45, 90, 135, 180, 225, 270, 315 }
W.OPPOSITE = { [0]=4, [1]=5, [2]=6, [3]=7, [4]=0, [5]=1, [6]=2, [7]=3, [8]=8 }
W.DIAGS = { 3, 1, 5, 7 }        -- NW,NE,SW,SE, indexed ((dy<0)<<1)+(dx>0) + 1
-- Per-species sound lumps (DOOM1.WAD): wake (sight), ranged attack, melee. Stamped
-- onto the matching W.MOBJINFO entry so the AI can play them by species.
W.MONSND = {
    POSS = { sight="DSPOSIT1", asfx="DSPISTOL", psfx="DSPOPAIN", dsfx="DSPODTH1" },
    SPOS = { sight="DSPOSIT2", asfx="DSSHOTGN", psfx="DSPOPAIN", dsfx="DSPODTH2" },
    TROO = { sight="DSBGSIT1", asfx="DSFIRSHT", msfx="DSCLAW", psfx="DSPOPAIN", dsfx="DSBGDTH1" },
    SARG = { sight="DSSGTSIT", msfx="DSSGTATK", psfx="DSDMPAIN", dsfx="DSSGTDTH" },
    HEAD = { sight="DSCACSIT", asfx="DSFIRSHT", msfx="DSCLAW", psfx="DSDMPAIN", dsfx="DSCACDTH" },
    BOSS = { sight="DSBRSSIT", asfx="DSFIRSHT", msfx="DSCLAW", psfx="DSDMPAIN", dsfx="DSBRSDTH" },
}
for k, s in pairs(W.MONSND) do
    local mi = W.MOBJINFO[k]
    if mi then mi.sight = s.sight; mi.asfx = s.asfx; mi.msfx = s.msfx; mi.psfx = s.psfx; mi.dsfx = s.dsfx end
end

-- Player weapons (p_pspr.c). fireS = summed firing-state tics; dmg = P_Random rolls;
-- pellets + spread; range 2048 (MISSILERANGE); proj weapons defer to chunk 4.
W.WEAPONS = {
    [1] = { name="FIST", ammo=nil, cost=0, fireS=13*W.TIC, spr="PUNG", fire="B", melee=true, range=64,
        dmg=function() return (W.pRandom()%10+1)*2*(W.powers and W.powers.berserk and 10 or 1) end, sfx="DSPUNCH", auto=true },
    [2] = { name="PISTOL", ammo="bul", cost=1, fireS=19*W.TIC, spr="PISG", fire="B", flash="PISF",
        dmg=function() return 5*(W.pRandom()%3+1) end, pellets=1, accurate=true, range=2048, sfx="DSPISTOL", auto=true },
    [3] = { name="SHOTGUN", ammo="shl", cost=1, fireS=44*W.TIC, spr="SHTG", fire="A", flash="SHTF",
        dmg=function() return 5*(W.pRandom()%3+1) end, pellets=7, range=2048, sfx="DSSHOTGN", auto=true },
    [4] = { name="CHAINGUN", ammo="bul", cost=1, fireS=8*W.TIC, spr="CHGG", fire="A", flash="CHGF",
        dmg=function() return 5*(W.pRandom()%3+1) end, pellets=1, accurate=true, range=2048, sfx="DSPISTOL", auto=true },
    [5] = { name="ROCKET", ammo="rck", cost=1, fireS=20*W.TIC, spr="MISG", fire="B", flash="MISF", proj="ROCKET", sfx="DSRLAUNC", auto=true },
    [6] = { name="PLASMA", ammo="cel", cost=1, fireS=3*W.TIC, spr="PLSG", fire="A", flash="PLSF", proj="PLASMA", sfx="DSPLASMA", auto=true },
    [7] = { name="BFG9000", ammo="cel", cost=40, fireS=40*W.TIC, spr="BFGG", fire="B", flash="BFGF", proj="BFG", sfx="DSBFG", auto=false },
    [8] = { name="CHAINSAW", ammo=nil, cost=0, fireS=8*W.TIC, spr="SAWG", fire="C", melee=true, range=65,
        dmg=function() return (W.pRandom()%10+1)*2 end, sfx="DSSAWHIT", auto=true },
    [9] = { name="SSG", ammo="shl", cost=2, fireS=57*W.TIC, spr="SHT2", fire="A", flash="SHT2", pellets=20, range=2048, wide=true,
        dmg=function() return 5*(W.pRandom()%3+1) end, sfx="DSDSHTGN", auto=true },
}

-- Synthetic THING_SPR ids (never in a WAD) for pooled fx + projectiles: r=nil so
-- they never block movement; drawn via the normal sprite path (with th.spr/th.frame).
W.THING_SPR[30030] = { spr="PUFF", seq="A", rot=false, kind="fx" }
W.THING_SPR[30031] = { spr="BLUD", seq="A", rot=false, kind="fx" }
W.THING_SPR[30032] = { spr="BEXP", seq="A", rot=false, kind="fx" }
W.THING_SPR[30040] = { spr="MISL", seq="A", rot=false, kind="fx" }   -- projectile (th.spr overrides prefix)

-- Missiles (info.c mobjinfo). speed = units/SECOND (Doom fracunit/tic * 35). dmg =
-- direct-hit roll (P_Random%8+1)*info.damage; splash = A_Explode radius+dmg (rockets/
-- BFG only, 0 for fireballs/plasma). flySpr/fly = in-flight sprite + anim frames;
-- boomSpr/boom = explosion sprite + frames. Player and monster share this table.
W.PROJ = {
    ROCKET      = { flySpr="MISL", fly="A",  boomSpr="MISL", boom="BCD",   speed=660, splash=128, boomsfx="DSBAREXP",
        dmg=function() return (W.pRandom()%8+1)*20 end },
    PLASMA      = { flySpr="PLSS", fly="AB", boomSpr="PLSE", boom="ABCDE", speed=875, splash=0,   boomsfx="DSFIRXPL",
        dmg=function() return (W.pRandom()%8+1)*5 end },
    BFG         = { flySpr="BFS1", fly="AB", boomSpr="BFE1", boom="ABCDEF",speed=875, splash=280, boomsfx="DSRXPLOD", spray=true,
        dmg=function() return (W.pRandom()%8+1)*100 end },
    TROOPSHOT   = { flySpr="BAL1", fly="AB", boomSpr="BAL1", boom="CDE",   speed=350, splash=0,   boomsfx="DSFIRXPL",
        dmg=function() return (W.pRandom()%8+1)*3 end },
    HEADSHOT    = { flySpr="BAL2", fly="AB", boomSpr="BAL2", boom="CDE",   speed=350, splash=0,   boomsfx="DSFIRXPL",
        dmg=function() return (W.pRandom()%8+1)*5 end },
    BRUISERSHOT = { flySpr="BAL7", fly="AB", boomSpr="BAL7", boom="CDE",   speed=525, splash=0,   boomsfx="DSFIRXPL",
        dmg=function() return (W.pRandom()%8+1)*8 end },
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
    -- shade: sector light x distance, same curve as planes
    local br = W.planeLight(sec and sec.light or 160, depth)
    local tint = W.greyTint(br)
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

-- H.6: collect visible/in-range things, depth-sort far->near, draw the nearest
-- SPRITE_MAX under the per-frame SPRITE_BUDGET. Scratch is reused (no per-frame
-- alloc for the collect list; the sort view is small and bounded).
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
    for i = startI, n do
        if W.spriteDraws >= W.SPRITE_BUDGET then break end
        W.drawThing(view[i].th, view[i].e, view[i].depth)
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
    W.fallVel = 0                           -- vertical velocity for gravity/falling
    W.viewZ = W.floorZAt(W.viewX, W.viewY) + W.EYE
    W.activeSectors = {}                    -- in-progress door/sector movements
    if W.health == nil then W.newGame() end -- first level of a fresh game
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
    local feet = W.viewZ - W.EYE
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
    if not sec then return W.viewZ - W.EYE end        -- off-map: keep current height
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

-- One collision-resolved step: full diagonal first (so you can walk out of a
-- concave corner where both single axes are blocked), else axis-separated slide.
function W.moveStep(dx, dy)
    if not W.blocked(W.viewX + dx, W.viewY + dy) then
        W.viewX = W.viewX + dx; W.viewY = W.viewY + dy; return
    end
    if not W.blocked(W.viewX + dx, W.viewY) then W.viewX = W.viewX + dx end
    if not W.blocked(W.viewX, W.viewY + dy) then W.viewY = W.viewY + dy end
end

-- Substep the frame's movement so a fast move (at low fps) cannot tunnel a wall.
function W.tryMove(dx, dy)
    local n = ceil(sqrt(dx * dx + dy * dy) / 8)      -- <= 8 units per collision step
    if n < 1 then n = 1 end
    local sx, sy = dx / n, dy / n
    for _ = 1, n do W.moveStep(sx, sy) end
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
-- Use-activated (manual) door line specials -> {stay=open-and-hold, blaze=fast}.
-- key is the required keycard; not enforced yet (no inventory), doors open anyway.
W.DOOR_SPECIALS = {
    [1]   = {},                              -- DR door: open, wait, auto-close
    [26]  = { key = "blue" },                -- DR, blue-locked
    [27]  = { key = "yellow" },
    [28]  = { key = "red" },
    [31]  = { stay = true },                 -- D1 door: open and stay
    [32]  = { stay = true, key = "blue" },
    [33]  = { stay = true, key = "red" },
    [34]  = { stay = true, key = "yellow" },
    [117] = { blaze = true },                -- DR blazing
    [118] = { stay = true, blaze = true },   -- D1 blazing
}

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

-- Lowest ceiling among sectors sharing a two-sided line with sector index si.
-- This is the height a Doom door opens to (minus 4). nil if si has no neighbor.
function W.lowestNeighborCeiling(si)
    local LD, SD, SE = W.map.linedefs, W.map.sidedefs, W.map.sectors
    local lo
    for _, ld in ipairs(LD) do
        if ld.front ~= NONE and ld.back ~= NONE then
            local fsd = SD[ld.front + 1]; local bsd = SD[ld.back + 1]
            local other
            if fsd and fsd.sector == si then other = bsd
            elseif bsd and bsd.sector == si then other = fsd end
            if other then
                local osec = SE[other.sector + 1]
                if osec and (not lo or osec.ceil < lo) then lo = osec.ceil end
            end
        end
    end
    return lo
end

function W.playerInSector(si)
    local sec = W.map.sectors[si + 1]
    return sec ~= nil and W.sectorAt(W.viewX, W.viewY) == sec
end

-- Start (or retrigger) a manual door on the back sector of the used line.
function W.activateDoor(ld, meta)
    if ld.back == NONE then return end
    local bsd = W.map.sidedefs[ld.back + 1]; if not bsd then return end
    local si = bsd.sector
    local sec = W.map.sectors[si + 1]; if not sec then return end
    local m = W.activeSectors[si]
    if m and m.kind == "door" then                    -- already moving: DR toggles
        if m.phase == "closing" then m.phase = "opening"
        elseif (m.phase == "opening" or m.phase == "wait") and not m.stay then m.phase = "closing" end
        return
    end
    local top = (W.lowestNeighborCeiling(si) or sec.ceil) - 4
    if top < sec.floor then top = sec.floor end
    W.activeSectors[si] = { kind = "door", sec = sec, si = si, phase = "opening",
        openTop = top, speed = (meta.blaze and 260) or 100, stay = meta.stay or false }
end

function W.exitLevel()
    W.finishLevel()                         -- keep gear across the level, drop keys/powers
    local cur = W.map and W.map.name
    local list = W.mapList or {}
    local nxt
    for i, m in ipairs(list) do if m == cur then nxt = list[i + 1]; break end end
    if nxt then W.startMap(nxt)
    else
        W.menu.fromPlay = false; W.menu.screen = "main"; W.menu.cursor = 1
        W.gameState = "frontend"; W.status = "level complete"
    end
end

-- Dispatch a linedef special hit by the use ray.
function W.useSpecial(ld)
    local sp = ld.special
    local door = W.DOOR_SPECIALS[sp]
    if door then
        if door.key and not (W.keys and W.keys[door.key]) then
            W.hudMsg = "You need a " .. door.key .. " key."
            W.hudMsgUntil = now() + 2.0
            return
        end
        W.activateDoor(ld, door); return
    end
    if sp == 11 or sp == 51 then W.exitLevel() end    -- S1 exit switch (normal / secret)
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
                if ld.special and ld.special ~= 0 then
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

-- Advance every in-progress sector movement. Doors open, hold ~4s, then close;
-- a door will not shut while the player stands in it (reverses to open instead).
function W.updateSectors(dt)
    if not W.activeSectors then return end
    for si, m in pairs(W.activeSectors) do
        local sec = m.sec
        if m.phase == "opening" then
            sec.ceil = sec.ceil + m.speed * dt
            if sec.ceil >= m.openTop then
                sec.ceil = m.openTop
                if m.stay then W.activeSectors[si] = nil
                else m.phase = "wait"; m.waitAt = now() + 4.0 end
            end
        elseif m.phase == "wait" then
            if now() >= m.waitAt then m.phase = "closing" end
        elseif m.phase == "closing" then
            if W.playerInSector(si) then m.phase = "opening"    -- never crush the player
            else
                sec.ceil = sec.ceil - m.speed * dt
                if sec.ceil <= sec.floor then sec.ceil = sec.floor; W.activeSectors[si] = nil end
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
    W.powers = {}
    W.damageCount = 0
    W.playerDead = false
    W.hudMsg = nil; W.hudMsgUntil = 0; W.bonusFlash = 0
    W.psp = { state = "ready", sx = 0, sy = 0, flash = 0, refire = 0, bobT = 0 }
    W.weaponClock = 0; W.rndIdx = 0
end

function W.finishLevel()                    -- between levels: keep gear, drop keys/powers
    W.keys = { blue = false, yellow = false, red = false }
    W.keyForm = {}
    W.powers = {}
    W.bonusFlash = 0; W.hudMsg = nil
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
        if p.heal then W.health = max(W.health, p.heal) end
        W.powers[p.pw] = true; return true
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
                W.bonusFlash = now() + 0.2
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
    for _, s in ipairs(list) do
        if W.weaponOwned[s] then W.pendingWeapon = s; return end   -- raise via psprite swap
    end
end

-- Build the live-actor and pickup indices from the map THINGS (called per level).
-- Monsters/barrels get a .think tag + hp/z and enter W.thinkers (ticked once AI
-- lands); pickups get .pk and enter W.pickupThings; decor gets nothing. In place,
-- so renderThings/blocked keep reading the same table.
function W.spawnActors(map)
    W.thinkers = {}
    W.pickupThings = {}
    W.projPool = {}
    W.freeThingSlots = {}
    -- Skill filter (P_SpawnMapThing): a thing spawns only if it is not multiplayer-
    -- only AND carries this skill's flag bit. Filtered things are marked removed so
    -- the renderer/collision/pickups all skip them (no frozen ghost monsters). This
    -- is why default (Hurt Me Plenty) has far fewer monsters than "spawn everything".
    local bit = W.skillBit()
    for _, th in ipairs(map.things) do
        local e = W.THING_SPR[th.dtype]
        if e then                                            -- only renderable/interactive things
            if (th.flags & 0x0010) == 0 and (th.flags & bit) ~= 0 then
                th.removed = false
                if e.kind == "monster" then
                    th.think = "monster"
                    th.info = W.MOBJINFO and W.MOBJINFO[e.spr] or nil
                    th.hp = (th.info and th.info.hp) or W.MONHP[e.spr] or 60
                    th.st = "idle"; th.frame = e.seq:sub(1, 1)
                    th.z = W.floorZFor(e.r or 20, th.x, th.y)
                    th.sx, th.sy = th.x, th.y; th.dead = false
                    th.movedir = 8; th.movecount = 0; th.atkCool = 0
                    th.target = nil; th.atkKind = nil; th.fired = false
                    th.lookTimer = (W.pRandom() % 16) * 0.03   -- stagger first LOS check
                    W.thinkers[#W.thinkers + 1] = th
                elseif e.spr == "BAR1" then
                    th.think = "barrel"; th.hp = 20
                    th.frame = e.seq:sub(1, 1)
                    th.z = W.floorZFor(10, th.x, th.y); th.dead = false
                    W.thinkers[#W.thinkers + 1] = th
                elseif W.PICKUP[th.dtype] then
                    th.pk = W.PICKUP[th.dtype]
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
-- Spawn a short-lived cosmetic actor (puff/blood/explosion) via the appended-thing
-- pool so it draws + occludes like any billboard. Recycled through W.freeThingSlots.
function W.spawnFx(dtype, seq, x, y, z, dur)
    local idx = (#W.freeThingSlots > 0) and table.remove(W.freeThingSlots) or (#W.map.things + 1)
    local th = W.map.things[idx]
    if not th then th = {}; W.map.things[idx] = th end
    th.dtype = dtype; th.x = x; th.y = y; th.z = z; th.angle = 0; th.flags = 0
    th.think = "fx"; th.seq = seq; th.frameIdx = 1; th.frame = seq:sub(1, 1)
    th.frdur = dur / #seq; th.stime = th.frdur
    th.removed = false; th.dead = false; th.pk = nil; th.spr = nil; th._slot = idx
    W.thinkers[#W.thinkers + 1] = th
end

-- P_SpawnMissile: launch a projectile from (x,y,z) at horizontal angle ang with the
-- given vertical velocity momz. owner ("player" or the firing monster th) is never
-- hit by its own missile. Uses the same appended-thing pool as spawnFx; th.spr
-- drives the flight sprite so drawThing renders it with no THING_SPR change.
function W.spawnProjectile(kind, x, y, z, ang, momz, owner)
    local p = W.PROJ[kind]; if not p then return end
    local idx = (#W.freeThingSlots > 0) and table.remove(W.freeThingSlots) or (#W.map.things + 1)
    local th = W.map.things[idx]
    if not th then th = {}; W.map.things[idx] = th end
    th.dtype = 30040; th.x = x; th.y = y; th.z = z; th.angle = 0; th.flags = 0
    th.think = "proj"; th.st = "fly"; th.proj = p; th.owner = owner
    th.srcTag = (owner == "player") and "player" or nil
    th.spr = p.flySpr; th.flyseq = p.fly; th.frameIdx = 1; th.frame = p.fly:sub(1, 1)
    th.frdur = 4 * W.TIC; th.stime = th.frdur
    th.momx = cos(ang) * p.speed; th.momy = sin(ang) * p.speed; th.momz = momz or 0
    th.life = 4.0
    th.removed = false; th.dead = false; th.pk = nil; th._slot = idx
    W.thinkers[#W.thinkers + 1] = th
end

-- P_ExplodeMissile: stop, switch to the explosion sprite/anim, apply the direct hit
-- (P_Random%8+1 damage roll) and any A_Explode splash, then die when the anim ends.
function W.projExplode(th, hit)
    local p = th.proj
    th.st = "boom"; th.momx = 0; th.momy = 0; th.momz = 0; th.flyseq = nil
    th.spr = p.boomSpr; th.seq = p.boom; th.frameIdx = 1; th.frame = p.boom:sub(1, 1)
    th.frdur = 4 * W.TIC; th.stime = th.frdur
    if p.boomsfx then pcall(W.playSfx, p.boomsfx) end
    local dmg = (p.dmg and p.dmg()) or 10
    if hit == "player" then W.hurtPlayer(dmg)
    elseif hit then W.damageMobj(hit, dmg, th.srcTag) end
    if (p.splash or 0) > 0 then W.radiusDamage(th.x, th.y, p.splash, p.splash, th.owner) end
end

-- Missile per-tick: animate, then substep (<=16u) the move testing wall / thing /
-- player / floor-ceiling; explode on the first hit. Horizontal thing test mirrors
-- shootTrace (no z gate); floor/ceiling detonate ground shots. Expires after life.
function W.projThink(th, dt)
    if th.st == "boom" then
        th.stime = th.stime - dt
        if th.stime <= 0 then
            th.frameIdx = th.frameIdx + 1
            if th.frameIdx > #th.seq then th.removed = true
            else th.frame = th.seq:sub(th.frameIdx, th.frameIdx); th.stime = th.frdur end
        end
        return
    end
    th.stime = th.stime - dt
    if th.stime <= 0 then
        th.frameIdx = (th.frameIdx % #th.flyseq) + 1
        th.frame = th.flyseq:sub(th.frameIdx, th.frameIdx); th.stime = th.frdur
    end
    th.life = th.life - dt
    if th.life <= 0 then th.removed = true; return end
    local mx, my, mz = th.momx, th.momy, th.momz
    local hspeed = sqrt(mx * mx + my * my); if hspeed < 1 then hspeed = 1 end
    local steps = ceil(hspeed * dt / 16); if steps < 1 then steps = 1 end
    local sdt = dt / steps
    local things = W.map.things
    for _ = 1, steps do
        local ox, oy, oz = th.x, th.y, th.z
        local segdx, segdy = mx * sdt, my * sdt
        local seglen = sqrt(segdx * segdx + segdy * segdy); if seglen < 1e-4 then seglen = 1e-4 end
        local ndx, ndy = segdx / seglen, segdy / seglen
        local wd = W.rayWallDist(ox, oy, ndx, ndy, seglen, oz)
        local hitThing, hitAlong = nil, min(seglen, wd)
        for _, o in ipairs(things) do
            local oe = W.THING_SPR[o.dtype]
            if oe and oe.r and o ~= th.owner and not o.dead and not o.removed and (o.flags & 0x0010) == 0 then
                local rx, ry = o.x - ox, o.y - oy
                local along = rx * ndx + ry * ndy
                if along > 0 and along < hitAlong then
                    local perp = abs(rx * (-ndy) + ry * ndx)
                    -- z-gate so an arcing shot does not clip a thing it flies over/under
                    -- (full-height decor has no o.z, so it always blocks).
                    local oz2 = o.z
                    if perp <= oe.r and (not oz2 or (oz >= oz2 - 16 and oz <= oz2 + 72)) then
                        hitThing = o; hitAlong = along
                    end
                end
            end
        end
        if th.owner ~= "player" then                     -- only monster missiles hit the player
            local rx, ry = W.viewX - ox, W.viewY - oy
            local along = rx * ndx + ry * ndy
            local pz0 = W.viewZ - W.EYE
            if along > 0 and along < hitAlong and oz >= pz0 - 8 and oz <= pz0 + W.PHEIGHT then
                local perp = abs(rx * (-ndy) + ry * ndx)
                if perp <= W.RADIUS then hitThing = "player"; hitAlong = along end
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
            W.projExplode(th, nil); return
        end
        th.x = ox + segdx; th.y = oy + segdy; th.z = oz + mz * sdt
        local sec = W.sectorAt(th.x, th.y)
        if sec and (th.z <= sec.floor or th.z >= sec.ceil) then W.projExplode(th, nil); return end
    end
end

-- Enter a monster state: pick the frame string + per-frame duration for it.
function W.setState(th, st)
    th.st = st; th.frameIdx = 1; th.fired = false
    local inf = th.info; local seq
    if inf and inf.frames then
        if st == "pain" then seq = inf.frames.pain
        elseif st == "death" then seq = inf.frames.death
        elseif st == "xdeath" then seq = inf.frames.xdeath or inf.frames.death
        elseif st == "atk" then seq = inf.frames.atk
        else seq = inf.frames.walk end
    end
    th.seq = seq or "A"
    th.frame = th.seq:sub(1, 1)
    th.frdur = (st == "pain") and (6 * W.TIC)
        or (st == "death" or st == "xdeath") and (8 * W.TIC)
        or (st == "atk") and (8 * W.TIC) or (4 * W.TIC)
    th.stime = th.frdur
end

-- Straight-line distance from a monster to the player.
function W.distToPlayer(th)
    local dx, dy = W.viewX - th.x, W.viewY - th.y
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

-- Can this monster see the player? 3D sight from the monster's eye to the player's
-- full body box, gated by SIGHT_RANGE. Replaces the old flat-Z ray so a monster
-- cannot shoot the player over/under geometry that occludes it on screen.
function W.monsterSees(th)
    local dx, dy = W.viewX - th.x, W.viewY - th.y
    if dx * dx + dy * dy > W.SIGHT_RANGE * W.SIGHT_RANGE then return false end
    local z1 = (th.z or 0) + (th.info and th.info.eye or 42)
    local pbot = W.viewZ - W.EYE
    return W.checkSight(th.x, th.y, z1, W.viewX, W.viewY, pbot, pbot + W.PHEIGHT)
end

-- A_FaceTarget: aim the monster's sprite rotation at the player (WAD degrees).
function W.faceTarget(th)
    th.angle = atan(W.viewY - th.y, W.viewX - th.x) * (180 / pi)
end

-- P_CheckMeleeRange: player within claw/bite reach and in sight. Doom measures
-- center-to-center: dist < MELEERANGE(64) - 20 + player radius.
function W.monsterInMelee(th)
    local inf = th.info; if not inf then return false end
    local reach = (inf.mrange or 64) - 20 + W.RADIUS
    return W.distToPlayer(th) <= reach and W.monsterSees(th)
end

-- Wake an idle monster: switch to chase, seed its move state, play the sight cry.
function W.wakeMonster(th)
    th.target = "player"
    if th.st == "idle" then
        W.setState(th, "chase")
        th.movedir = 8; th.movecount = 0; th.atkCool = 0
        if th.info and th.info.sight then pcall(W.playSfx, th.info.sight) end
    end
end

-- Generalized P_CheckPosition for a monster's bounding box at (nx,ny). Returns
-- (blocked, tmfloor, tmdropoff): blocked if the box crosses a one-sided/blocking/
-- block-monsters line, the vertical opening is too short, the step up exceeds
-- MAXSTEP, it would stand over a dropoff > MAXSTEP (non-floaters only), or it
-- overlaps another solid thing or the player. Floaters skip the height/step/
-- dropoff gates (they fly). tmfloor = highest floor the box overlaps.
function W.monBlocked(th, nx, ny)
    local se = W.THING_SPR[th.dtype]
    local R = (se and se.r) or 20
    local bl, br, bb, bt = nx - R, nx + R, ny - R, ny + R
    local sec = W.sectorAt(nx, ny)
    if not sec then return true end
    local tmfloor, tmceil, tmdrop = sec.floor, sec.ceil, sec.floor
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
            end
        end
    end
    local feet = th.z or tmfloor
    if not (th.info and th.info.float) then
        if tmceil - tmfloor < W.MON_HEIGHT then return true end   -- opening too short
        if tmfloor - feet > W.MAXSTEP then return true end        -- step up too high
        if tmfloor - tmdrop > W.MAXSTEP then return true end      -- avoid ledges
    end
    for _, o in ipairs(W.map.things) do
        if o ~= th then
            local oe = W.THING_SPR[o.dtype]
            if oe and oe.r and (o.flags & 0x0010) == 0 and not o.dead and not o.removed then
                local rr = R + oe.r
                if abs(nx - o.x) < rr and abs(ny - o.y) < rr then return true end
            end
        end
    end
    local pr = R + W.RADIUS
    if abs(nx - W.viewX) < pr and abs(ny - W.viewY) < pr then return true end
    return false, tmfloor, tmdrop
end

-- Can the monster take a probe step in direction dir (0..7)? Lookahead is ~one
-- Doom move-tic, floored so wall detection still works at tiny per-frame dt.
function W.canWalk(th, dir)
    local probe = (th.info and th.info.speed or 100) * 0.12
    if probe < 16 then probe = 16 end
    local nx = th.x + W.DIRX[dir + 1] * probe
    local ny = th.y + W.DIRY[dir + 1] * probe
    return not W.monBlocked(th, nx, ny)
end

function W.setMoveCount(th)
    th.movecount = 0.25 + (W.pRandom() % 16) * 0.03      -- commit to a heading ~0.25..0.7s
end

-- P_NewChaseDir: choose an 8-way heading toward the player, trying the direct
-- diagonal, then each axis (larger-delta first), then the old heading, then a
-- randomized full search, then the turnaround. Sets movedir (8 = boxed in).
function W.newChaseDir(th)
    local olddir = th.movedir or 8
    local turn = W.OPPOSITE[olddir]
    local dxp, dyp = W.viewX - th.x, W.viewY - th.y
    local d1, d2 = 8, 8
    if dxp > 10 then d1 = 0 elseif dxp < -10 then d1 = 4 end          -- EAST / WEST
    if dyp < -10 then d2 = 6 elseif dyp > 10 then d2 = 2 end          -- SOUTH / NORTH
    if d1 ~= 8 and d2 ~= 8 then
        local idx = ((dyp < 0) and 2 or 0) + ((dxp > 0) and 1 or 0)
        local diag = W.DIAGS[idx + 1]
        th.movedir = diag
        if diag ~= turn and W.canWalk(th, diag) then W.setMoveCount(th); return end
    end
    if W.pRandom() > 200 or abs(dyp) > abs(dxp) then d1, d2 = d2, d1 end
    if d1 == turn then d1 = 8 end
    if d2 == turn then d2 = 8 end
    if d1 ~= 8 then th.movedir = d1; if W.canWalk(th, d1) then W.setMoveCount(th); return end end
    if d2 ~= 8 then th.movedir = d2; if W.canWalk(th, d2) then W.setMoveCount(th); return end end
    if olddir ~= 8 then th.movedir = olddir; if W.canWalk(th, olddir) then W.setMoveCount(th); return end end
    if (W.pRandom() & 1) ~= 0 then
        for t = 0, 7 do
            if t ~= turn then th.movedir = t; if W.canWalk(th, t) then W.setMoveCount(th); return end end
        end
    else
        for t = 7, 0, -1 do
            if t ~= turn then th.movedir = t; if W.canWalk(th, t) then W.setMoveCount(th); return end end
        end
    end
    if turn ~= 8 then th.movedir = turn; if W.canWalk(th, turn) then W.setMoveCount(th); return end end
    th.movedir = 8      -- DI_NODIR: boxed in, stand and keep trying
end

-- P_Move (continuous): step speed*dt along movedir; re-pick on timeout or a block.
-- Floaters glide their feet toward the player's; walkers snap to the floor they land on.
function W.monMove(th, dt)
    local inf = th.info
    th.movecount = (th.movecount or 0) - dt
    if th.movedir == nil or th.movedir >= 8 or th.movecount <= 0 then W.newChaseDir(th) end
    if th.movedir >= 8 then return end
    th.angle = W.DIRDEG[th.movedir + 1]
    local sp = (inf.speed or 100) * dt
    local nx = th.x + W.DIRX[th.movedir + 1] * sp
    local ny = th.y + W.DIRY[th.movedir + 1] * sp
    local blk, fz = W.monBlocked(th, nx, ny)
    if not blk then
        th.x = nx; th.y = ny
        if inf.float then
            local tz = W.viewZ - W.EYE
            local dz = tz - th.z
            if dz > sp then dz = sp elseif dz < -sp then dz = -sp end
            th.z = th.z + dz
        elseif fz then
            th.z = fz
        end
    else
        th.movecount = 0        -- blocked: re-pick a heading next tick
    end
end

-- One hitscan/melee resolution at the attack's fire frame (A_PosAttack /
-- A_SPosAttack / A_SargAttack / A_TroopAttack close). Missile species with no
-- projectile yet (chunk 4) only reach here via their melee branch.
--
-- Hitscan is NOT auto-hit: like A_PosAttack, each bullet takes an angular spread
-- of (P_Random-P_Random)<<20 radians. It only connects if that spread stays inside
-- the half-angle the player's body subtends at this range (atan(RADIUS/dist)), so
-- shots reliably land point-blank but mostly miss at distance. Melee never misses
-- if still in reach (matches A_SargAttack/A_TroopAttack). Vertical aim is auto.
function W.doMonAttack(th)
    local inf = th.info; if not inf then return end
    if th.atkKind == "melee" then
        if inf.msfx then pcall(W.playSfx, inf.msfx) end
        if W.monsterInMelee(th) then W.hurtPlayer((inf.melee and inf.melee()) or 5) end
    elseif th.atkKind == "missile" then
        if inf.asfx then pcall(W.playSfx, inf.asfx) end
        if inf.proj and W.monsterSees(th) then          -- A_TroopAttack/A_HeadAttack/A_BruisAttack (ranged)
            local se = W.THING_SPR[th.dtype]
            local ang = atan(W.viewY - th.y, W.viewX - th.x)
            local sz = (th.z or 0) + (inf.eye or 42)
            local sx = th.x + cos(ang) * ((se and se.r or 20) + 8)
            local sy = th.y + sin(ang) * ((se and se.r or 20) + 8)
            local tz = W.viewZ - 8                       -- aim at player torso
            local dist = W.distToPlayer(th); if dist < 1 then dist = 1 end
            local momz = (tz - sz) * (W.PROJ[inf.proj].speed) / dist
            W.spawnProjectile(inf.proj, sx, sy, sz, ang, momz, th)
        end
    else
        if inf.asfx then pcall(W.playSfx, inf.asfx) end
        if W.monsterSees(th) then
            local dist = W.distToPlayer(th); if dist < 1 then dist = 1 end
            local half = atan(W.RADIUS, dist)                 -- player half-width at this range
            for _ = 1, (inf.shots or 1) do
                local spread = (W.pRandom() - W.pRandom()) * (pi / 2048)   -- A_PosAttack <<20
                if abs(spread) <= half then W.hurtPlayer((inf.dmg and inf.dmg()) or 3) end
            end
        end
    end
end

-- Decide whether to launch an attack this evaluation. Melee if in reach; hitscan and
-- missile species fire at range with a per-tic probability (missile species still
-- prefer the melee branch above when the player is adjacent).
function W.tryMonAttack(th)
    local inf = th.info; if not inf then return false end
    if not W.monsterSees(th) then return false end
    if inf.melee and W.monsterInMelee(th) then
        W.setState(th, "atk"); th.atkKind = "melee"; return true
    end
    if inf.atk == "hitscan" and (W.pRandom() % 255) < 40 then
        W.setState(th, "atk"); th.atkKind = "hitscan"; return true
    end
    if inf.atk == "missile" and inf.proj and (W.pRandom() % 255) < 40 then
        W.setState(th, "atk"); th.atkKind = "missile"; return true
    end
    return false
end

-- Advance an in-progress attack animation; land the hit on the fire frame, then
-- return to chase with a short cooldown.
function W.monAttackState(th, dt)
    th.stime = th.stime - dt
    if th.stime > 0 then return end
    local inf = th.info
    th.frameIdx = th.frameIdx + 1
    if th.frameIdx > #th.seq then
        W.setState(th, "chase")
        th.atkCool = 0.4 + (W.pRandom() % 16) * 0.03
        return
    end
    th.frame = th.seq:sub(th.frameIdx, th.frameIdx)
    th.stime = th.frdur
    if not th.fired and th.frameIdx >= ((inf and inf.frames and inf.frames.fireAt) or 99) then
        th.fired = true
        W.faceTarget(th)
        W.doMonAttack(th)
    end
end

function W.monsterThink(th, dt)
    local st = th.st
    if st == "pain" then
        th.stime = th.stime - dt
        if th.stime <= 0 then W.setState(th, "chase") end      -- resume the hunt
        return
    elseif st == "death" or st == "xdeath" then
        th.stime = th.stime - dt
        if th.stime <= 0 then
            th.frameIdx = th.frameIdx + 1
            if th.frameIdx > #th.seq then th.think = nil        -- corpse: stop ticking, stays drawn
            else th.frame = th.seq:sub(th.frameIdx, th.frameIdx); th.stime = th.frdur end
        end
        return
    elseif st == "atk" then
        W.monAttackState(th, dt)
        return
    end
    local inf = th.info; if not inf then return end
    if st == "idle" then
        th.lookTimer = (th.lookTimer or 0) - dt               -- A_Look, throttled
        if th.lookTimer <= 0 then
            th.lookTimer = 0.2 + (W.pRandom() % 8) * 0.02
            if W.monsterSees(th) then W.wakeMonster(th) end
        end
        return
    end
    -- CHASE: face + animate walk frames, evaluate attacks, then move.
    if not th.target then th.target = "player" end
    th.stime = th.stime - dt
    if th.stime <= 0 then
        th.frameIdx = (th.frameIdx % #th.seq) + 1
        th.frame = th.seq:sub(th.frameIdx, th.frameIdx)
        th.stime = th.frdur
    end
    th.atkCool = (th.atkCool or 0) - dt
    if th.atkCool <= 0 then
        th.atkCool = 0.12 + (W.pRandom() % 8) * 0.02          -- re-evaluate ~7x/sec
        if W.tryMonAttack(th) then return end
    end
    W.monMove(th, dt)
end

function W.barrelThink(th, dt)
    -- barrels do nothing until destroyed; explosion is handled in W.explodeBarrel
end

function W.fxThink(th, dt)
    th.stime = th.stime - dt
    if th.stime <= 0 then
        th.frameIdx = th.frameIdx + 1
        if th.frameIdx > #th.seq then th.removed = true
        else th.frame = th.seq:sub(th.frameIdx, th.frameIdx); th.stime = th.frdur end
    end
end

W.THINK = { monster = W.monsterThink, barrel = W.barrelThink, fx = W.fxThink, proj = W.projThink }

-- Advance every live thing; swap-remove finished ones (recycle fx/proj slots).
function W.updateActors(dt)
    local list = W.thinkers; if not list then return end
    for i = #list, 1, -1 do
        local th = list[i]
        if th.removed or not th.think then
            list[i] = list[#list]; list[#list] = nil
            if th.removed and th._slot then W.freeThingSlots[#W.freeThingSlots + 1] = th._slot end
        else
            local fn = W.THINK[th.think]; if fn then fn(th, dt) end
        end
    end
end

-- DOOM (P_Random - P_Random) << 18 BAM spread converted to radians (~ +-5.6 deg).
function W.hAngle() return (W.pRandom() - W.pRandom()) * (pi / 8192) end

-- Nearest bullet-stopping distance along a ray (blockmap-free). A one-sided line
-- always stops; a two-sided line stops only if shootZ is outside its opening (so
-- shots pass through open doorways/windows at eye height, stop at closed doors).
function W.rayWallDist(x1, y1, dx, dy, range, shootZ)
    local x2, y2 = x1 + dx * range, y1 + dy * range
    local V, LD, SD, SE = W.map.vertexes, W.map.linedefs, W.map.sidedefs, W.map.sectors
    local best = range
    for _, ld in ipairs(LD) do
        local a = V[ld.v1 + 1]; local b = V[ld.v2 + 1]
        if a and b then
            local t, u = W.raySeg(x1, y1, x2, y2, a.x, a.y, b.x, b.y)
            if t and t >= 0 and t <= 1 and u >= 0 and u <= 1 then
                local stops
                if ld.back == NONE or ld.front == NONE then stops = true
                else
                    local fsd = SD[ld.front + 1]; local bsd = SD[ld.back + 1]
                    local fsec = fsd and SE[fsd.sector + 1]; local bsec = bsd and SE[bsd.sector + 1]
                    if fsec and bsec then
                        local ot = min(fsec.ceil, bsec.ceil); local ob = max(fsec.floor, bsec.floor)
                        stops = (shootZ <= ob or shootZ >= ot)
                    else stops = true end
                end
                if stops then local d = t * range; if d < best then best = d end end
            end
        end
    end
    return best
end

-- One hitscan ray: stops at the nearest wall, hits the nearest actor before it.
function W.shootTrace(x1, y1, ang, range, dmg)
    local dx, dy = cos(ang), sin(ang)
    local wd = W.rayWallDist(x1, y1, dx, dy, range, W.viewZ)
    -- Vertical autoaim (P_AimLineAttack): the target search runs to the FULL range,
    -- not the flat-Z wall stop, and each candidate must have a clear SLOPED sight
    -- line from the eye to its torso. So a monster up (or down) a staircase gets hit
    -- even though a level ray would stop in a step riser. Horizontal aim = crosshair
    -- angle; vertical is resolved by sight, exactly like Doom's no-freelook autoaim.
    local best, bestAlong = nil, range
    for _, th in ipairs(W.map.things) do
        local e = W.THING_SPR[th.dtype]
        if e and e.r and not th.dead and not th.removed and (th.flags & 0x0010) == 0 then
            local rx, ry = th.x - x1, th.y - y1
            local along = rx * dx + ry * dy
            if along > 0 and along < bestAlong then
                local perp = abs(rx * (-dy) + ry * dx)
                if perp <= e.r then
                    local tz = (th.z or 0) + 24
                    if W.checkSight(x1, y1, W.viewZ, th.x, th.y, tz - 6, tz + 6) then
                        best = th; bestAlong = along
                    end
                end
            end
        end
    end
    if best then
        local tz = (best.z or 0) + 24
        W.spawnFx(30031, "ABC", x1 + dx * bestAlong, y1 + dy * bestAlong, tz, 0.18)
        W.damageMobj(best, dmg, "player")
    else
        W.spawnFx(30030, "ABCD", x1 + dx * wd, y1 + dy * wd, W.viewZ, 0.16)
    end
    return best
end

-- Autoaim slope for player PROJECTILES: nearest thing along the crosshair that has
-- a clear sloped sight line, returning dz/horizontal to its torso (0 if none). The
-- rocket/plasma/bfg ball is launched with momz = slope*speed so it arcs up or down
-- to whatever the crosshair covers, clearing intervening steps as its z rises.
function W.playerAimSlope(ang, range)
    local dx, dy = cos(ang), sin(ang)
    local bestAlong, slope = range, 0
    for _, th in ipairs(W.map.things) do
        local e = W.THING_SPR[th.dtype]
        if e and e.r and not th.dead and not th.removed and (th.flags & 0x0010) == 0 then
            local rx, ry = th.x - W.viewX, th.y - W.viewY
            local along = rx * dx + ry * dy
            if along > 0 and along < bestAlong then
                local perp = abs(rx * (-dy) + ry * dx)
                if perp <= e.r then
                    local tz = (th.z or 0) + 24
                    if W.checkSight(W.viewX, W.viewY, W.viewZ, th.x, th.y, tz - 6, tz + 6) then
                        bestAlong = along; slope = (tz - W.viewZ) / along
                    end
                end
            end
        end
    end
    return slope
end

-- P_DamageMobj: target is "player" or a thing. Player gets armor absorb + red flash.
function W.damageMobj(target, dmg, src)
    if target == "player" then
        if W.playerDead then return end
        if W.skill == 1 then dmg = floor(dmg / 2) end        -- sk_baby: player takes half damage
        local absorb = 0
        if W.armor > 0 and W.armorType > 0 then
            absorb = min(W.armor, floor(dmg * ((W.armorType == 1) and (1 / 3) or (1 / 2))))
            W.armor = W.armor - absorb
            if W.armor <= 0 then W.armorType = 0 end
        end
        local d = dmg - absorb
        W.health = W.health - d
        W.damageCount = min(100, (W.damageCount or 0) + d)
        if W.health <= 0 and not W.playerDead then
            W.health = 0; W.playerDead = true; W.deadTimer = now()
            pcall(W.playSfx, "DSPLDETH")
        end
        return
    end
    local th = target
    if th.dead or th.removed then return end
    th.hp = (th.hp or 0) - dmg
    if th.hp <= 0 then
        if th.think == "barrel" then W.explodeBarrel(th); return end
        th.dead = true
        local inf = th.info
        local gib = inf and inf.frames and inf.frames.xdeath and th.hp < -(inf.hp or 60)
        W.setState(th, gib and "xdeath" or "death")
        pcall(W.playSfx, (inf and inf.dsfx) or "DSPODTH1")
    elseif th.think == "monster" then                -- barrels take damage silently
        local inf = th.info
        if W.pRandom() < (inf and inf.pain or 128) and th.st ~= "pain" then
            W.setState(th, "pain")
            pcall(W.playSfx, (inf and inf.psfx) or "DSPOPAIN")
        end
        W.wakeMonster(th)                            -- retaliate: enter the hunt
    end
end

function W.hurtPlayer(dmg) W.damageMobj("player", dmg, nil) end

-- A_Explode: barrel vanishes into a BEXP burst and splash-damages everything near.
function W.explodeBarrel(th)
    th.dead = true; th.removed = true
    W.spawnFx(30032, "ABCDE", th.x, th.y, th.z or (W.viewZ - W.EYE), 0.5)
    pcall(W.playSfx, "DSBAREXP")
    W.radiusDamage(th.x, th.y, W.BARREL.boomdmg, W.BARREL.boomrad, th)
end

-- P_RadiusAttack: falloff = radius - (max(|dx|,|dy|) - target radius), LOS-gated.
function W.radiusDamage(x, y, dmg, rad, src)
    local function reach(tx, ty)
        local ddx, ddy = tx - x, ty - y; local dd = sqrt(ddx * ddx + ddy * ddy)
        if dd <= 1 then return true end
        return W.rayWallDist(x, y, ddx / dd, ddy / dd, dd, W.viewZ) >= dd - 1
    end
    for _, th in ipairs(W.map.things) do
        local e = W.THING_SPR[th.dtype]
        if e and e.r and not th.dead and not th.removed and (th.flags & 0x0010) == 0 and th ~= src then
            local dist = max(abs(th.x - x), abs(th.y - y)) - e.r
            if dist < 0 then dist = 0 end
            if dist < rad and reach(th.x, th.y) then W.damageMobj(th, rad - dist, src) end
        end
    end
    local pdist = max(abs(W.viewX - x), abs(W.viewY - y)) - W.RADIUS
    if pdist < 0 then pdist = 0 end
    if pdist < rad and reach(W.viewX, W.viewY) then W.hurtPlayer(rad - pdist) end
end

-- Best owned weapon that has ammo, DOOM downgrade order, for auto-switch on empty.
function W.bestWeapon()
    local order = { 6, 9, 4, 3, 2, 8, 1 }
    for _, s in ipairs(order) do
        local w = W.WEAPONS[s]
        if W.weaponOwned[s] and (not w.ammo or W.ammo[w.ammo] >= (w.cost or 1)) then return s end
    end
    return 1
end

-- Fire the current weapon once (hitscan / melee / projectile).
function W.fireWeapon()
    local w = W.WEAPONS[W.curWeapon]; if not w then return end
    W.psp.flash = 3 * W.TIC
    pcall(W.playSfx, w.sfx)
    if w.melee then
        W.shootTrace(W.viewX, W.viewY, W.viewAngle, w.range, w.dmg())
        return
    end
    if w.proj then                                   -- rocket / plasma / bfg
        local slope = W.playerAimSlope(W.viewAngle, 2048)   -- autoaim up/down stairs
        local px = W.viewX + cos(W.viewAngle) * (W.RADIUS + 8)
        local py = W.viewY + sin(W.viewAngle) * (W.RADIUS + 8)
        W.spawnProjectile(w.proj, px, py, W.viewZ - 8, W.viewAngle, slope * W.PROJ[w.proj].speed, "player")
        return
    end
    local pellets = w.pellets or 1
    for _ = 1, pellets do
        local ang = W.viewAngle
        local spread = (pellets > 1) or (w.accurate and W.psp.refire > 0) or (not w.accurate)
        if spread then ang = ang + W.hAngle() * (w.wide and 2 or 1) end
        W.shootTrace(W.viewX, W.viewY, ang, w.range, w.dmg())
    end
end

-- Fire scheduler + ammo + auto-switch (P_FireWeapon / A_ReFire / P_CheckAmmo).
function W.tryFire(dt)
    W.weaponClock = (W.weaponClock or 0) - dt
    if W.weaponClock > 0 then return end
    local w = W.WEAPONS[W.curWeapon]; if not w then return end
    local canFire = w.auto and W.fireHeld or (W.fireHeld and not W.firePrev)
    if not canFire then W.psp.refire = 0; return end
    if w.ammo then
        if W.ammo[w.ammo] < (w.cost or 1) then
            W.pendingWeapon = W.bestWeapon(); W.weaponClock = 0.2; W.psp.refire = 0; return
        end
        W.ammo[w.ammo] = W.ammo[w.ammo] - w.cost
    end
    W.fireWeapon()
    W.weaponClock = w.fireS
    W.psp.refire = (W.psp.refire or 0) + 1
end

-- Psprite state machine (dt-driven): lower/raise on switch, bob + fire when ready.
function W.updateWeapon(dt)
    local psp = W.psp
    if psp.flash > 0 then psp.flash = psp.flash - dt end
    if W.pendingWeapon and W.pendingWeapon ~= W.curWeapon and psp.state ~= "raise" then psp.state = "lower" end
    if psp.state == "lower" then
        psp.sy = (psp.sy or 0) + 900 * dt
        if psp.sy >= 128 then
            psp.sy = 128; W.curWeapon = W.pendingWeapon or W.curWeapon; W.pendingWeapon = nil
            psp.state = "raise"; W.weaponClock = 0; psp.refire = 0
        end
    elseif psp.state == "raise" then
        psp.sy = (psp.sy or 128) - 900 * dt
        if psp.sy <= 0 then psp.sy = 0; psp.state = "ready" end
    else
        psp.state = "ready"
        W.tryFire(dt)
        psp.bobT = (psp.bobT or 0) + dt
        local amp = min((W.playerSpeed or 0) * 0.02, 7)
        psp.sx = cos(psp.bobT * 8) * amp
        psp.sy = abs(sin(psp.bobT * 8)) * amp
    end
end

-- Draw the view weapon (psprite): centered, bobbing, with a muzzle flash overlay.
function W.drawWeapon(sw, viewH)
    local w = W.WEAPONS[W.curWeapon]; if not w then return end
    local psp = W.psp
    local firing = psp.flash > 0
    local frame = firing and (w.fire or "A") or "A"
    local lump = W.spriteFrameLump(w.spr, frame, 1)
    if not lump then return end
    local meta = W.spriteTex(lump); if not meta or not meta.tex then return end
    local S = W.viewW / 320                   -- DOOM psprite scale (view width / 320)
    local bx = (psp.sx or 0) * S; local by = (psp.sy or 0) * S
    local wpx, hpx = meta.w * S, meta.h * S
    local dx = W.centerX - wpx * 0.5 + bx      -- centered on the crosshair
    local dy = viewH - hpx + by
    local uw, vh = 0.5 / meta.w, 0.5 / meta.h  -- half-texel inset (no edge bleed line)
    ImGui.AddImage(meta.tex, dx, dy, dx + wpx, dy + hpx, uw, vh, 1 - uw, 1 - vh, 0xFFFFFFFF)
    if firing and w.flash then
        local fl = W.spriteFrameLump(w.flash, "A", 1)
        if fl then
            local fm = W.spriteTex(fl)
            if fm and fm.tex then
                -- keep the flash aligned to the gun's muzzle (its offset relative to the gun sprite)
                local fdx = dx + (meta.xoff - fm.xoff) * S
                local fdy = dy + (meta.yoff - fm.yoff) * S
                local fuw, fvh = 0.5 / fm.w, 0.5 / fm.h
                ImGui.AddImage(fm.tex, fdx, fdy, fdx + fm.w * S, fdy + fm.h * S, fuw, fvh, 1 - fuw, 1 - fvh, 0xFFFFFFFF)
            end
        end
    end
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

function W.update(dt, menuOpen)
    W.updateWipe(dt)                             -- advance the screen melt (over any state)
    -- World is frozen (no input, no move) while the menu is open or a wipe plays.
    if W.gameState == "play" and not menuOpen and not W.wipe.active then
        if W.playerDead then                 -- dead: frozen; USE/fire to restart the level
            local floorz = W.floorZAt(W.viewX, W.viewY)   -- Doom death cam: view sinks to the floor
            local target = floorz + 12
            if W.viewZ > target then W.viewZ = max(target, W.viewZ - 90 * dt) end
            if now() - (W.deadTimer or 0) > 1.0 and (kpressed(W.VK.E) or kpressed(W.VK.SPACE)) then
                W.newGame(); W.startMap(W.map and W.map.name)
            end
            return
        end
        -- fire input: held for auto weapons, rising edge for the BFG. Check LCTRL/
        -- RCTRL specifically (generic VK_CONTROL 0x11 is often not reported) + LMB.
        W.firePrev = W.fireHeld
        local md = false; local mok, mr = pcall(ImGui.IsMouseDown, 0); if mok then md = mr end
        W.fireHeld = kdown(0xA2) or kdown(0xA3) or kdown(W.VK.CTRL) or md
        -- turn: LEFT = CCW = +angle, RIGHT = -angle
        local turn = 0
        if kdown(W.VK.LEFT) then turn = turn + 1 end
        if kdown(W.VK.RIGHT) then turn = turn - 1 end
        W.viewAngle = W.viewAngle + turn * W.TURN * dt
        if W.mouseLook then
            -- Turn with GTA's raw mouse-look input (INPUT_LOOK_LR) rather than the
            -- cursor position: there is no cursor to warp, no screen-edge stall, and
            -- it reads 0 while the game window is unfocused, so alt-tabbing never
            -- steals the desktop mouse. Read the DISABLED control because
            -- W.suppressGameInput disables all game controls each frame.
            local ok, look = pcall(Natives.InvokeFloat, 0x11E65974A982637C, 0, 1)
            if ok and look then W.viewAngle = W.viewAngle - look * W.LOOKSENS end
        end
        W.viewAngle = angNorm(W.viewAngle)

        W.unstick()                          -- free the player if wedged from a fall/landing

        -- move: forward/back + strafe
        local mf, ms = 0, 0
        if kdown(W.VK.W) or kdown(W.VK.UP) then mf = mf + 1 end
        if kdown(W.VK.S) or kdown(W.VK.DOWN) then mf = mf - 1 end
        if kdown(W.VK.A) then ms = ms - 1 end
        if kdown(W.VK.DK) then ms = ms + 1 end
        local sp = W.MOVE * (kdown(W.VK.SHIFT) and W.RUN or 1) * dt
        local fx, fy = cos(W.viewAngle), sin(W.viewAngle)
        local rx, ry = sin(W.viewAngle), -cos(W.viewAngle)
        if mf ~= 0 or ms ~= 0 then
            W.tryMove((fx * mf + rx * ms) * sp, (fy * mf + ry * ms) * sp)
        end
        W.playerSpeed = (mf ~= 0 or ms ~= 0) and (W.MOVE * (kdown(W.VK.SHIFT) and W.RUN or 1)) or 0

        -- use: open a door / hit a switch on the line straight ahead. Scanned once
        -- per frame so the HUD can prompt when something usable is in reach.
        W.useHint = W.useLine()
        if W.useHint and (kpressed(W.VK.SPACE) or kpressed(W.VK.E)) then W.useSpecial(W.useHint) end
        W.updateSectors(dt)
        W.updateActors(dt)                   -- monster pain/death anim, barrels, fx

        -- floor follow with gravity. Stand on the highest floor the body overlaps
        -- (W.floorZAt = DOOM tmfloorz), NOT just the center sector, so a landing that
        -- straddles a step rests ON the step instead of wedging below it. Grounded:
        -- snap up/down for small changes (crisp stairs, <= MAXSTEP); a real ledge
        -- (drop > MAXSTEP) hands off to gravity until you land. fallVel ~= 0 = airborne.
        local floorz = W.floorZAt(W.viewX, W.viewY)
        local feet = W.viewZ - W.EYE
        if W.fallVel == 0 and (feet - floorz) <= W.MAXSTEP then
            feet = floorz                                 -- grounded: step up / down
        else
            W.fallVel = W.fallVel - W.GRAVITY * dt        -- airborne: accelerate down
            feet = feet + W.fallVel * dt
            if feet <= floorz then feet = floorz; W.fallVel = 0 end
        end
        W.viewZ = feet + W.EYE

        W.updatePickups()                    -- walk-over item touch (end of frame)
        if kpressed(W.VK.ONE) then W.selectSlot(1) end
        if kpressed(W.VK.TWO) then W.selectSlot(2) end
        if kpressed(W.VK.THREE) then W.selectSlot(3) end
        if kpressed(W.VK.FOUR) then W.selectSlot(4) end
        if kpressed(W.VK.FIVE) then W.selectSlot(5) end
        if kpressed(W.VK.SIX) then W.selectSlot(6) end
        if kpressed(W.VK.SEVEN) then W.selectSlot(7) end

        W.updateWeapon(dt)                    -- psprite: switch anim, bob, fire scheduler
        if W.damageCount > 0 then W.damageCount = max(0, W.damageCount - dt * 45) end

        if kpressed(W.VK.M) then W.mouseLook = not W.mouseLook end
        if kpressed(W.VK.BACKSPACE) or kpressed(W.VK.ESCAPE) then    -- pause -> front-end main
            W.menu.fromPlay = true; W.menu.screen = "main"; W.menu.cursor = 1
            W.gameState = "frontend"; pcall(W.playSfx, "DSSWTCHN")
        end
    elseif W.gameState == "frontend" and not menuOpen then
        if not W.menu.fromPlay then                  -- fresh menu: attract level behind the buttons
            if W.menu.screen ~= "title" and not W.attractOn then W.startAttract() end
            if W.attractOn then W.updateAttractCam(dt) end
        end
        W.updateFrontend(dt)
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

-- Load a map and drop the player at its start.
function W.startMap(name)
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
function W.drawHUD(sw, sh)
    local y = W.viewH
    rectf(0, y, sw, sh, 24, 22, 28, 235)
    ImGui.AddText(8, y + 2, tostring(W.map and W.map.name or "-"), 175, 170, 155, 255)
    -- status line: health / armor / weapon / ammo, with coloured key pips at right
    local sy = y + floor(W.hudH * 0.42)
    ImGui.AddText(8, sy, string.format("HEALTH %d%%", floor(W.health or 0)), 235, 90, 80, 255)
    ImGui.AddText(floor(sw * 0.22), sy, string.format("ARMOR %d%%", floor(W.armor or 0)), 120, 180, 235, 255)
    ImGui.AddText(floor(sw * 0.44), sy, W.WEAPNAME[W.curWeapon or 2] or "-", 230, 220, 140, 255)
    local ak = W.HUDAMMOKEY[W.curWeapon or 2]
    local ammoStr = (ak and W.ammo and W.ammo[ak] ~= nil) and tostring(W.ammo[ak]) or "--"
    ImGui.AddText(floor(sw * 0.64), sy, "AMMO " .. ammoStr, 230, 210, 120, 255)
    local kx, ki = floor(sw * 0.85), 0
    for _, col in ipairs({ "blue", "yellow", "red" }) do
        if W.keys and W.keys[col] then
            local c = W.KEYCOL[col]; local x0 = kx + ki * 16
            rectf(x0, sy, x0 + 11, sy + 13, c[1], c[2], c[3], 255)
        end
        ki = ki + 1
    end
    -- No crosshair: original DOOM had none, and with vertical autoaim a fixed
    -- center mark would misrepresent where shots actually land.
    local cx, cy = W.centerX, W.horizon
    -- "use" prompt when facing a door / switch
    local hint = W.useHint
    if hint then
        local sp = hint.special
        local label = (sp == 11 or sp == 51) and "SPACE: EXIT"
            or W.DOOR_SPECIALS[sp] and "SPACE: OPEN" or "SPACE: USE"
        ImGui.AddText(cx - 34, cy + 16, label, 245, 230, 140, 255)
    end
    -- pickup / locked-door message (top center) + gold bonus flash
    local m = (W.hudMsgUntil and now() < W.hudMsgUntil) and W.hudMsg or nil
    if m then ImGui.AddText(floor(W.centerX - #m * 3), 26, m, 245, 235, 150, 255) end
    if W.bonusFlash and now() < W.bonusFlash then rectf(0, 0, sw, W.viewH, 220, 180, 60, 40) end
    -- red pain flash scaled by recent damage
    if (W.damageCount or 0) > 0 then rectf(0, 0, sw, W.viewH, 200, 0, 0, floor(min(90, W.damageCount * 1.4))) end
    -- death overlay
    if W.playerDead then
        ImGui.AddText(floor(W.centerX - 44), floor(W.viewH * 0.42), "YOU DIED", 235, 60, 55, 255)
        ImGui.AddText(floor(W.centerX - 78), floor(W.viewH * 0.42) + 18, "press USE to restart", 210, 190, 120, 255)
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
    if mapName:match("^E%dM%d$") then
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
function W._mus2midi(mus)
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
            emit(string.char(0x90 | ch, n, vol[mch]))
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
function W.mus2midi(mus)
    local ok, midi, secs = pcall(W._mus2midi, mus)
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

-- Ensure the on-disk cache directory exists (shared with the texture cache).
-- Returns true if a cache path is available, false if music must stay silent.
function W.ensureCacheDir()
    if W.cacheDir then return true end
    local rok, root = pcall(FileMgr.GetMenuRootPath)
    if rok and root and root ~= "" then
        root = tostring(root)
        W.cacheDir = root .. "/Lua/DoomWad/cache"
        pcall(FileMgr.CreateDir, root .. "/Lua/DoomWad")
        pcall(FileMgr.CreateDir, W.cacheDir)
    end
    return W.cacheDir ~= nil
end

-- Convert (if needed), cache, and start the music for a map. No-op if music is
-- off or nothing suitable is found. Any prior track is closed first.
function W.playMusic(mapName)
    if not W.musicOn then return end
    W.stopMusic()
    if not W.ensureCacheDir() then return end
    local ord, name = W.musicLumpFor(mapName)
    if not ord then return end
    local path = W.cacheDir .. "/mus_" .. name:gsub("[^%w_%-]", "_") .. ".mid"
    local exists = false
    if FileMgr and FileMgr.DoesFileExist then
        local dok, de = pcall(FileMgr.DoesFileExist, path)
        if dok and de then exists = true end
    end
    -- Convert + cache once per track. If the .mid is already on disk and we know
    -- its duration, skip the (re)conversion entirely (avoids redundant work on
    -- map switches / re-enable).
    W.musLenByName = W.musLenByName or {}
    local secs = W.musLenByName[name]
    if not (exists and secs) then
        local bytes = W.lumpBytes(ord)
        if #bytes < 4 then return end
        local head = bytes:sub(1, 4)
        local midi
        if head == "MThd" then
            midi, secs = bytes, 0             -- already a MIDI (custom PWAD)
        elseif head == "MUS\26" then
            midi, secs = W.mus2midi(bytes)
        else
            return                            -- unknown music format -> silence
        end
        if not midi then return end
        if not exists then
            if not W.writeBytes(path, midi) then return end   -- io.open "wb"
        end
        W.musLenByName[name] = secs
    end
    local mp = path:gsub("/", "\\")           -- MCI prefers backslash paths
    W.musAlias = W.musAlias or "doommus"
    W.mci('close ' .. W.musAlias)             -- clear any stale alias
    if not W.mci('open "' .. mp .. '" type sequencer alias ' .. W.musAlias) then return end
    if not W.mci('play ' .. W.musAlias) then W.mci('close ' .. W.musAlias); return end
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
            W.mci('play ' .. W.musAlias)
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
function W._dmx2wav(bytes)
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
function W.dmx2wav(bytes)
    local ok, wav = pcall(W._dmx2wav, bytes)
    if not ok then return nil end
    return wav
end

-- Convert (if needed), cache, and play a DOOM sound effect lump one-shot.
function W.playSfx(name)
    if not W.ensureCacheDir() then return end
    local ord = W.lumpIndex and W.lumpIndex[name] and W.lumpIndex[name][1]
    if not ord then return end
    local path = W.cacheDir .. "/sfx_" .. name:gsub("[^%w_%-]", "_") .. ".wav"
    local exists = false
    if FileMgr and FileMgr.DoesFileExist then
        local dok, de = pcall(FileMgr.DoesFileExist, path)
        if dok and de then exists = true end
    end
    if not exists then
        local wav = W.dmx2wav(W.lumpBytes(ord))
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

-- Patch pixel size (cheap 4-int header read, cached), independent of the GPU bake.
function W.patchSize(name)
    W.patchWH = W.patchWH or {}
    local m = W.patchWH[name]
    if m == nil then
        local li = W.lumpIndex and W.lumpIndex[name]
        local data = W.lumpBytes(li and li[1])
        if not data or #data < 8 then W.patchWH[name] = false; return nil end
        local w, h = string.unpack("<i2i2", data, 1)
        if w <= 0 or h <= 0 or w > 4096 or h > 4096 then W.patchWH[name] = false; return nil end
        m = { w = w, h = h }; W.patchWH[name] = m
    end
    if m == false then return nil end
    return m.w, m.h
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

function W.drawOptions(sw, sh, S, xbase)
    ImGui.AddText(floor(xbase + 100 * S), floor(18 * S), "OPTIONS", 235, 210, 120, 255)
    for i, it in ipairs(W.OPT_ITEMS) do
        local dy = 50 + (i - 1) * 16; local sel = (W.menu.cursor == i)
        local val
        if it.opt == "mouselook" then val = W.mouseLook and "ON" or "OFF"
        elseif it.opt == "music" then val = W.musicOn and "ON" or "OFF"
        else val = string.format("%.2f", W.LOOKSENS or 0.1) end
        local x = floor(xbase + 60 * S); local y = floor(dy * S)
        local r, g, b = 200, 200, 205; if sel then r, g, b = 255, 240, 150 end
        ImGui.AddText(x, y, it.text .. ":  " .. val, r, g, b, 255)
        if sel then W.drawSkull(60, dy, S, xbase) end
    end
    ImGui.AddText(floor(xbase + 40 * S), floor(120 * S), "Left/Right adjust, Enter toggle, Esc back", 170, 170, 180, 220)
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
            ImGui.AddRectFilled(0, floor(sh * 0.44), floor(sw), floor(sh * 0.56), 8, 6, 10, 235)
            ImGui.AddText(floor(sw * 0.5 - 200), floor(sh * 0.48), "are you sure? this skill level isn't even remotely fair.  (y / n)", 235, 120, 90, 255)
        end
    elseif scr == "options" then
        W.drawOptions(sw, sh, S, xbase)
    elseif scr == "readthis" then
        W.drawPatchFS("HELP1", sw, sh)
    elseif scr == "quit" then
        ImGui.AddText(floor(sw * 0.5 - 110), floor(sh * 0.48), "Quit to the title screen?  (Y / N)", 235, 210, 120, 255)
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
    W.attractCam.baseZ = W.floorZAt(ax, ay) + W.EYE
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
        elseif act == "quit" then m.screen = "quit"; pcall(W.playSfx, "DSSWTCHN") end
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

function W.optionAdjust(it, dir)
    if it.opt == "mouselook" then W.mouseLook = not W.mouseLook; pcall(W.playSfx, "DSPISTOL")
    elseif it.opt == "music" then
        W.musicOn = not W.musicOn
        if not W.musicOn then pcall(W.requestStop, "opt") elseif W.gameState == "play" and W.map then W.musPending = W.map.name end
        pcall(W.playSfx, "DSPISTOL")
    elseif it.opt == "looksens" then
        W.LOOKSENS = clamp((W.LOOKSENS or 0.1) + dir * 0.02, 0.02, 0.5); pcall(W.playSfx, "DSSTNMOV")
    end
end

function W.updateFrontend(dt)
    local m = W.menu
    local scr = m.screen
    if scr == "title" then
        if kpressed(W.VK.ENTER) or kpressed(W.VK.SPACE) then m.screen = "main"; m.cursor = 1; pcall(W.playSfx, "DSPISTOL") end
        return
    end
    if scr == "quit" then
        if kpressed(W.VK.Y) then m.screen = "title"; m.fromPlay = false; W.attractOn = false; pcall(W.requestStop, "quit"); pcall(W.playSfx, "DSSWTCHX")
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

function W.render()
    local sok, sw, sh = pcall(ImGui.GetDisplaySize)
    if not sok or not sw or sw < 16 or sh < 16 then return end
    ImGui.SetNextWindowPos(0, 0, ImGuiCond.Always)
    ImGui.SetNextWindowSize(sw, sh, ImGuiCond.Always)
    ImGui.Begin("##DoomWadOverlay", true, W.OVERLAY_FLAGS)
    -- Draw the body under pcall so a mid-frame error can never skip ImGui.End():
    -- an unbalanced Begin/End would desync the shared ImGui window stack and
    -- corrupt Cherax's own overlay/menu on later frames.
    local bok, berr = pcall(W.renderBody, sw, sh)
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
    else
        ImGui.AddText(12, 12, "No WAD loaded. Put a .wad in Cherax/Lua (or Lua/DoomWad),", 200, 200, 205, 255)
        ImGui.AddText(12, 30, "then open the DOOM WAD tab and press Scan.", 200, 200, 205, 255)
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
        if p and p ~= "" and not seen[p] then seen[p] = true; out[#out + 1] = p end
    end
    local names = { "DOOM1.WAD", "DOOM.WAD", "DOOM2.WAD", "freedoom1.wad", "freedoom2.wad" }
    local dirs = {}
    local rok, root = pcall(FileMgr.GetMenuRootPath)
    if rok and root and root ~= "" then
        root = tostring(root)
        -- The Cherax root folder is cleared on update, so persistent user files
        -- live under Lua/. Prefer Lua/DoomWad, then Lua, before the volatile root.
        dirs[#dirs + 1] = root .. "/Lua/DoomWad/"
        dirs[#dirs + 1] = root .. "/Lua/"
        dirs[#dirs + 1] = root .. "/DoomWad/"
        dirs[#dirs + 1] = root .. "/"
        pcall(FileMgr.CreateDir, root .. "/Lua/DoomWad")   -- ensure a home for the wad + future cache
    end
    dirs[#dirs + 1] = ""   -- current working dir, last-resort fallback
    for _, d in ipairs(dirs) do
        if FileMgr and FileMgr.FindFiles then
            local fok, list = pcall(FileMgr.FindFiles, (d == "") and "." or d, "wad", false)
            if fok and type(list) == "table" then
                -- FindFiles may return bare names or full paths; accept whichever
                -- form actually exists so we never list an unopenable candidate.
                for _, f in ipairs(list) do
                    f = tostring(f)
                    local full = d .. f
                    local aok, ex = pcall(FileMgr.DoesFileExist, full)
                    if aok and ex then add(full)
                    else
                        local bok, bex = pcall(FileMgr.DoesFileExist, f)
                        if bok and bex then add(f) end
                    end
                end
            end
        end
        for _, n in ipairs(names) do
            local dok, ex = pcall(FileMgr.DoesFileExist, d .. n)
            if dok and ex then add(d .. n) end
        end
    end
    W.wadCandidates = out
    return out
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

-- Host-mode only: fetch DOOM1.WAD (shareware IWAD) into Lua/DoomWad on first run.
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
        local cands = W.scanWads()
        if cands and cands[1] then W.dlDone = true; return "done" end
    end
    if not W.dlHandle and not W.dlKicked then
        W.dlKicked = true
        local ok = pcall(function()
            local h = Curl.Easy()
            h:Setopt(eCurlOption.CURLOPT_URL, WAD_URL)
            h:Setopt(eCurlOption.CURLOPT_USERAGENT, "CheraxDoom-WAD")
            h:Perform()
            W.dlHandle = h
        end)
        if not ok or not W.dlHandle then W.dlHandle = nil; W.dlFailed = true; return "failed" end
        W.dlStart = now()
    end
    if W.dlHandle then
        local fin = false
        pcall(function() fin = W.dlHandle:GetFinished() end)
        if not fin then
            if (now() - (W.dlStart or 0)) > 60 then W.dlHandle = nil; W.dlFailed = true; return "failed" end
            return "busy"
        end
        local code, body
        pcall(function() code, body = W.dlHandle:GetResponse() end)
        W.dlHandle = nil
        local magic = (type(body) == "string") and body:sub(1, 4) or ""
        if code == eCurlCode.CURLE_OK and #body > 100000 and (magic == "IWAD" or magic == "PWAD") then
            if W.writeBytes(W.dlTarget, body) then W.dlDone = true; return "done" end
        end
        W.dlFailed = true; return "failed"
    end
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
            ImGui.AddText(cx, cy + 18, "Drop a .wad in Cherax/Lua/DoomWad and reopen.", 200, 200, 205, 255)
        else
            ImGui.AddText(cx, cy, "Downloading DOOM1.WAD...", 235, 220, 120, 255)
        end
    end)
    ImGui.End()
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
    -- Phase-2 constants (MOVE is units/sec; run with Shift, tune in-game)
    W.EYE = 41; W.RADIUS = 16; W.MAXSTEP = 24; W.PHEIGHT = 56
    W.NEARZ = 4; W.HFOV = pi / 2
    W.MOVE = 200; W.RUN = 1.8; W.TURN = 2.6; W.MOUSE = 0.0026
    W.LOOKSENS = 0.1                     -- mouse turn sensitivity (GTA INPUT_LOOK_LR -> radians)
    W.GRAVITY = 1225                     -- units/s^2 for falling off ledges (Doom ~1 u/tic^2)
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
    W.SIGHT_RANGE = 2048       -- max distance a monster can notice/attack the player
    W.MON_HEIGHT = 56          -- opening a monster's box needs to fit through a portal
    -- combat / weapon input state (inventory itself lives in W.newGame)
    W.psp = W.psp or { state = "ready", sx = 0, sy = 0, flash = 0, refire = 0, bobT = 0 }
    W.weaponClock = 0; W.autoAim = false
    W.fireHeld = false; W.firePrev = false; W.playerSpeed = 0
    -- camera / view state
    W.viewX = 0; W.viewY = 0; W.viewZ = W.EYE; W.viewAngle = 0
    W.active = false
    W.mouseLook = false
    -- audio / music state (Section M). musicOn is a user toggle (default on);
    -- looping is duration-driven off now() since MCI cannot report position.
    W.musicOn = true
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
    -- Host mode runs unconditionally (no toggle to find); standalone honors the
    -- DOOM WAD feature toggle as before.
    local enabled = BLAD_MODE
    if not enabled then
        local eok, e = pcall(FeatureMgr.IsFeatureEnabled, FEATURE_HASH)
        if eok then enabled = e end
    end
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
        W.drawBootProgress(st)
        if st ~= "done" then return end
    end

    if not W.active then
        W.active = true
        W.lastTime = now()
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
    ImGui.Text("Load a DOOM/DOOM2 .wad, pick a map, then close the menu to walk.")
    ImGui.Text("Put your .wad in the Cherax/Lua folder (or Cherax/Lua/DoomWad).")
    ImGui.Text("The Cherax root folder is cleared, so it must go under Lua.")
    ImGui.Text("State: " .. tostring(W.gameState) .. "    " .. tostring(W.status or ""))
    if ImGui.Separator then ImGui.Separator() end

    -- WAD picker
    ImGui.Text("WAD: " .. tostring(W.wadPath or "(none)"))
    if W.uiRow("Scan for WAD files") then W.scanWads() end
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

if FeatureMgr and FeatureMgr.AddFeature then
    pcall(FeatureMgr.AddFeature, FEATURE_HASH, "DOOM WAD",
        (eFeatureType and eFeatureType.Toggle) or 1,
        "Load and walk a DOOM/DOOM2 .wad map in the overlay (flat-shaded BSP renderer). Enable, then close the menu to walk.",
        function(f)
            local on = true
            local cok, cr = pcall(function() return f:IsToggled() end)
            if cok then on = cr end
            -- Runs on the menu thread (the context where the manual disable
            -- worked); request a retried stop so it also survives onPresent.
            if not on then W.active = false; pcall(W.requestStop, "toggle-cb") end
        end)
end

-- Host mode: reflect the always-on run state in the toggle so the DOOM WAD tab's
-- checkbox reads correctly, and register a hidden shutdown feature. bladscript
-- resolves SHUTDOWN_HASH from the shared registry and OnClick()s it; that callback
-- runs in THIS script's state, so SetShouldUnload marks this script for unload
-- (never the host). It is never RenderFeature'd and is set invisible besides.
if BLAD_MODE and FeatureMgr and FeatureMgr.GetFeature then
    pcall(function() FeatureMgr.GetFeature(FEATURE_HASH):SetBoolValue(true) end)
end
if BLAD_MODE and FeatureMgr and FeatureMgr.AddFeature then
    local sf = FeatureMgr.AddFeature(SHUTDOWN_HASH, "CheraxDoom Shutdown",
        (eFeatureType and eFeatureType.Button) or 0,
        "Internal: unload CheraxDoom. Triggered by the host script, not for direct use.",
        function()
            pcall(W.requestStop, "shutdown")
            if SetShouldUnload then pcall(SetShouldUnload) end
        end)
    if sf then
        pcall(function() sf:SetVisible(false) end)
        pcall(function() sf:SetSaveable(false) end)
    end
end

if EventMgr and EventMgr.RegisterHandler then
    pcall(EventMgr.RegisterHandler, (eLuaEvent and eLuaEvent.ON_PRESENT) or 7, W.onPresent)
    -- On unload (uninject), stop the MCI music + any SFX. The MCI sequencer is a
    -- Windows system device that keeps playing after the script is gone otherwise.
    -- No retry is possible after unload, so send the stop a few times.
    pcall(EventMgr.RegisterHandler, (eLuaEvent and eLuaEvent.ON_UNLOAD) or 11, function()
        -- The unload thread cannot reach the MCI device by our alias (stop/close
        -- <alias> return false here per the in-game log), so use the alias-free
        -- 'stop all'/'close all', which close every MCI device this process owns.
        local a = W.musAlias or "doommus"
        local r1, r2, r3, r4
        if Utils and Utils.MciSendString then
            for _ = 1, 3 do
                pcall(Utils.MciSendString, "stop " .. a)
                pcall(Utils.MciSendString, "close " .. a)
                local _, x1 = pcall(Utils.MciSendString, "stop all"); r3 = x1
                local _, x2 = pcall(Utils.MciSendString, "close all"); r4 = x2
            end
        end
        if Utils and Utils.StopSound then pcall(Utils.StopSound) end
        W.musPlaying = false; W.musTrack = nil
        -- Drop the hidden cross-script shutdown feature so no stale entry lingers
        -- in the shared registry for the next launch.
        if FeatureMgr and FeatureMgr.RemoveFeature then
            pcall(FeatureMgr.RemoveFeature, SHUTDOWN_HASH)
        end
        if W.stopDiag and Logger and Logger.LogInfo then
            pcall(Logger.LogInfo, ("[DOOMWAD] ON_UNLOAD: stopall=%s closeall=%s"):format(tostring(r3), tostring(r4)))
        end
    end)
end

if ClickGUI and ClickGUI.AddTab then
    pcall(ClickGUI.AddTab, "DOOM WAD", W.renderTab)
end

if Logger and Logger.LogInfo then
    pcall(Logger.LogInfo, "[DOOMWAD] loaded (phase 3: textured BSP walls + on-disk PNG cache).")
end

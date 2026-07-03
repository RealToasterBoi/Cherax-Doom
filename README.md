# Cherax-Doom

An implementation of DOOM that runs inside the [Cherax](https://cherax.io) Lua
overlay for Grand Theft Auto V. `CheraxDoom.lua` is a from-scratch WAD reader,
map-geometry parser and BSP renderer written in pure Lua against the Cherax Lua
API. It loads a real DOOM / DOOM2 `.wad`, parses its lumps, and draws a playable
level on an ImGui overlay window, with a Doom-style front-end, textured walls and
flats, billboard sprites, enemy AI, and MIDI music.

This is a toy / tech demo. No id Software assets are included; you supply your
own `.wad`.

## What it does

- **WAD container**: parses the 12-byte header + lump directory, decodes a
  level's geometry lumps (VERTEXES, LINEDEFS, SIDEDEFS, SECTORS, THINGS, SEGS,
  SSECTORS, NODES) into plain Lua tables. IWAD and PWAD supported.
- **Renderer**: front-to-back BSP wall renderer with textured walls, textured
  floor/ceiling flats, sky, and distance shading. Billboard THING sprites are
  drawseg-silhouette clipped against the walls.
- **Gameplay**: a 35 Hz simulation with player movement/collision, doors and
  lifts, the DOOM weapon set with hitscan and projectile combat, item/ammo
  pickups, and the full monster roster with AI ported from the original source.
- **Front-end**: the WAD's own menu patch lumps (M_DOOM, M_SKULL, skill icons)
  baked to textures, with a text fallback; skill select and a screen-melt wipe.
- **Music**: level music (MUS lumps converted to MIDI) played through the
  Windows MCI sequencer.

## Requirements

- GTA V with the Cherax menu (the Lua API must be available).
- A DOOM or DOOM2 `.wad`. The freely redistributable DOOM shareware IWAD works
  well; see for example
  [nneonneo/universal-doom](https://github.com/nneonneo/universal-doom).

## Standalone usage

1. Put `CheraxDoom.lua` in your Cherax `Lua` folder and run it from the Lua tab.
2. Put your `.wad` in `Cherax/Lua/DoomWad` (or `Cherax/Lua`). The Cherax root
   folder is wiped on update, so keep persistent files under `Lua`.
3. Enable the **DOOM WAD** feature and open the **DOOM WAD** tab. It scans for
   wads on its own; pick one, then press the centered **Play** button to launch,
   or pick a specific level from the map list. The top **Menu** entry is selected
   by default, so leaving it alone starts you on DOOM's own title screen. Close
   the menu to play. The **Scan** button re-checks the folders for wads you add
   later.

### Controls

| Action | Keys |
| --- | --- |
| Move forward / back | `W` / `S` or `Up` / `Down` |
| Strafe | `A` / `D` |
| Turn | `Left` / `Right`, or the mouse (toggle with `M`) |
| Run | `Shift` |
| Back to the map menu | `Backspace` |

## Embedding in another script

`CheraxDoom.lua` can be launched by a host Lua script instead of run by hand. If
the global `BladscriptLoaded` is set to `true` before this chunk runs (e.g. a
host prepends `BladscriptLoaded=true` and then `Utils.ExecuteScript`s the file),
CheraxDoom will:

- auto-run without waiting for the DOOM WAD toggle,
- download the shareware `DOOM1.WAD` into `Cherax/Lua/DoomWad` on first run if no
  wad is present, and
- register a hidden `CheraxDoom_Shutdown` button feature. Because each Cherax
  Lua script has its own isolated state, a host can resolve that hash from the
  shared feature registry and call `:OnClick()` on it to unload CheraxDoom
  cleanly without touching the host script.

## Notes / credits

- DOOM is a trademark of id Software LLC. This project ships no id assets and is
  not affiliated with or endorsed by id Software or Rockstar Games.
- WAD parsing follows the classic on-disk formats: all indices are 0-based as
  stored, `0xFFFF` is the "no sidedef" sentinel, and the `0x8000` bit on a node
  child marks a subsector reference.

# Working rules (`projects/pillow`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), which is
authoritative on proof soundness, allowed axioms and the strict ISO C17 undefined-behaviour policy.
The runtime starts from `framework/lean/StrictPtr.lean`.

**Status:** candidate. Upstream submodule `pillow/` tracks the latest default branch; not
registered in `framework/projects.json`; translation and proofs are not done.

## Tier 0

Tier 0 is the code that turns untrusted bytes into pixels or metadata on a default path. It is the
whole scope of this project.

**How it is reached.** `Image.open(fp)` tries every registered plugin's `_accept` (magic bytes
only) and parses the header in Python; `load()` — called by `thumbnail()`, `convert()`, `save()`
and pixel access — asks `Image._getdecoder` for a C decoder, and `src/decode.c` `_decode` feeds it
the file bytes. Pillow 13.0.0 ships its own decoders plus libjpeg-turbo, zlib-ng, libtiff (with
liblzma), libwebp, libavif and openjpeg; it does not use libpng or libexif.

**Functions** (`src/libImaging/` and its glue):

- Glue and allocation: `_decode` (`src/decode.c`), `ImagingNew`, `ImagingNewDirty`,
  `ImagingNewBlock`, `ImagingDelete`.
- Decoders with an external library behind them: `ImagingJpegDecode`, `ImagingZipDecode` (PNG,
  including row-filter reversal), `ImagingLibTiffDecode` with `_tiffReadProc` / `_tiffSeekProc`,
  `ImagingJpeg2KDecode`.
- Decoders Pillow owns completely: `ImagingGifDecode`, `ImagingPackbitsDecode`,
  `ImagingTgaRleDecode`, `ImagingSgiRleDecode`, `ImagingSunRleDecode`, `ImagingPcxDecode`,
  `ImagingFliDecode`, `ImagingPcdDecode`, `ImagingXbmDecode`, `ImagingBcnDecode`,
  `ImagingRawDecode`, `ImagingBitDecode`, and the unpackers chosen by `ImagingFindUnpacker`.

**What the proofs must cover.**

1. Decoder state (`x`, `y`, run lengths, LZW tables) carried across `_decode` calls with arbitrary
   chunk boundaries never writes outside `im->image[y]` or reads past the input chunk.
2. Buffers sized from the geometry Pillow requested agree with what the codec actually produces
   (JPEG draft scaling and lossless streams, TIFF strips and tiles).
3. Unpackers stay inside both the source chunk and the destination row for every raw mode.

## Local commands

```bash
lake --dir projects/pillow build --wfail PillowF PillowF.Results
python3 framework/check_project.py pillow --skip-build
```

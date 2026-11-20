# Working rules (`projects/libtiff`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), which is
authoritative on proof soundness, allowed axioms and the strict ISO C17 undefined-behaviour policy.
The runtime starts from `framework/lean/StrictPtr.lean`.

**Status:** candidate. Upstream submodule `libtiff/` tracks the latest default branch; not
registered in `framework/projects.json`; translation and proofs are not done.

## Tier 0

Tier 0 is the code that turns untrusted bytes into pixels or metadata on a default path. It is the
whole scope of this project.

**How it is reached.** TIFF is chosen by magic bytes, so a TIFF under any file name gets here.

- Sharp: `sharp(input).toBuffer()` → libvips `foreign/tiff.c` `vips__tiff_openin_source` →
  `foreign/tiff2vips.c` `rtiff_header_read`, `rtiff_strip_read`, `rtiff_read_tile`.
- Pillow: `Image.open(input).load()` → `TiffImageFile._load_libtiff` → `src/decode.c`
  `PyImaging_LibTiffDecoderNew` → `src/libImaging/TiffDecode.c` `ImagingLibTiffDecode`.

**Functions:** `TIFFClientOpen`, `TIFFClientOpenExt`, `TIFFReadDirectory`, `TIFFSetDirectory`,
`TIFFGetField`, `TIFFGetFieldDefaulted`, `TIFFIsTiled`, `TIFFScanlineSize`, `TIFFStripSize`,
`TIFFTileSize`, `TIFFReadScanline`, `TIFFReadEncodedStrip`, `TIFFReadTile`, `TIFFReadRawTile`,
`TIFFRGBAImageOK`, `TIFFRGBAImageBegin`, `TIFFRGBAImageGet`, `TIFFRGBAImageEnd`, `TIFFClose` —
plus the codecs they dispatch to in both builds: none, PackBits, LZW, Deflate, JPEG, CCITT
Group 3/4 (LZMA in Pillow's build), and the horizontal and floating-point predictors.

**What the proofs must cover.**

1. Directory parsing: tag counts and offsets, type mismatches, BigTIFF offsets and directory loops.
2. Strip and tile sizes computed in 64 bits and narrowed to `tmsize_t` match the buffers filled.
3. LZW, CCITT, PackBits and the predictors stay inside their buffers on hostile input.

## Local commands

```bash
lake --dir projects/libtiff build -j 4 --wfail LibtiffF LibtiffF.Results
python3 framework/check_project.py libtiff --skip-build
```

# Working rules (`projects/libtiff`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), including the strict
ISO C17 undefined-behaviour policy: no `NULL`, wild or dangling pointer `+ 0`, no `NULL - NULL`, no
cross-object pointer subtraction or comparison, no out-of-bounds pointer formation, no zero-length
`memcpy`/`memset` on invalid pointers, every struct pointer field written before it is read, and no
"benign UB" arguments. The runtime starts from `framework/lean/StrictPtr.lean`.

- **Status:** candidate. Upstream submodule `libtiff/` tracks the latest default branch. Not
  registered in `framework/projects.json`; translation and proofs are not done.

## Why it matters

TIFF is sniffed by magic bytes in both libraries, so a TIFF disguised under any file name reaches
libtiff (4.7.2 in both Sharp 0.35.5 and Pillow 13.0.0):

- **Sharp:** libvips `foreign/tiff2vips.c`, `foreign/vips2tiff.c`, `foreign/tiff.c`. Sharp's build
  disables the LZMA, ZSTD, LERC, JBIG, libdeflate, old-JPEG and PixarLog codecs.
- **Pillow:** `libImaging/TiffDecode.c` (decode and save, with Pillow's own in-memory read, seek
  and write callbacks). Pillow's build disables WebP, ZSTD and libdeflate and keeps LZMA.

## Interfaces to prove (P0)

- **Open and directories:** `TIFFClientOpen`, `TIFFClientOpenExt`, `TIFFOpenOptionsAlloc`,
  `TIFFOpenOptionsSetMaxCumulatedMemAlloc`, `TIFFOpenOptionsSetErrorHandlerExtR`,
  `TIFFOpenOptionsSetWarningHandlerExtR`, `TIFFOpenOptionsFree`, `TIFFFdOpen`, `TIFFReadDirectory`,
  `TIFFSetDirectory`, `TIFFSetSubDirectory`, `TIFFClose`, `TIFFCleanup`.
- **Tags:** `TIFFGetField`, `TIFFGetFieldDefaulted`, `TIFFSetField`, `TIFFVSetField`,
  `TIFFFindField`, `TIFFFieldDataType`, `TIFFFieldPassCount`, `TIFFFieldWriteCount`,
  `TIFFMergeFieldInfo`.
- **Geometry:** `TIFFIsTiled`, `TIFFScanlineSize`, `TIFFScanlineSize64`, `TIFFStripSize`,
  `TIFFTileSize`, `TIFFTileRowSize`, `TIFFNumberOfStrips`, `TIFFNumberOfTiles`, `TIFFComputeStrip`,
  `TIFFComputeTile`.
- **Read:** `TIFFReadScanline`, `TIFFReadEncodedStrip`, `TIFFReadTile`, `TIFFReadRawTile`,
  `TIFFReadRGBATile`, `TIFFRGBAImageOK`, `TIFFRGBAImageBegin`, `TIFFRGBAImageGet`,
  `TIFFRGBAImageEnd`, and the built-in codecs they dispatch to: none, PackBits, LZW, Deflate,
  JPEG, CCITT Group 3/4, plus the horizontal and floating-point predictors.
- **Write:** `TIFFWriteScanline`, `TIFFWriteTile`, `TIFFWriteRawTile`, `TIFFWriteDirectory`,
  `TIFFFlush`.

## Verification hazards

1. Directory parsing: tag counts and offsets, type mismatches, BigTIFF 64-bit offsets, directory
   loops and sub-IFDs.
2. Strip and tile size arithmetic in 64 bits narrowed to `tmsize_t`, planar configuration, and
   bits per sample.
3. LZW, CCITT and PackBits decoders on truncated or hostile input.
4. Predictors whose buffer length is not a multiple of the stride.
5. The RGBA path (`tif_getimage.c`) for every photometric interpretation.
6. Save path: tags supplied by the caller that disagree with the pixel buffer it writes.

## Not in scope

Codecs disabled in both builds (ZSTD, LERC, JBIG, libdeflate, old-JPEG, PixarLog), the C++
stream API, command-line tools, and the file-system `TIFFOpen` beyond the callback model.

## Local commands

```bash
lake --dir projects/libtiff build --wfail LibtiffF LibtiffF.Results
python3 framework/check_project.py libtiff --skip-build
```

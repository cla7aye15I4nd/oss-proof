# Working rules (`projects/libavif`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), including the strict
ISO C17 undefined-behaviour policy: no `NULL`, wild or dangling pointer `+ 0`, no `NULL - NULL`, no
cross-object pointer subtraction or comparison, no out-of-bounds pointer formation, no zero-length
`memcpy`/`memset` on invalid pointers, every struct pointer field written before it is read, and no
"benign UB" arguments. The runtime starts from `framework/lean/StrictPtr.lean`.

- **Status:** candidate. Upstream submodule `libavif/` tracks the latest default branch. Not
  registered in `framework/projects.json`; translation and proofs are not done.

## Why it matters

Pillow's wheels bundle libavif (1.4.2 in Pillow 13.0.0) and register an AVIF plugin, so any AVIF
upload passed to `Image.open` is parsed by libavif's container code and decoded by dav1d; saving
uses aom. Sharp does not use libavif (it reads AVIF and HEIF through libheif).

## Interfaces to prove (P0)

Exactly what `src/_avif.c` calls:

- **Decode:** `avifDecoderCreate`, `avifDecoderSetIOMemory`, `avifDecoderParse`,
  `avifDecoderNthImage`, `avifRGBImageSetDefaults`, `avifRGBImageAllocatePixels`,
  `avifImageYUVToRGB`, `avifRGBImageFreePixels`, `avifDecoderDestroy`, `avifResultToString`.
- **Encode:** `avifEncoderCreate`, `avifEncoderSetCodecSpecificOption`, `avifImageCreateEmpty`,
  `avifImageRGBToYUV`, `avifImageSetProfileICC`, `avifImageSetMetadataExif`,
  `avifImageSetMetadataXMP`, `avifEncoderAddImage`, `avifEncoderFinish`, `avifImageDestroy`,
  `avifEncoderDestroy`, `avifRWDataFree`.
- **Queries:** `avifVersion`, `avifCodecVersions`, `avifCodecName`, `avifCodecChoiceFromName`.

The libavif code behind them: stream reader and writer, ISOBMFF box parser (`read.c`), AV1
sequence-header parser (`obu.c`), grid assembly, YUV/RGB reformatting (`reformat.c`, `alpha.c`).

## Verification hazards

1. Box sizes (32-bit, 64-bit `largesize`, size 0) and stream buffer growth.
2. Item locations (`iloc`) extents, item references (`iref`) cycles, and the `clap` crop rectangle.
3. Grid images whose tiles differ in size, depth or chroma subsampling from the declared grid.
4. YUV/RGB conversion strides for odd dimensions and every supported depth.

## Not in scope

The AV1 codecs themselves (dav1d, aom — large, partly assembly), libyuv and sharpyuv
acceleration, experimental gain-map APIs, and the command-line tools.

## Local commands

```bash
lake --dir projects/libavif build --wfail LibavifF LibavifF.Results
python3 framework/check_project.py libavif --skip-build
```

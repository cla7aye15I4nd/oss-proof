# Working rules (`projects/pillow`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), including the strict
ISO C17 undefined-behaviour policy: no `NULL`, wild or dangling pointer `+ 0`, no `NULL - NULL`, no
cross-object pointer subtraction or comparison, no out-of-bounds pointer formation, no zero-length
`memcpy`/`memset` on invalid pointers, every struct pointer field written before it is read, and no
"benign UB" arguments. The runtime starts from `framework/lean/StrictPtr.lean`.

- **Status:** candidate. Upstream submodule `pillow/` tracks the latest default branch. Not
  registered in `framework/projects.json`; translation and proofs are not done.

## What ships (measured, not assumed)

Measured by installing Pillow 13.0.0 from PyPI on Linux x86_64 (`PIL.features`, the bundled
`pillow.libs/` directory, and the upstream wheel build script):

- **Bundled C libraries:** libjpeg-turbo 3.2.0, zlib-ng 2.3.3, libtiff 4.7.2 (with liblzma 5.8.4),
  libwebp 1.6.0, libavif 1.4.2 (dav1d for decoding, aom for encoding), openjpeg 2.5.4, lcms2 2.19,
  FreeType 2.14.3 (+ harfbuzz, raqm, brotli, libpng for fonts only), libxcb.
- **Pillow does not use libpng or libexif.** PNG chunks are parsed in Python
  (`PngImagePlugin.py`) and pixel data is inflated by `libImaging/ZipDecode.c` with zlib-ng; EXIF is
  parsed in Python.
- **`Image.open(fp)` tries every registered plugin's `_accept` check** (43 formats) unless the
  caller passes `formats=`. The file name is not consulted, so every C decoder below is reachable
  from an upload.

## High-profile paths

| Format (plugin) | Decoder | C implementation | External library |
| --- | --- | --- | --- |
| JPEG, MPO | `jpeg` | `libImaging/JpegDecode.c` | libjpeg-turbo |
| PNG, APNG | `zip` | `libImaging/ZipDecode.c` | zlib-ng (`inflateInit`, `inflate`, `inflateEnd`) |
| GIF | `gif` | `libImaging/GifDecode.c` | none (own LZW) |
| TIFF | `libtiff`, `raw` | `libImaging/TiffDecode.c` | libtiff (+ libjpeg-turbo, zlib-ng, liblzma) |
| WebP | — | `src/_webp.c` | libwebp |
| AVIF | — | `src/_avif.c` | libavif → dav1d |
| JPEG 2000 | `jpeg2k` | `libImaging/Jpeg2KDecode.c` | openjpeg |
| PSD | `packbits` | `libImaging/PackDecode.c` | none |
| TGA, SGI, SUN | `tga_rle`, `sgi_rle`, `sun_rle` | `TgaRleDecode.c`, `SgiRleDecode.c`, `SunRleDecode.c` | none |
| PCX, FLI, PCD, XBM | `pcx`, `fli`, `pcd`, `xbm` | `PcxDecode.c`, `FliDecode.c`, `PcdDecode.c`, `XbmDecode.c` | none |
| DDS, FTEX, BLP | `bcn` | `libImaging/BcnDecode.c` | none |
| BMP, ICO, PPM, IM, and the rest | `raw`, `bit` | `RawDecode.c`, `BitDecode.c`, `Unpack.c` | none |

Decoders written in Python (BMP RLE, DDS RGB, FITS, MSP, PPM text, QOI, SGI 16-bit, XPM) are not C
targets. After decoding, `thumbnail()` / `resize()` / `reduce()` run `Resample.c` and `Reduce.c`,
and `convert()` runs `Convert.c`. Saving runs `JpegEncode.c`, `ZipEncode.c`, `GifEncode.c`,
`TiffDecode.c` (`ImagingLibTiffEncode` with Pillow's own in-memory write callback), `_webp.c` and
`_avif.c`. `ImageCms` (lcms2) and `ImageFont` (FreeType) run only when the application calls them.

## Interfaces to prove (P0)

`src/libImaging/`:

- Allocation: `ImagingNew`, `ImagingNewDirty`, `ImagingNewBlock`, `ImagingDelete` (`Alloc.c`).
- Decoders: `ImagingJpegDecode`, `ImagingZipDecode`, `ImagingGifDecode`, `ImagingLibTiffDecode`
  (with `_tiffReadProc`, `_tiffSeekProc`), `ImagingJpeg2KDecode`, `ImagingPackbitsDecode`,
  `ImagingTgaRleDecode`, `ImagingSgiRleDecode`, `ImagingSunRleDecode`, `ImagingPcxDecode`,
  `ImagingFliDecode`, `ImagingPcdDecode`, `ImagingXbmDecode`, `ImagingBcnDecode`,
  `ImagingRawDecode`, `ImagingBitDecode`, and the unpackers found by `ImagingFindUnpacker`.
- Processing: `ImagingResample`, `ImagingReduce`, `ImagingConvert`, `ImagingTranspose`,
  `ImagingRotate90`.
- Encoders: `ImagingJpegEncode`, `ImagingZipEncode`, `ImagingGifEncode`, `ImagingLibTiffEncode`
  (with `_tiffWriteProc`), and the packers found by `ImagingFindPacker`.

## Verification hazards

1. Buffers sized from the image geometry Pillow requested while the codec reports a different
   geometry (JPEG draft scaling and lossless streams; TIFF tags supplied at save time).
2. In-memory TIFF write callback growing and seeking its buffer.
3. RLE and LZW decoders whose state (`x`, `y`, run length, code table) crosses `ImagingDecode`
   calls with arbitrary input chunk boundaries.
4. Resampling coefficient windows for extreme scale factors and crop boxes.
5. Row-pointer images (`im->image[y]`) and pixel-format packers/unpackers with mismatched strides.

## Not in scope

CPython internals (modelled at the buffer boundary), Python-level plugins, subprocess paths
(Ghostscript for EPS), display and clipboard modules, and the external codecs, which are their own
projects.

## Local commands

```bash
lake --dir projects/pillow build --wfail PillowF PillowF.Results
python3 framework/check_project.py pillow --skip-build
```

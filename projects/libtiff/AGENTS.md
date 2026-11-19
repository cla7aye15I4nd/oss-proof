# Working rules (`projects/libtiff`)

Inherits all rules of the repository root [`../../AGENTS.md`](../../AGENTS.md), including the
**Strict ISO C17 Undefined Behaviour Policy** (`framework/check_runtime_ub.py` enforces this
mechanically):

- **No wild, uninitialised, freed/dangling, or `NULL` pointer `+ 0` (`p + 0`, `p - 0`, `&p[0]`)** —
  `Ptr.add` MUST check non-null, live allocation, `off <= a.size`, and `0 <= off + k <= a.size`
  even when `k = 0` (start from `framework/lean/StrictPtr.lean`; NEVER copy legacy shortcuts).
- **No `NULL - NULL` and no cross-object pointer subtraction or relational comparison** (`p - q`,
  `<`, `<=`, `>`, `>=` require the same live array object).
- **No out-of-bounds pointer formation**, even without dereference.
- **No `memcpy` / `memmove` / `memset` / `memcmp` with `n == 0` on `NULL` or dangling pointers**.
- **Every struct pointer field must be written before it is read**.
- **Never argue "benign UB"**. Report confirmed ISO C17 UB in `docs/{en,zh}/findings.md` with
  minimal upstream patches in `patches/`.

- **Status:** Scoped candidate project (not yet registered in `framework/projects.json`; Lean
  runtime bootstrap, upstream submodule pin, C translation, and safety proofs **Not done**).

## Scope (`LibtiffF`)

- **Upstream source:** `libtiff/` pinned submodule (`https://gitlab.com/libtiff/libtiff`) +
  `patches/*.patch` in name order.
- **Target configuration:** portable scalar x86_64 Linux LP64 build of `libtiff` (`libtiff/*.c`,
  linking proved `zlib` and modeled `libjpeg-turbo`/`libwebp`/`zstd`/`lzma` codec contracts when
  sub-codecs are enabled; classic TIFF + BigTIFF).
- **Verification goal:** full safety (no ISO C17 undefined behaviour, no IFD tag/count integer
  overflow, no strip/tile/scanline/predictor buffer overflow, no LZW/Fax3/PackBits/ZIP codec heap
  corruption, no UAF/double-free on directory switches or close, stated write frame, and
  termination) across **both TIFF decoding AND TIFF encoding** APIs called by **Sharp** and
  **Pillow**.

## Real-World Usage Paths & Function Priority

`libtiff` has historically had one of the **highest CVE densities of any C library in existence** —
and is **automatically reachable on untrusted uploads** in BOTH **Sharp** (`libvips/foreign/tiffload.c`
is auto-sniffed unless explicitly blocked via `sharp.block()`, site of `CVE-2026-35591`!) AND
**PIL / Pillow** (`Image.open()` auto-sniffs TIFF and routes into `TiffDecode.c`; saving hits
`ImagingLibTiffEncode` / `_tiffWriteProc`, site of `CVE-2026-112393` & `CVE-2026-128067`!), as well
as PDF renderers, OCR engines (Tesseract), geospatial (GDAL), and medical imaging.

### Exact C Functions Called by Sharp (`libvips`) & Pillow (`TiffDecode.c`)

- **Opening / Closing & Custom I/O:** `TIFFClientOpen`, `TIFFClientOpenExt`, `TIFFOpenOptionsAlloc`,
  `TIFFOpenOptionsSetMaxSingleMemAlloc`, `TIFFOpenOptionsFree`, `TIFFClose`, `TIFFCleanup`.
- **IFD / Directory & Tag Access:** `TIFFReadDirectory`, `TIFFSetDirectory`, `TIFFSetSubDirectory`,
  `TIFFNumberOfDirectories`, `TIFFGetField`, `TIFFGetFieldDefaulted`, `TIFFVGetField`,
  `TIFFSetField`, `TIFFVSetField`, `TIFFCheckpointDirectory`, `TIFFWriteDirectory`, `TIFFFlush`.
- **Geometry & Sizing:** `TIFFIsTiled`, `TIFFScanlineSize`, `TIFFScanlineSize64`, `TIFFStripSize`,
  `TIFFStripSize64`, `TIFFTileSize`, `TIFFTileSize64`, `TIFFTileRowSize`, `TIFFTileRowSize64`,
  `TIFFNumberOfStrips`, `TIFFNumberOfTiles`, `TIFFComputeStrip`, `TIFFComputeTile`.
- **Decoding (Read):** `TIFFReadScanline`, `TIFFReadEncodedStrip`, `TIFFReadRawStrip`,
  `TIFFReadTile`, `TIFFReadEncodedTile`, `TIFFReadRawTile`, `TIFFReadRGBAImage`,
  `TIFFReadRGBAImageOriented`, `TIFFReadRGBAStrip`, `TIFFReadRGBATile`.
- **Encoding (Write):** `TIFFWriteScanline`, `TIFFWriteEncodedStrip`, `TIFFWriteEncodedTile`,
  `TIFFWriteTile`.

### Tier 1 (P0) — Directory Parser, Strip/Tile Engine & Core Built-in Codecs (Prove First)

1. **Core I/O, IFD reader & tag system (`tif_open.c`, `tif_close.c`, `tif_dir.c`, `tif_dirinfo.c`,
   `tif_dirread.c`, `tif_error.c`, `tif_warning.c`, `tif_swab.c`, `tif_aux.c`, `tif_flush.c`):**
   `TIFFClientOpen*`, `TIFFReadDirectory`, `TIFFFetchNormalTag`, `TIFFSetDirectory`, `TIFFGetField*`,
   `TIFFSetField*`, `TIFFClose` (both classic 32-bit TIFF and 64-bit BigTIFF, little & big endian,
   IFD loop/cycle detection).
2. **Strip, tile, scanline & RGBA reader (`tif_read.c`, `tif_strip.c`, `tif_tile.c`,
   `tif_getimage.c`, `tif_color.c`):**
   `TIFFReadScanline`, `TIFFReadEncodedStrip`, `TIFFReadTile`, `TIFFReadEncodedTile`,
   `TIFFReadRGBAImage*`, `TIFFReadRGBAStrip`, `TIFFReadRGBATile`.
3. **Self-contained built-in compression codecs & horizontal/FP predictors (`tif_dumpmode.c`,
   `tif_packbits.c`, `tif_lzw.c`, `tif_zip.c`, `tif_predict.c`, `tif_fax3.c`, `tif_fax3sm.c`):**
   Covers uncompressed, PackBits, LZW, Deflate/ZIP (on top of proved `zlib`), CCITT Group 3/4 Fax,
   and horizontal 8/16/32-bit + floating-point predictors (`horAcc8`, `horAcc16`, `horAcc32`,
   `fpAcc` — and their encoder counterparts `horDiff8`, `horDiff16`, `horDiff32`, `fpDiff`!).

### Tier 1 (P0) — TIFF Encoding / Writing Path (Used by Sharp `tiffsave` & Pillow `save()`)

- **Directory & pixel writer (`tif_write.c`, `tif_dirwrite.c`, `tif_compress.c`):**
  `TIFFWriteScanline`, `TIFFWriteEncodedStrip`, `TIFFWriteEncodedTile`, `TIFFWriteTile`,
  `TIFFWriteDirectory`, `TIFFCheckpointDirectory` — paired with `tif_predict.c` (`horDiff*` —
  directly relevant to Pillow `CVE-2026-128067`!), `tif_zip.c` (`ZIPEncode`), `tif_lzw.c`
  (`LZWEncode`), `tif_packbits.c` (`PackBitsEncode`).

### Tier 2 (P1) & Explicitly Not Planned

- **Tier 2:** External-codec bridge wrappers (`tif_jpeg.c`, `tif_webp.c`, `tif_zstd.c`, `tif_lzma.c`),
  `tif_luv.c`, `tif_next.c`, `tif_thunder.c`, `tif_pixarlog.c`.
- **Not planned:** Obsolete/deprecated JPEG-in-TIFF v6 (`tif_ojpeg.c` — notoriously broken legacy
  spec; callers should disable), JBIG (`tif_jbig.c`), LERC (`tif_lerc.c`), CLI tools (`tools/tiff*`
  — historically huge separate CVE surface unrelated to library calls), C++ stream wrapper
  (`tif_stream.cxx`), and OS `mmap` (`tif_unix.c` beyond abstract `TIFFClientOpen` callbacks).

## Library-Specific Verification Hazards (No Shortcuts)

1. **IFD tag count/offset overflows, type confusion & cyclic IFD chains (`tif_dirread.c`, `tif_dir.c`).**
   Prove `TIFFFetchNormalTag` ASCII NUL-termination, BigTIFF 64-bit vs. 32-bit tag offset casting,
   `SubIFD` recursion depth & cycle rejection, and `TIFFFreeDirectory` cleanup on partial parse
   failure (no UAF or dangling tag pointers across `TIFFReadDirectory` calls).
2. **Strip/tile geometry, planar configuration & `BitsPerSample` overflow (`tif_strip.c`,
   `tif_tile.c`, `tif_read.c`, `tif_getimage.c`).**
   Prove `TIFFScanlineSize64`, `TIFFStripSize64`, `TIFFTileSize64`, and `TIFFReadRGBAImage`
   check `width * height * samples * bits` overflow and `PlanarConfig` (`CONTIG` vs. `SEPARATE`)
   buffer sizing without div-by-zero or truncation from `uint64_t` to `tmsize_t`/`uint32_t`.
3. **LZW & CCITT Fax3/Fax4 bit-stream & table bounds (`tif_lzw.c`, `tif_fax3.c`).**
   Prove `LZWDecode` code-table (`CSIZE = 4096+`) / `clear_code` / `free_entp` bounds and
   `Fax3Decode1D`/`2D` run-length state-machine `runs` buffer bounds cannot overrun on adversarial
   bitstreams or zero-length strips.
4. **Predictor stride & `SamplesPerPixel` divisibility (`tif_predict.c`).**
   `horAcc8`/`horAcc16`/`horDiff8`/`fpAcc` assume buffer length `cc` is an exact multiple of
   `stride * sizeof(sample)` and `rowsize`; prove every call validates `cc % stride == 0` and
   never reads/writes past `cp0 + cc` (directly blocking the `CVE-2026-128067` predictor write
   overflow pattern!).
5. **ZIP/Deflate uncompressed-size mismatch (`tif_zip.c`).**
   Prove that `ZIPDecode` / `ZIPEncode` strictly honor `occ` buffer capacity when the embedded
   `zlib` stream expands larger or smaller than expected.

## Bootstrap & Local Commands

When onboarding into `framework/projects.json`: pin `libtiff/` submodule, copy `lean-toolchain`,
start `LibtiffF/Runtime/Ptr.lean` from `framework/lean/StrictPtr.lean`, wire `LibtiffF/Results.lean`
and `project.json`, then run:

```bash
lake --dir projects/libtiff build --wfail LibtiffF LibtiffF.Results
python3 framework/check_project.py libtiff --skip-build
```

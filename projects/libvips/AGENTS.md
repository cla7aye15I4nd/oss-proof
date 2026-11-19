# Working rules (`projects/libvips`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), including the strict
ISO C17 undefined-behaviour policy: no `NULL`, wild or dangling pointer `+ 0`, no `NULL - NULL`, no
cross-object pointer subtraction or comparison, no out-of-bounds pointer formation, no zero-length
`memcpy`/`memset` on invalid pointers, every struct pointer field written before it is read, and no
"benign UB" arguments. The runtime starts from `framework/lean/StrictPtr.lean`.

- **Status:** candidate. Upstream submodule `libvips/` tracks the latest default branch. Not
  registered in `framework/projects.json`; translation and proofs are not done.

## Why it matters

Every Sharp call goes through libvips. Sharp sniffs the input with `vips_foreign_find_load_buffer`
and hands the bytes to whichever libvips loader claims them, so every loader Sharp enables is
reachable from an upload (see [`../sharp/AGENTS.md`](../sharp/AGENTS.md)). Two parsers live inside
libvips itself: the vendored GIF decoder and the EXIF bridge.

## Interfaces to prove (P0)

Only the code Sharp reaches by default:

1. **Format sniffing and buffer sources** — `foreign/foreign.c` (`vips_foreign_find_load_buffer`,
   the `is_a_buffer` / `is_a_source` sniffers of the enabled loaders), `iofuncs/source.c`.
2. **Vendored GIF decoder** — `foreign/libnsgif/gif.c`, `foreign/libnsgif/lzw.c` and its caller
   `foreign/nsgifload.c`: `nsgif_create`, `nsgif_data_scan`, `nsgif_data_complete`,
   `nsgif_get_info`, `nsgif_get_frame_info`, `nsgif_frame_decode`, `nsgif_global_palette`,
   `nsgif_local_palette`, `nsgif_destroy`. All GIF input in Sharp goes through this code.
3. **EXIF bridge** — `foreign/exif.c` (`vips__exif_parse`, `vips__exif_update`), triggered from
   `vips_image_set` in `iofuncs/header.c` whenever a loader attaches an `exif-data` blob.
4. **Loader glue that sizes buffers from header fields** — `foreign/jpeg2vips.c`,
   `foreign/vipspng.c`, `foreign/webp2vips.c`, `foreign/tiff2vips.c` (with `foreign/tiff.c`):
   width × height × bands × sample size, tile and strip sizes, page counts, before any pixel buffer
   is allocated or indexed.
5. **ICC bridge** — `colour/icc_transform.c`, `colour/profile_load.c` (only the glue; lcms2 itself
   is its own project).

## Verification hazards

1. Header-derived geometry multiplied in `int` or `size_t` before allocation or
   `VIPS_REGION_ADDR` indexing.
2. TIFF tiles and strips whose decoded component count or subsampling differs from the directory
   tags (`tiff2vips.c`).
3. libnsgif LZW code table and stack bounds; frame rectangles that exceed the logical screen;
   interlaced row passes; frame disposal against the previous canvas.
4. EXIF entries formatted into strings (`exif_entry_get_value` into fixed buffers), entries with
   bogus component counts, and rebuilding the blob on save.

## Not in scope

The C++ binding layer, SIMD (Highway/Orc) kernels, threaded region evaluation (proofs assume one
thread), and loaders Sharp's prebuilt binary does not enable (magick, pdf, openslide, jp2k, jxl,
fits, ppm, rad, csv, matrix). `vipsload` is reachable in Sharp only from a file path, not a buffer.

## Local commands

```bash
lake --dir projects/libvips build --wfail LibvipsF LibvipsF.Results
python3 framework/check_project.py libvips --skip-build
```

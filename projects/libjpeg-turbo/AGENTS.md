# Working rules (`projects/libjpeg-turbo`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), including the strict
ISO C17 undefined-behaviour policy: no `NULL`, wild or dangling pointer `+ 0`, no `NULL - NULL`, no
cross-object pointer subtraction or comparison, no out-of-bounds pointer formation, no zero-length
`memcpy`/`memset` on invalid pointers, every struct pointer field written before it is read, and no
"benign UB" arguments. The runtime starts from `framework/lean/StrictPtr.lean`.

- **Status:** candidate. Upstream submodule `libjpeg-turbo/` tracks the latest default branch. Not
  registered in `framework/projects.json`; translation and proofs are not done.

## Why it matters

Pillow's wheels bundle libjpeg-turbo (3.2.0 in Pillow 13.0.0). Every JPEG and MPO passed to
`Image.open` is decoded by it through `libImaging/JpegDecode.c`, every JPEG save goes through
`libImaging/JpegEncode.c`, and libtiff uses it for JPEG-compressed TIFF. Sharp uses mozjpeg instead
(see [`../mozjpeg/AGENTS.md`](../mozjpeg/AGENTS.md)).

## Interfaces to prove (P0)

Exactly what Pillow calls:

- **Decode:** `jpeg_std_error`, `jpeg_create_decompress`, `jpeg_read_header`,
  `jpeg_start_decompress`, `jpeg_read_scanlines`, `jpeg_finish_decompress`,
  `jpeg_destroy_decompress`, with Pillow's own buffer source manager and `scale_num / scale_denom`
  set by `Image.draft()` / `thumbnail()`. The standard 8-bit API also accepts lossless (SOF3)
  streams, so `jdlossls.c` and `jddiffct.c` are in scope.
- **Encode:** `jpeg_create_compress`, `jpeg_set_defaults`, `jpeg_set_colorspace`,
  `jpeg_set_quality`, `jpeg_quality_scaling`, `jpeg_add_quant_table`, `jpeg_simple_progression`,
  `jpeg_c_set_int_param`, `jpeg_suppress_tables`, `jpeg_write_tables`, `jpeg_start_compress`,
  `jpeg_write_marker`, `jpeg_write_scanlines`, `jpeg_finish_compress`, `jpeg_destroy_compress`.

## Verification hazards

1. Fatal errors leave through `error_exit` and `longjmp`; prove `jpeg_destroy_*` releases every
   pool block from any failure point.
2. Output geometry after `jpeg_start_decompress` (`output_width`, `output_components`) when the
   caller asked for a scaled or lossless decode.
3. Huffman bit buffer refill, restart markers, truncated input and progressive coefficient buffers.
4. Scaled IDCT, upsampling and merged upsampling for every sampling factor and odd image size.
5. `jmemmgr.c` pool allocator and virtual arrays.

## Not in scope

SIMD (build with `-DWITH_SIMD=0`), the TurboJPEG API (Pillow does not call it), 12- and 16-bit
sample APIs, command-line tools, and image-quality claims.

## Local commands

```bash
lake --dir projects/libjpeg-turbo build --wfail LibjpegTurboF LibjpegTurboF.Results
python3 framework/check_project.py libjpeg-turbo --skip-build
```

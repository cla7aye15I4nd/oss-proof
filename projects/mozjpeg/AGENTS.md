# Working rules (`projects/mozjpeg`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), including the strict
ISO C17 undefined-behaviour policy: no `NULL`, wild or dangling pointer `+ 0`, no `NULL - NULL`, no
cross-object pointer subtraction or comparison, no out-of-bounds pointer formation, no zero-length
`memcpy`/`memset` on invalid pointers, every struct pointer field written before it is read, and no
"benign UB" arguments. The runtime starts from `framework/lean/StrictPtr.lean`.

- **Status:** candidate. Upstream submodule `mozjpeg/` tracks the latest default branch. Not
  registered in `framework/projects.json`; translation and proofs are not done.

## Why it matters

mozjpeg is the only JPEG implementation inside Sharp's prebuilt libvips (the binary identifies
itself as `mozjpeg version 5.0.0`, built from the commit this submodule tracks). Every JPEG upload
to Sharp is decoded by it, every `.jpeg()` output is encoded by it, and libtiff uses it for
JPEG-compressed TIFF. mozjpeg is a fork of libjpeg-turbo, but 52 of its 70 codec sources differ from
current libjpeg-turbo (including `jdapistd.c`, `jdmaster.c`, `jdcolor.c`, `jdmerge.c`,
`jdsample.c`), so the [`libjpeg-turbo`](../libjpeg-turbo/AGENTS.md) proofs do not cover it.

## Interfaces to prove (P0)

Exactly what libvips calls (`foreign/jpeg2vips.c`, `foreign/vips2jpeg.c`):

- **Decode:** `jpeg_std_error`, `jpeg_create_decompress`, `jpeg_save_markers`, `jpeg_read_header`,
  `jpeg_calc_output_dimensions`, `jpeg_has_multiple_scans`, `jpeg_start_decompress`,
  `jpeg_read_scanlines`, `jpeg_finish_decompress`, `jpeg_destroy_decompress`, with
  `scale_num / scale_denom` set for shrink-on-load (Sharp asks for 1/2, 1/4, 1/8) and libvips'
  own memory/stream source manager.
- **Encode:** `jpeg_create_compress`, `jpeg_set_defaults`, `jpeg_set_quality`,
  `jpeg_simple_progression`, `jpeg_c_bool_param_supported`, `jpeg_c_int_param_supported`,
  `jpeg_c_set_bool_param`, `jpeg_c_set_int_param` (mozjpeg's trellis / scan-optimisation knobs),
  `jpeg_start_compress`, `jpeg_write_marker`, `jpeg_write_m_header`, `jpeg_write_m_byte`,
  `jpeg_write_scanlines`, `jpeg_finish_compress`, `jpeg_destroy_compress`.

## Verification hazards

1. Fatal errors leave through `error_exit` and `longjmp` back to the caller's `setjmp`; model the
   jump as a structured abort and prove `jpeg_destroy_*` releases every pool block from any
   failure point.
2. `jmemmgr.c` pool allocator and the 2-D sample / coefficient arrays it hands out.
3. Huffman bit buffer refill, restart markers, truncated input and progressive scan parameters.
4. Scaled IDCT, upsampling and merged upsampling for every sampling factor and odd image size.
5. mozjpeg's encoder additions: trellis quantisation, scan optimisation and its larger
   coefficient buffers.

## Not in scope

SIMD (build with `-DWITH_SIMD=0`), the TurboJPEG API (`-DWITH_TURBOJPEG=FALSE` in Sharp's build),
command-line tools, and image-quality claims.

## Local commands

```bash
lake --dir projects/mozjpeg build --wfail MozjpegF MozjpegF.Results
python3 framework/check_project.py mozjpeg --skip-build
```

# Working rules (`projects/openjpeg`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), including the strict
ISO C17 undefined-behaviour policy: no `NULL`, wild or dangling pointer `+ 0`, no `NULL - NULL`, no
cross-object pointer subtraction or comparison, no out-of-bounds pointer formation, no zero-length
`memcpy`/`memset` on invalid pointers, every struct pointer field written before it is read, and no
"benign UB" arguments. The runtime starts from `framework/lean/StrictPtr.lean`.

- **Status:** candidate. Upstream submodule `openjpeg/` tracks the latest default branch. Not
  registered in `framework/projects.json`; translation and proofs are not done.

## Why it matters

Pillow's wheels bundle openjpeg (2.5.4 in Pillow 13.0.0) and `Image.open` sniffs JPEG 2000 (`.jp2`
and raw codestreams) under any file name, so the decoder is reachable from any upload through
`libImaging/Jpeg2KDecode.c`. Sharp's prebuilt binary does not enable JPEG 2000.

## Interfaces to prove (P0)

Exactly what Pillow calls:

- **Decode (tile by tile):** `opj_set_default_decoder_parameters`, `opj_create_decompress`,
  `opj_set_error_handler`, `opj_set_warning_handler`, `opj_set_info_handler`,
  `opj_setup_decoder`, `opj_stream_create`, `opj_stream_set_read_function`,
  `opj_stream_set_skip_function`, `opj_stream_set_seek_function`, `opj_stream_set_user_data`,
  `opj_stream_set_user_data_length`, `opj_read_header`, `opj_read_tile_header`,
  `opj_decode_tile_data`, `opj_end_decompress`, `opj_stream_destroy`, `opj_destroy_codec`,
  `opj_image_destroy`.
- **Encode:** `opj_set_default_encoder_parameters`, `opj_image_create`, `opj_create_compress`,
  `opj_encoder_set_extra_options`, `opj_setup_encoder`, `opj_stream_set_write_function`,
  `opj_start_compress`, `opj_write_tile`, `opj_end_compress`.

## Verification hazards

1. `SIZ`, `COD`, `COC`, `QCD` marker values: image and tile origins, subsampling, decomposition
   levels, code-block sizes, and the 32-bit products derived from them.
2. Packet headers, tag trees and code-block segment lengths (tier 2).
3. MQ decoder and bit-plane passes against the code-block buffers (tier 1).
4. Inverse wavelet transform on one-pixel and odd-sized sub-bands.
5. JP2 palette (`pclr`), component mapping (`cmap`) and channel definitions against the
   allocated components.

## Not in scope

Threads (build without them), SIMD transforms, the high-throughput (HTJ2K) decoder unless
Pillow's build enables it, and the command-line tools.

## Local commands

```bash
lake --dir projects/openjpeg build --wfail OpenjpegF OpenjpegF.Results
python3 framework/check_project.py openjpeg --skip-build
```

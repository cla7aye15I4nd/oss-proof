# Working rules (`projects/mozjpeg`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), which is
authoritative on proof soundness, allowed axioms and the strict ISO C17 undefined-behaviour policy.
The runtime starts from `framework/lean/StrictPtr.lean`.

**Status:** candidate. Upstream submodule `mozjpeg/` tracks the latest default branch; not
registered in `framework/projects.json`; translation and proofs are not done.

## Tier 0

Tier 0 is the code that turns untrusted bytes into pixels or metadata on a default path. It is the
whole scope of this project.

**How it is reached.** mozjpeg is the only JPEG implementation inside Sharp's prebuilt libvips:
`sharp(jpeg).resize(800).toBuffer()` → libvips `foreign/jpeg2vips.c` `read_jpeg_header` /
`read_jpeg_image`, and JPEG-compressed TIFF through `foreign/tiff2vips.c`
`rtiff_decompress_jpeg_run`. 52 of its 70 codec sources differ from current libjpeg-turbo, so the
libjpeg-turbo proofs do not cover it.

**Functions:** `jpeg_std_error`, `jpeg_create_decompress`, `jpeg_save_markers`,
`jpeg_read_header`, `jpeg_calc_output_dimensions`, `jpeg_start_decompress`,
`jpeg_read_scanlines`, `jpeg_finish_decompress`, `jpeg_destroy_decompress`, with
`scale_num / scale_denom` of 1/2, 1/4 and 1/8 (Sharp's shrink-on-load) and libvips' source manager.

**What the proofs must cover.**

1. `error_exit` → `longjmp` from any failure point leaves no leaked pool block once
   `jpeg_destroy_decompress` runs.
2. Huffman bit-buffer refill, restart markers, truncated input and progressive scans stay inside
   the coefficient buffers.
3. Scaled IDCT, upsampling and merged upsampling stay inside the output rows for every sampling
   factor and odd size.

## Local commands

```bash
lake --dir projects/mozjpeg build --wfail MozjpegF MozjpegF.Results
python3 framework/check_project.py mozjpeg --skip-build
```

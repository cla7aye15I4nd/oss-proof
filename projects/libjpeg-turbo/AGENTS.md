# Working rules (`projects/libjpeg-turbo`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), which is
authoritative on proof soundness, allowed axioms and the strict ISO C17 undefined-behaviour policy.
The runtime starts from `framework/lean/StrictPtr.lean`.

**Status:** candidate. Upstream submodule `libjpeg-turbo/` tracks the latest default branch; not
registered in `framework/projects.json`; translation and proofs are not done.

## Tier 0

Tier 0 is the code that turns untrusted bytes into pixels or metadata on a default path. It is the
whole scope of this project.

**How it is reached.** Pillow's wheels bundle libjpeg-turbo: `Image.open(jpeg).thumbnail(...)` →
`JpegImageFile.draft` → `ImageFile.load` → `src/decode.c` `PyImaging_JpegDecoderNew` →
`src/libImaging/JpegDecode.c` `ImagingJpegDecode`; libtiff also uses it for JPEG-compressed TIFF.
Sharp uses mozjpeg instead.

**Functions:** `jpeg_std_error`, `jpeg_create_decompress`, `jpeg_read_header`,
`jpeg_start_decompress`, `jpeg_read_scanlines`, `jpeg_finish_decompress`,
`jpeg_destroy_decompress`, with Pillow's buffer source manager and the `scale_num / scale_denom`
set by `draft()`. The 8-bit API also accepts lossless (SOF3) streams, so `jdlossls.c` and
`jddiffct.c` are included.

**What the proofs must cover.**

1. `error_exit` → `longjmp` from any failure point leaves no leaked pool block once
   `jpeg_destroy_decompress` runs.
2. `output_width` and `output_components` after `jpeg_start_decompress` are what the caller's row
   buffer can hold, including scaled and lossless decodes.
3. Huffman refill, restart markers, progressive scans, scaled IDCT and upsampling stay in bounds.

## Local commands

```bash
lake --dir projects/libjpeg-turbo build --wfail LibjpegTurboF LibjpegTurboF.Results
python3 framework/check_project.py libjpeg-turbo --skip-build
```

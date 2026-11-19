# Working rules (`projects/libpng`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), including the strict
ISO C17 undefined-behaviour policy: no `NULL`, wild or dangling pointer `+ 0`, no `NULL - NULL`, no
cross-object pointer subtraction or comparison, no out-of-bounds pointer formation, no zero-length
`memcpy`/`memset` on invalid pointers, every struct pointer field written before it is read, and no
"benign UB" arguments. The runtime starts from `framework/lean/StrictPtr.lean`.

- **Status:** candidate. Upstream submodule `libpng/` tracks the latest default branch. Not
  registered in `framework/projects.json`; translation and proofs are not done.

## Why it matters

Sharp's prebuilt libvips is built with `-Dspng=disabled`, and current libvips prefers libpng over
libspng anyway, so **every PNG upload to Sharp and every `.png()` output goes through libpng**
(1.6.58 in Sharp 0.35.5) via `libvips/foreign/vipspng.c`, with zlib-ng underneath. Pillow does not
use libpng for PNG.

## Interfaces to prove (P0)

Exactly what `vipspng.c` calls:

- **Read:** `png_sig_cmp`, `png_create_read_struct`, `png_create_info_struct`, `png_set_read_fn`,
  `png_set_user_limits`, `png_set_chunk_malloc_max`, `png_set_chunk_cache_max`,
  `png_set_crc_action`, `png_set_option`, `png_read_info`, `png_get_IHDR`, `png_get_valid`,
  `png_get_channels`, `png_get_rowbytes`, `png_get_interlace_type`, `png_get_iCCP`,
  `png_get_eXIf_1`, `png_get_text`, `png_get_pHYs`, `png_get_bKGD`, `png_get_cICP`,
  `png_get_cLLI_fixed`, `png_get_acTL`, `png_get_next_frame_fcTL`,
  `png_get_first_frame_is_hidden`, `png_get_io_ptr`, the transforms `png_set_palette_to_rgb`,
  `png_set_expand_gray_1_2_4_to_8`, `png_set_tRNS_to_alpha`, `png_set_packing`, `png_set_swap`,
  `png_set_add_alpha`, `png_set_interlace_handling`, then `png_read_update_info`,
  `png_read_row`, `png_read_image`, `png_read_frame_head`, `png_read_end`,
  `png_destroy_read_struct`.
- **Write:** `png_create_write_struct`, `png_set_write_fn`, `png_set_IHDR`, `png_set_PLTE`,
  `png_set_tRNS`, `png_set_iCCP`, `png_set_eXIf_1`, `png_set_text`, `png_set_pHYs`,
  `png_set_cICP`, `png_set_cLLI_fixed`, `png_set_acTL`, `png_set_compression_level`,
  `png_set_filter`, `png_write_info`, `png_write_row`, `png_write_rows`,
  `png_write_frame_head`, `png_write_frame_tail`, `png_write_end`, `png_destroy_write_struct`.
- **Shared:** `png_error`, `png_jmpbuf`, `png_malloc`, `png_free`.

## Verification hazards

1. Errors leave through `png_error` and `longjmp`; prove the destroy functions release every
   partial allocation from any failure point.
2. Row buffer size against `pixel_depth` and `rowbytes` after the transform combination above,
   including interlaced passes and sub-byte depths.
3. Compressed ancillary chunks (`iCCP`, `zTXt`, `iTXt`) inflated under `chunk_malloc_max`.
4. Animated PNG frame control: frame rectangles against the canvas, sequence numbers.
5. Pointers returned by `png_get_*` stay valid until the struct is destroyed.

## Not in scope

SIMD filter code (build without hardware optimisations), the simplified `png_image_*` API and the
progressive reader (libvips calls neither), `stdio` helpers, and colour accuracy.

## Local commands

```bash
lake --dir projects/libpng build --wfail LibpngF LibpngF.Results
python3 framework/check_project.py libpng --skip-build
```

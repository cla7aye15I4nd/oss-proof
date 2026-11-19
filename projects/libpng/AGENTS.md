# Working rules (`projects/libpng`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), which is
authoritative on proof soundness, allowed axioms and the strict ISO C17 undefined-behaviour policy.
The runtime starts from `framework/lean/StrictPtr.lean`.

**Status:** candidate. Upstream submodule `libpng/` tracks the latest default branch; not
registered in `framework/projects.json`; translation and proofs are not done.

## Tier 0

Tier 0 is the code that turns untrusted bytes into pixels or metadata on a default path. It is the
whole scope of this project.

**How it is reached.** Sharp's libvips is built with `-Dspng=disabled`, so every PNG goes through
libpng: `sharp(png).metadata()` or any pipeline → libvips `foreign/vipspng.c` `read_new` →
`png2vips_header` → `png2vips_generate`. Pillow does not use libpng.

**Functions:** `png_sig_cmp`, `png_create_read_struct`, `png_create_info_struct`,
`png_set_read_fn`, `png_set_user_limits`, `png_set_chunk_malloc_max`, `png_read_info` (and the
chunk handlers it runs: `IHDR`, `PLTE`, `tRNS`, `iCCP`, `eXIf`, `tEXt` / `zTXt` / `iTXt`, `pHYs`),
`png_get_IHDR`, `png_get_iCCP`, `png_get_eXIf_1`, `png_get_text`, the transforms
`png_set_palette_to_rgb`, `png_set_expand_gray_1_2_4_to_8`, `png_set_tRNS_to_alpha`,
`png_set_packing`, `png_set_interlace_handling`, then `png_read_update_info`, `png_read_row`,
`png_read_image`, `png_read_end`, `png_destroy_read_struct`. Inflation goes to zlib-ng.

**What the proofs must cover.**

1. `png_error` → `longjmp` from any chunk handler leaves no leaked allocation once
   `png_destroy_read_struct` runs.
2. The row buffer covers `rowbytes` after every combination of the transforms above, including
   interlaced passes and sub-byte depths.
3. Compressed chunks are inflated within `chunk_malloc_max`, and palette indices stay inside the
   palette.

## Local commands

```bash
lake --dir projects/libpng build --wfail LibpngF LibpngF.Results
python3 framework/check_project.py libpng --skip-build
```

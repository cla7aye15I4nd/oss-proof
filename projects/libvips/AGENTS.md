# Working rules (`projects/libvips`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), which is
authoritative on proof soundness, allowed axioms and the strict ISO C17 undefined-behaviour policy.
The runtime starts from `framework/lean/StrictPtr.lean`.

**Status:** candidate. Upstream submodule `libvips/` tracks the latest default branch; not
registered in `framework/projects.json`; translation and proofs are not done.

## Tier 0

Tier 0 is the code that turns untrusted bytes into pixels or metadata on a default path. It is the
whole scope of this project.

**How it is reached.** Every Sharp call: `sharp(upload).toBuffer()` → Sharp `src/common.cc`
`OpenInput` → `vips_foreign_find_load_buffer` → the loader that claims the bytes.

**Functions:**

- Format sniffing: `vips_foreign_find_load_buffer` and the `is_a` / `is_a_source` checks of the
  loaders Sharp enables (`foreign/foreign.c`).
- Loader glue that sizes buffers from header fields: `read_jpeg_header`, `read_jpeg_image`
  (`foreign/jpeg2vips.c`); `read_new`, `png2vips_header`, `png2vips_generate`
  (`foreign/vipspng.c`); `read_header`, `read_frame` (`foreign/webp2vips.c`);
  `vips__tiff_openin_source` (`foreign/tiff.c`), `rtiff_header_read`, `rtiff_strip_read`,
  `rtiff_read_tile`, `rtiff_decompress_jpeg_run` (`foreign/tiff2vips.c`).
- Vendored GIF decoder, the only GIF code in Sharp: `vips_foreign_load_nsgif_header`,
  `vips_foreign_load_nsgif_generate` (`foreign/nsgifload.c`) and `nsgif_create`,
  `nsgif_data_scan`, `nsgif_frame_decode`, `nsgif_destroy` (`foreign/libnsgif/gif.c`, `lzw.c`).
- EXIF bridge: `vips_image_set` (`iofuncs/header.c`) → `vips__exif_parse` (`foreign/exif.c`).
- ICC bridge: `vips_icc_transform` and its profile loading (`colour/icc_transform.c`).

**What the proofs must cover.**

1. Width × height × bands × sample size, tile and strip sizes, and page counts never overflow
   before allocation or region indexing.
2. TIFF tiles whose decoded components disagree with the directory tags cannot overrun the tile
   buffer.
3. libnsgif's LZW tables, frame rectangles against the screen, and interlaced passes stay in
   bounds.
4. EXIF entries are formatted into fixed buffers without over-reads.

## Local commands

```bash
lake --dir projects/libvips build --wfail LibvipsF LibvipsF.Results
python3 framework/check_project.py libvips --skip-build
```

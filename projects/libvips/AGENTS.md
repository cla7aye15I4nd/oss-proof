# Working rules (`projects/libvips`)

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

## Scope (`LibvipsF`)

- **Upstream source:** `libvips/` pinned submodule (`https://github.com/libvips/libvips`) +
  `patches/*.patch` in name order.
- **Target configuration:** portable scalar x86_64 Linux LP64 C core build (without Highway/Orc
  SIMD acceleration, single-threaded region evaluation `vips_concurrency_set(1)`), focused on the
  **pure-C untrusted-input parsing, format-loader/saver, metadata, color-bridge, and pixel-buffer
  subsystems** directly invoked by **Sharp (Node.js)**, `pyvips`, `ruby-vips`, `govips`, and
  `netvips`.
- **Verification goal:** full safety (no ISO C17 undefined behaviour, no integer overflow in
  dimension/stride/tile/band calculations, no heap buffer overflow, no out-of-bounds read/write,
  no use-after-free or leak across error unwinding, stated write frame, and termination) of the
  pure-C foreign loaders, savers, vendored `libnsgif`, EXIF/ICC bridges, and region-geometry core.

## Real-World Usage Paths & Function Priority

`libvips` is a demand-driven, streaming image-processing engine with ~200k LOC total, but real-world
security exposure (especially via Node.js **Sharp**) concentrates heavily in **four C subsystems**
that directly touch untrusted bytes and raw pixel buffers — confirmed directly by the 2026 CVE wave:
- **CVE-2026-33327 (`libvips/foreign/vipsload.c` / `iofuncs/header.c`):** Integer overflow in
  dimension calculations when loading crafted native `.vips` files -> heap buffer overflow.
- **CVE-2026-35591 (`libvips/foreign/tiffload.c`):** Buffer overflow when decoding JPEG/JPEG2000-encoded
  tiles inside TIFF files due to channel-count / tile-dimension mismatch.
- **CVE-2026-35590 (`libvips/foreign/exif.c`):** Out-of-bounds / range-check flaw when parsing
  untrusted EXIF tag structures prior to or alongside `libexif` calls.
- **CVE-2026-33328 / `nsgifload.c` + vendored `libnsgif`:** Crafted animated GIF dimension, frame
  disposal, and LZW/canvas buffer hazards.

### Tier 1 (P0) — Untrusted Format Sniffing, Loaders, Metadata & Vendored GIF Decoder (Prove First)

1. **Format dispatcher, source/target streaming & native `.vips` header (`libvips/foreign/foreign.c`,
   `libvips/foreign/vipsload.c`, `libvips/iofuncs/source.c`, `libvips/iofuncs/target.c`,
   `libvips/iofuncs/header.c`, `libvips/iofuncs/region.c`, `libvips/iofuncs/memory.c`):**
   `vips_foreign_find_load_buffer`, `vips_foreign_find_load_source`, `vips_vipsload_source`
   (`CVE-2026-33327`), `vips_image_init_fields`, `vips_region_buffer`, `VIPS_IMAGE_SIZEOF_LINE` /
   `VIPS_IMAGE_SIZEOF_IMAGE` / `VIPS_REGION_ADDR` overflow-free geometry arithmetic.
2. **Vendored `libnsgif` GIF decoder & wrapper (`libvips/foreign/libnsgif/gif.c`,
   `libvips/foreign/libnsgif/lzw.c`, `libvips/foreign/nsgifload.c`):**
   `nsgif_create`, `nsgif_data_scan`, `nsgif_frame_decode`, `nsgif_destroy`, `vips_gifload_buffer`,
   `vips_gifload_source`. *(Pure C, self-contained, directly bundled inside `libvips` — Sharp relies
   exclusively on this code for ALL GIF decoding!)*
3. **EXIF & ICC bridges (`libvips/foreign/exif.c`, `libvips/colour/icc_transform.c`):**
   `vips__exif_parse`, `vips__exif_update`, `vips_icc_import`, `vips_icc_export`,
   `vips_icc_transform` (`CVE-2026-35590`; bridges untrusted blobs to `libexif` and `lcms2`).
4. **TIFF, JPEG, PNG (`libspng`), WebP loaders (`libvips/foreign/tiffload.c`, `jpegload.c`,
   `jpeg2vips.c`, `spngload.c`, `webpload.c`, `webp2vips.c`):**
   `vips_tiffload_buffer`/`_source` (`CVE-2026-35591` tile/strip channel validation!),
   `vips_jpegload_buffer`/`_source` (including shrink-on-load `shrink=2/4/8` & EXIF/ICC/XMP
   extraction), `vips_spngload_buffer`/`_source`, `vips_webpload_buffer`/`_source` (still +
   animated demux).

### Tier 2 (P1) — Format Savers (Compression/Output Paths) & Pure-C Resampling / Conversion

1. **Format savers (`libvips/foreign/jpegsave.c`, `vips2jpeg.c`, `spngsave.c`, `webpsave.c`,
   `vips2webp.c`, `tiffsave.c`, `vips2tiff.c`, `cgifsave.c`):**
   `vips_jpegsave_buffer`/`_target`, `vips_spngsave_buffer`/`_target`, `vips_webpsave_buffer`/
   `_target`, `vips_tiffsave_buffer`/`_target`, `vips_gifsave_buffer`/`_target` — verifying pixel
   row-buffer sizing, band/format packing, metadata injection (EXIF/ICC/XMP), and error cleanup.
2. **Thumbnail & integer shrink/geometry ops (`libvips/resample/thumbnail.c`, `resize.c`,
   `shrink.c`, `shrinkh.c`, `shrinkv.c`, `libvips/conversion/extract.c`, `embed.c`, `rot.c`,
   `autorot.c`, `bandjoin.c`, `flatten.c`):**
   `vips_thumbnail_buffer`, `vips_resize`, `vips_shrink`, `vips_extract_area`, `vips_embed`,
   `vips_autorot`, `vips_flatten`.

### Explicitly Not Planned

- External codec internals verified in their own projects (`libjpeg-turbo`, `libspng`, `libwebp`,
  `libtiff`, `libexif`, `lcms2`, `cgif`, `expat`, `zlib`, `libarchive`, `freetype` — modeled at
  their proved C ABI contracts when verifying `libvips` glue).
- C++ wrapper & C++ template kernels (`cplusplus/`, `libvips/resample/reduceh.cpp`/`reducev.cpp`
  Highway SIMD kernels, `affine.cpp`), `heifload.c`/`heifsave.c` (`libheif` C++ glue), exotic/scientific
  loaders not enabled in Sharp (`openslide`, `fits`, `mat`, `nifti`, `cfitsio`, `magick`, `poppler`,
  `pdfium`, `jxl`, `rad`, `ppm`, `analyze`, `csv`, `matrix`), GLib/GObject internals, and CLI tools.

## Library-Specific Verification Hazards (No Shortcuts)

1. **Image dimension, `bands`, `sizeof_pel`, and multi-page `page-height` integer overflows
   (`vipsload.c`, `header.c`, `region.c`, `tiffload.c` — `CVE-2026-33327`, `CVE-2026-35591`).**
   Every loader computes `width * height * bands * sizeof(band_fmt)` and tile/strip buffer sizes.
   Prove strict 64-bit / `size_t` overflow checks before every allocation and before indexing
   `VIPS_REGION_ADDR(reg, x, y)`.
2. **TIFF embedded JPEG/J2K tile channel-count mismatches (`tiffload.c` — `CVE-2026-35591`).**
   When TIFF strips/tiles carry compressed payloads whose decoded sample count or subsampling
   differs from the IFD `SamplesPerPixel` / `Photometric` tags, prove destination tile buffers
   cannot be overrun.
3. **Vendored `libnsgif` LZW dictionary & animated frame-disposal clipping (`libnsgif/gif.c`,
   `libnsgif/lzw.c`, `nsgifload.c`).**
   Prove that LZW code table indices (`<= 4096`), `clear_code` resets, sub-frame `(left, top, width,
   height)` coordinates against logical screen canvas bounds, and interlaced row passes never write
   outside the RGBA frame buffer.
4. **EXIF tag & IFD boundary parsing (`libvips/foreign/exif.c` — `CVE-2026-35590`).**
   Prove strict length/offset/NUL-termination validation when reading, mutating, and re-serializing
   EXIF blobs across `vips__exif_parse` and `vips__exif_update`.
5. **Custom `VipsSource` / `VipsTarget` buffer & GObject error-unwinding cleanup.**
   Prove that truncated inputs, short reads, and mid-pipeline allocation failures never leave
   dangling pointers in `VipsForeignLoad` / `VipsForeignSave` structs or double-free codec handles.

## Bootstrap & Local Commands

When onboarding into `framework/projects.json`: pin `libvips/` submodule, copy `lean-toolchain`,
start `LibvipsF/Runtime/Ptr.lean` from `framework/lean/StrictPtr.lean`, model external codec &
GLib allocator contracts cleanly, wire `LibvipsF/Results.lean` and `project.json`, then run:

```bash
lake --dir projects/libvips build --wfail LibvipsF LibvipsF.Results
python3 framework/check_project.py libvips --skip-build
```

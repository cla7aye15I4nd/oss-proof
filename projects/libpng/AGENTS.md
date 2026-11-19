# Working rules (`projects/libpng`)

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

- **Status:** Upstream submodule `libpng/` pinned (not yet registered in `framework/projects.json`;
  Lean runtime bootstrap, C translation, and safety proofs **Not done**).

## Scope (`LibpngF`)

- **Upstream source:** `libpng/` pinned submodule (`https://github.com/pnggroup/libpng`) +
  `patches/*.patch` in name order.
- **Target configuration:** portable scalar x86_64 Linux LP64 static build (`-DPNG_HARDWARE_OPTIMIZATIONS=OFF`
  / `-DPNG_INTEL_SSE_OPT=0`, linking our already-verified `zlib` from `projects/zlib`, default
  allocator).
- **Verification goal:** full safety (no ISO C17 undefined behaviour, no heap buffer overflow or
  over-read in row transforms/simplified API/quantization, no pointer-aliasing UAF in chunk
  setters, no `setjmp`/`longjmp` leak, stated write frame, and termination) across **both PNG
  decoding AND PNG encoding** public APIs in `png.h`.

## Real-World Usage Paths & Function Priority

While Sharp uses `libspng` and Pillow uses Python + `zlib`, **`libpng` remains the universal C PNG
engine** across **Chromium/Blink**, **Firefox/Gecko**, **Cairo** (also linked into `sharp-libvips`
for SVG rasterization!), **OpenCV**, **matplotlib**, **ImageMagick**, **GTK / Qt / Skia**,
**Android**, and Linux desktops — and suffered a **major 2025–2026 CVE wave**:
- **CVE-2025-65018 (`pngread.c` `png_combine_row` / `png_image_finish_read`):** Heap buffer
  overflow in the Simplified API!
- **CVE-2026-22695 (`pngread.c` `png_image_read_direct_scaled`):** Heap buffer over-read on
  interlaced 16-bit -> 8-bit PNGs with non-minimal row strides (regression of `CVE-2025-65018` fix).
- **CVE-2025-64720 (`pngread.c`, `pngrtran.c` `png_image_read_composite`):** OOB read / heap
  overflow from palette premultiplication when `PNG_FLAG_OPTIMIZE_ALPHA` is set.
- **CVE-2026-25646 & CVE-2025-64505 (`pngrtran.c` `png_set_quantize`, `png_do_quantize`):**
  Legacy heap buffer overflow / OOB read / infinite loop when quantizing malformed palettes.
- **CVE-2026-34757 & CVE-2026-33416 (`pngset.c` `png_set_PLTE`, `png_set_tRNS`, `png_set_hIST`):**
  Use-after-free & pointer-aliasing corruption when passing `png_get_*` pointers back to `png_set_*`.

### Tier 1 (P0) — Standard Read, Progressive Read, Simplified Read & Chunk Setters (Prove First)

1. **Core lifecycle, header & sequential reader (`png.c`, `pngread.c`, `pngrutil.c`, `pngrio.c`,
   `pngget.c`, `pngset.c`, `pngmem.c`, `pngerror.c`):**
   `png_create_read_struct`, `png_create_info_struct`, `png_set_read_fn`, `png_sig_cmp`,
   `png_read_info`, `png_read_update_info`, `png_read_row`, `png_read_rows`, `png_read_image`,
   `png_read_end`, `png_destroy_read_struct`, plus all `png_get_*` / `png_set_*` chunk accessors
   (`png_set_PLTE`, `png_set_tRNS`, `png_set_hIST`, `png_set_iCCP`, `png_set_eXIf_1` — directly
   covering `CVE-2026-34757` and `CVE-2026-33416`!).
2. **Read transforms (`pngrtran.c`, `pngtrans.c`):**
   `png_set_palette_to_rgb`, `png_set_expand_gray_1_2_4_to_8`, `png_set_tRNS_to_alpha`,
   `png_set_strip_16`, `png_set_strip_alpha`, `png_set_gray_to_rgb`, `png_set_rgb_to_gray`,
   `png_set_filler`, `png_set_bgr`, `png_set_swap`, `png_set_interlace_handling`,
   `png_set_background`, `png_set_alpha_mode`, `png_set_quantize` (`CVE-2026-25646`, `CVE-2025-64505`).
3. **Progressive streaming reader (`pngpread.c` — browser/HTTP primary path):**
   `png_set_progressive_read_fn`, `png_process_data`, `png_progressive_combine_row`.
4. **Simplified API (`pngread.c` — site of `CVE-2025-65018`, `CVE-2025-64720`, `CVE-2026-22695`):**
   `png_image_begin_read_from_memory`, `png_image_finish_read`, `png_image_free`.

### Tier 1 (P0) — Standard & Simplified Write/Encode Path

1. **Sequential & simplified PNG writer (`pngwrite.c`, `pngwutil.c`, `pngwtran.c`, `pngwio.c`):**
   `png_create_write_struct`, `png_set_write_fn`, `png_set_IHDR`, `png_write_info`, `png_write_row`,
   `png_write_rows`, `png_write_image`, `png_write_end`, `png_destroy_write_struct`,
   `png_image_write_to_memory`, `png_set_compression_level`, `png_set_filter`.

### Explicitly Not Planned

- SIMD filter directories (`intel/`, `arm/`, `mips/`, `powerpc/`, `loongarch/`).
- Legacy `stdio` convenience wrappers (`png_init_io` beyond callback abstraction), `contrib/`
  example tools, and visual gamma/colorimetric accuracy proofs beyond safety invariants.

## Verified Translation Units

- `png.h`, `pngconf.h`, `pngpriv.h`, `pngstruct.h`, `pnginfo.h`
- `png.c`, `pngerror.c`, `pngget.c`, `pngmem.c`, `pngpread.c`, `pngread.c`, `pngrio.c`,
  `pngrtran.c`, `pngrutil.c`, `pngset.c`, `pngtrans.c`, `pngwio.c`, `pngwrite.c`, `pngwtran.c`,
  `pngwutil.c`
*(Linked against the proved `zlib` C ABI contract from `projects/zlib/`.)*

## Library-Specific Verification Hazards (No Shortcuts)

1. **Simplified API row stride, 16-to-8 scaling & alpha compositing (`pngread.c`, `pngrtran.c` —
   `CVE-2025-65018`, `CVE-2025-64720`, `CVE-2026-22695`).**
   Prove that `png_image_read_direct_scaled`, `png_image_read_composite`, and `png_combine_row`
   never over-read or overwrite caller buffers for positive/negative `row_stride`, interlaced Adam7
   passes, 1/2/4/8/16-bit depths, and `PNG_FLAG_OPTIMIZE_ALPHA`.
2. **Transform-pipeline row-buffer expansion (`pngrtran.c`).**
   Combining multiple `png_set_*` transforms (expand + strip + filler + quantize + interlace) changes
   `pixel_depth` and `rowbytes` dynamically; prove `row_buf` allocation in `png_read_start_row`
   strictly dominates every intermediate transform buffer size, including `png_set_quantize` /
   `png_do_quantize` (`CVE-2026-25646`, `CVE-2025-64505`).
3. **Aliasing between `png_get_*` and `png_set_*` (`pngset.c` — `CVE-2026-34757`, `CVE-2026-33416`).**
   Prove that `png_set_PLTE`, `png_set_tRNS`, `png_set_hIST`, `png_set_iCCP`, and `png_set_text`
   handle self-aliasing (`info_ptr` passing its own buffer back) without use-after-free or
   double-free across `png_free_data`.
4. **`setjmp`/`longjmp` unwinding (`pngerror.c`).**
   Every `png_error` longjmps out of deep chunk/transform frames; prove `png_destroy_read_struct`
   and `png_destroy_write_struct` safely reclaim all partial allocations without leaks or UAF.
5. **Progressive push-parser state & `iCCP`/`zTXt`/`iTXt` inflate loops (`pngpread.c`, `pngrutil.c`).**
   Prove arbitrary 1-byte `png_process_data` splits and `user_chunk_malloc_max` bounds cannot
   overflow `save_buffer` or leak inflated buffers.

## Bootstrap & Local Commands

When onboarding into `framework/projects.json`: copy `lean-toolchain`,
start `LibpngF/Runtime/Ptr.lean` from `framework/lean/StrictPtr.lean`, wire `LibpngF/Results.lean`
and `project.json`, then run:

```bash
lake --dir projects/libpng build --wfail LibpngF LibpngF.Results
python3 framework/check_project.py libpng --skip-build
```

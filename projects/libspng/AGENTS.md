# Working rules (`projects/libspng`)

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

- **Status:** Upstream submodule `libspng/` pinned (not yet registered in `framework/projects.json`;
  Lean runtime bootstrap, C translation, and safety proofs **Not done**).

## Scope (`LibspngF`)

- **Upstream source:** `libspng/` pinned submodule (`https://github.com/randy408/libspng`) +
  `patches/*.patch` in name order.
- **Target configuration:** portable scalar x86_64 Linux LP64 build (`-DSPNG_DISABLE_OPT` — disables
  SSE2/SSSE3/SSE4.1/NEON scanline filter intrinsics; links `zlib` — which is **already proved safe
  in `projects/zlib`**!).
- **Why `libspng` is the single highest-ROI Sharp image-codec proof target:**
  **Sharp (`sharp-libvips`) uses `libspng` — NOT `libpng` — for ALL PNG decoding and encoding!**
  The entire library is **one single clean C file (`spng/spng.c`, ~4k LOC) plus `spng/spng.h`**,
  relying on our already-verified `zlib` (`inflate`, `deflate`, `crc32`). Proving `libspng`
  completely secures every PNG upload and PNG output across the entire Sharp/Node.js ecosystem!

## Real-World Usage Paths & Function Priority

Direct call audit of `libvips/foreign/spngload.c` and `libvips/foreign/spngsave.c` (invoked by
every Sharp PNG input and `.png()` output):

### Tier 1 (P0) — Complete `libvips` / Sharp PNG Decode & Encode Surface (Prove All)

1. **Context lifecycle, limits, options & stream binding:**
   `spng_ctx_new`, `spng_ctx_free`, `spng_set_png_buffer`, `spng_set_png_stream`,
   `spng_set_option`, `spng_get_option`, `spng_set_image_limits`, `spng_set_chunk_limits`,
   `spng_set_crc_action`, `spng_strerror`, `spng_version_string`.
2. **Header & ancillary chunk parsing (`spngload.c`):**
   `spng_get_ihdr`, `spng_get_plte`, `spng_get_trns`, `spng_get_chrm`, `spng_get_chrm_int`,
   `spng_get_gama`, `spng_get_iccp`, `spng_get_srgb`, `spng_get_text`, `spng_get_bkgd`,
   `spng_get_phys`, `spng_get_sbit`, `spng_get_exif`, `spng_get_offs`, `spng_get_unknown_chunks`.
3. **PNG decoding (one-shot & progressive row-by-row, interlaced Adam7 & non-interlaced):**
   `spng_decoded_image_size`, `spng_decode_image`, `spng_decode_scanline`, `spng_decode_row`,
   `spng_decode_chunks`, `spng_get_row_info` — across all output formats (`SPNG_FMT_RGBA8`,
   `SPNG_FMT_RGBA16`, `SPNG_FMT_RGB8`, `SPNG_FMT_GA8`, `SPNG_FMT_GA16`, `SPNG_FMT_G8`,
   `SPNG_FMT_PNG`, `SPNG_FMT_RAW`) and flags (`SPNG_DECODE_TRNS`, `SPNG_DECODE_GAMMA`,
   `SPNG_DECODE_PROGRESSIVE`).
4. **PNG encoding (`spngsave.c` — compression/output path):**
   `spng_set_ihdr`, `spng_set_plte`, `spng_set_trns`, `spng_set_iccp`, `spng_set_srgb`,
   `spng_set_gama`, `spng_set_phys`, `spng_set_text`, `spng_set_exif`, `spng_encode_image`,
   `spng_encode_scanline`, `spng_encode_row`, `spng_encode_chunks`, `spng_get_png_buffer`.

### Tier 2 (P1) & Explicitly Not Planned

- **Tier 2:** Remaining rare ancillary chunk getters/setters (`spng_get_splt`/`spng_set_splt`,
  `spng_get_hist`/`spng_set_hist`, `spng_get_time`/`spng_set_time`, `spng_set_png_file`,
  `spng_ctx_new2` custom allocator).
- **Not planned:** SIMD filter intrinsics (disabled via `SPNG_DISABLE_OPT`), `miniz` backend
  (Sharp/Linux uses `zlib`), and full PNG spec visual rendering equivalence beyond safety invariants.

## Verified Translation Units

Entire library:
- `spng/spng.h`
- `spng/spng.c`
*(Linked against the proved `zlib` C ABI contract from `projects/zlib/` for `inflateInit_`,
`inflate`, `inflateEnd`, `deflateInit2_`, `deflate`, `deflateEnd`, `crc32`.)*

## Library-Specific Verification Hazards (No Shortcuts)

1. **Integer overflows in scanline width, bit-depth unpacking & `spng_decoded_image_size`.**
   PNG supports 1, 2, 4, 8, and 16-bit depths across Grayscale, Truecolor, Indexed, Grayscale+Alpha,
   and RGBA, plus Adam7 7-pass sub-images with small dimensions (1x1, 2x2, 3x5). Prove `scanline_width`
   and `out_width * height` never overflow `size_t` and match allocated `scanline_buf` / `prev_scanline_buf`.
2. **PNG scanline defiltering (`defilter_scanline`) & filtering (`filter_scanline`).**
   Sub, Up, Average, and Paeth filters access `scanline[i - bytes_per_pixel]` and `prev_scanline[i]`.
   Prove `bytes_per_pixel` (`1..8`), filter byte validation (`0..4`), first-row `prev_scanline`
   handling, and Adam7 pass transitions never underflow or read/write out of bounds.
3. **Palette (`PLTE`), transparency (`tRNS`), and sub-8-bit expansion.**
   Prove that indexed pixels (values `0..255`) referencing truncated palettes (`n_entries < 256`) or
   partial `tRNS` tables (`n_type3_entries <= 256`) are strictly bounds-checked before indexing
   `ctx->plte.entries` / `ctx->trns.type3_alpha`.
4. **Compressed ancillary chunks (`iCCP`, `zTXt`, `iTXt`) & chunk-size / memory limits.**
   `read_chunks_before_idat` / `read_chunks_after_idat` inflate untrusted compressed chunks with
   `inflate` into dynamically grown buffers bounded by `chunk_cache_max`. Prove growth doubling,
   NUL-terminator searches inside `text`/`iCCP` keyword fields, and cleanup on `spng_ctx_free` are
   completely free of OOB reads, leaks, or double-frees.
5. **Encoder dynamic buffer (`SPNG_ENCODE_TO_BUFFER`) & progressive row state machine.**
   Prove `spng_encode_row` / `spng_encode_image` / `spng_get_png_buffer` enforce valid call order,
   output buffer reallocation bounds, and clean failure when `deflate` or `malloc` fails mid-image.

## Bootstrap & Local Commands

When onboarding into `framework/projects.json`: copy `lean-toolchain`,
start `LibspngF/Runtime/Ptr.lean` from `framework/lean/StrictPtr.lean`, wire `LibspngF/Results.lean`
and `project.json`, then run:

```bash
lake --dir projects/libspng build --wfail LibspngF LibspngF.Results
python3 framework/check_project.py libspng --skip-build
```

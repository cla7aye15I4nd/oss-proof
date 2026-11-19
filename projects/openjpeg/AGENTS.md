# Working rules (`projects/openjpeg`)

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

- **Status:** Upstream submodule `openjpeg/` pinned (not yet registered in `framework/projects.json`;
  Lean runtime bootstrap, C translation, and safety proofs **Not done**).

## Scope (`OpenjpegF`)

- **Upstream source:** `openjpeg/` pinned submodule (`https://github.com/uclouvain/openjpeg`, core
  `src/lib/openjp2/`) + `patches/*.patch` in name order.
- **Target configuration:** portable scalar, single-threaded x86_64 Linux LP64 build
  (`-DOPJ_USE_THREAD=OFF`, disabling AVX2/SSE/NEON DWT/MCT SIMD kernels).
- **Verification goal:** full safety (no ISO C17 undefined behaviour, no integer overflow in
  tile/precinct/code-block/DWT dimension math, no heap OOB read/write in MQ arithmetic coder or
  packet/tier-2 parser, no memory leak or UAF, stated write frame, and termination) across **both
  JPEG 2000 decoding AND encoding** APIs in `openjpeg.h`.

## Real-World Usage Paths & Function Priority

`libopenjp2` is the standard open-source JPEG 2000 codec — **auto-sniffed by PIL / Pillow** on
untrusted uploads (`Image.open()` -> `Jpeg2KImagePlugin.py` -> `src/libImaging/Jpeg2KDecode.c`, plus
`Jpeg2KEncode.c` on `.save(..., "JPEG2000")`), and embedded in **Chrome/PDFium**, **Poppler**,
**MuPDF**, **Ghostscript**, **FFmpeg**, **GDAL**, and medical DICOM viewers. Historically it has a
very high density of heap buffer overflows, signed integer overflows, and OOB reads/writes across
`j2k.c`, `tcd.c`, `t1.c`, `t2.c`, `dwt.c`, `jp2.c`, and `pi.c`:

- **PIL / Pillow (`Jpeg2KDecode.c` & `Jpeg2KEncode.c`):**
  - Decode: `opj_set_default_decoder_parameters`, `opj_create_decompress` (`OPJ_CODEC_J2K` and
    `OPJ_CODEC_JP2`), `opj_setup_decoder`, `opj_stream_create`, `opj_stream_set_read_function` /
    `_skip_function` / `_seek_function`, `opj_read_header`, `opj_set_decode_area`, `opj_decode`,
    `opj_end_decompress`, `opj_stream_destroy`, `opj_destroy_codec`, `opj_image_destroy`.
  - Encode: `opj_set_default_encoder_parameters`, `opj_image_create`, `opj_create_compress`,
    `opj_setup_encoder`, `opj_start_compress`, `opj_encode`, `opj_end_compress`,
    `opj_stream_destroy`, `opj_destroy_codec`, `opj_image_destroy`.

### Tier 1 (P0) — JPEG 2000 Decoding Path (`OPJ_CODEC_JP2` & `OPJ_CODEC_J2K`, Prove First)

1. **Codec lifecycle, stream I/O & JP2/J2K container/marker parsing (`openjpeg.c`, `cio.c`,
   `jp2.c`, `j2k.c`, `image.c`, `event.c`, `opj_malloc.c`):**
   `opj_create_decompress`, `opj_setup_decoder`, `opj_stream_create`, `opj_read_header`,
   `opj_set_decode_area`, `opj_decode`, `opj_read_tile_header`, `opj_decode_tile_data`,
   `opj_end_decompress`, `opj_destroy_codec`, `opj_image_destroy` (including JP2 box parsing:
   `ihdr`, `colr`, `pclr`, `cmap`, `cdef`, `jp2c`; J2K markers: `SIZ`, `COD`, `COC`, `QCD`, `QCC`,
   `RGN`, `POC`, `TLM`, `PLM`, `PLT`, `PPM`, `PPT`, `SOT`, `SOD`, `EOC`).
2. **Tile, Packet (Tier-2), Bit-plane/MQ Coder (Tier-1), DWT & MCT (`tcd.c`, `t2.c`, `pi.c`,
   `tgt.c`, `bio.c`, `t1.c`, `mqc.c`, `dwt.c`, `mct.c`, `sparse_array.c`, `invert.c`):**
   Full scalar decompression pipeline from codestream packets to reconstructed component buffers.

### Tier 2 (P1) — JPEG 2000 Encoding Path & Explicitly Not Planned

- **Tier 2 (Encoding path — `j2k.c`, `jp2.c`, `tcd.c`, `t1.c`, `t2.c`, `dwt.c`, `mct.c`, `mqc.c`):**
  `opj_create_compress`, `opj_setup_encoder`, `opj_start_compress`, `opj_encode`,
  `opj_write_tile`, `opj_end_compress`, `opj_image_create`.
- **Not planned:** Multi-threaded worker pool (`thread.c` when `OPJ_USE_THREAD=OFF`), HTJ2K
  high-throughput extensions (`ht_dec.c` unless enabled in Pillow), SIMD kernels, `opj_decompress`
  / `opj_compress` CLI binaries (`src/bin/jp2/`), and rate-distortion/PSNR functional equivalence.

## Verified Translation Units

- `src/lib/openjp2/openjpeg.h`, `opj_includes.h`, `opj_intmath.h`
- `src/lib/openjp2/bio.c`, `cio.c`, `dwt.c`, `event.c`, `image.c`, `invert.c`, `j2k.c`, `jp2.c`,
  `mct.c`, `mqc.c`, `openjpeg.c`, `opj_malloc.c`, `pi.c`, `sparse_array.c`, `t1.c`, `t2.c`,
  `tcd.c`, `tgt.c`

## Library-Specific Verification Hazards (No Shortcuts)

1. **Tile/resolution/precinct/code-block 32-bit coordinate overflows (`tcd.c`, `j2k.c`, `pi.c`).**
   J2K `SIZ` and `COD` markers encode arbitrary 32-bit canvas origins `(x0, y0)`, subsampling
   factors `(dx, dy)`, tile grids, and decomposition levels (`numresolutions <= 33`). Prove every
   `opj_int_ceildiv` / `opj_uint_ceildivpow2` and `(x1 - x0) * (y1 - y0)` allocation calculation
   cannot overflow or divide by zero.
2. **JP2 palette (`pclr`) & component-mapping (`cmap`) expansion (`jp2.c`).**
   `opj_jp2_apply_pclr` replaces indexed components with multi-channel palette lookups; prove
   sample indices are clamped to `[0, nr_entries - 1]`, signed/unsigned precision shifts (`prec` in
   `1..32`) cannot shift by `>= 32` or `< 0`, and channel counts match allocated `image->comps`.
3. **Tier-2 packet iterator (`pi.c`), tag-trees (`tgt.c`) & bit-I/O (`bio.c`, `t2.c`).**
   Prove `t2_read_packet_header` / `t2_read_packet_data` validate code-block segment lengths,
   inclusion/zero-bit-plane tag-tree depth, and `cblk->data` buffer growth without OOB reads/writes.
4. **Tier-1 MQ arithmetic coder & bit-plane passes (`t1.c`, `mqc.c`).**
   Prove `opj_t1_dec_sigpass`/`refpass`/`clnpass` stay strictly inside `t1->data` and `t1->flags`
   (including sentinel border padding) and `opj_mqc_bytein` respects `mqc->end`.
5. **1D/2D Discrete Wavelet Transform (`dwt.c`) & Multi-Component Transform (`mct.c`).**
   Prove 5-3 reversible and 9-7 irreversible lifting steps handle degenerate 1-pixel or odd-sized
   subbands (`sn == 0`, `dn == 0`, `sn == 1`) without negative pointer offsets or signed overflow.

## Bootstrap & Local Commands

When onboarding into `framework/projects.json`: copy `lean-toolchain`,
start `OpenjpegF/Runtime/Ptr.lean` from `framework/lean/StrictPtr.lean`, wire
`OpenjpegF/Results.lean` and `project.json`, then run:

```bash
lake --dir projects/openjpeg build --wfail OpenjpegF OpenjpegF.Results
python3 framework/check_project.py openjpeg --skip-build
```

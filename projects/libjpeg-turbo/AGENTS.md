# Working rules (`projects/libjpeg-turbo`)

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

- **Status:** Upstream submodule `libjpeg-turbo/` pinned (not yet registered in
  `framework/projects.json`; Lean runtime bootstrap, C translation, and safety proofs **Not done**).

## Scope (`LibjpegTurboF`)

- **Upstream source:** `libjpeg-turbo/` pinned submodule
  (`https://github.com/libjpeg-turbo/libjpeg-turbo`) + `patches/*.patch` in name order.
  *(Note: Sharp's bundled `mozjpeg` is a fork of `libjpeg-turbo` that shares the exact same IJG
  decoder `jd*.c` and adds trellis quantization / progressive scan optimization in the encoder
  `jc*.c`; proving `libjpeg-turbo` covers **100% of Pillow's JPEG path** and the core decoder +
  base encoder of **Sharp**.)*
- **Target configuration:** portable scalar x86_64 Linux LP64 build (`-DWITH_SIMD=0
  -DWITH_ARITH_DEC=1 -DWITH_ARITH_ENC=1 -DWITH_TURBOJPEG=1`, pure-C fallback without SSE2/AVX2/NEON
  assembly, 8-bit primary target with 12-bit/lossless SOF3 explicitly tracked in Tier 2).
- **Verification goal:** full safety (no ISO C17 undefined behaviour, no heap/stack buffer overflow
  in upsampling/IDCT/Huffman/coefficient buffers, no `setjmp`/`longjmp` resource leak or UAF, no
  null dereference or div-by-zero on malformed markers, stated write frame, and termination) across
  **both JPEG decompression AND JPEG compression** APIs (`jpeglib.h` and `turbojpeg.h`).

## Real-World Usage Paths & Function Priority

JPEG is the single highest-volume untrusted image format on the internet:
- **Sharp / `libvips` (`jpegload.c`/`jpeg2vips.c` & `jpegsave.c`/`vips2jpeg.c`):**
  - Decode: `jpeg_create_decompress`, `jpeg_save_markers` (`APP1` EXIF/XMP, `APP2` ICC, `APP13` IPTC),
    `jpeg_read_header`, shrink-on-load (`cinfo.scale_num = 1; cinfo.scale_denom = 2/4/8`),
    `jpeg_start_decompress`, `jpeg_read_scanlines`, `jpeg_finish_decompress`, `jpeg_destroy_decompress`.
  - Encode: `jpeg_create_compress`, `jpeg_set_defaults`, `jpeg_set_quality`, `jpeg_simple_progression`,
    `jpeg_start_compress`, `jpeg_write_marker` (EXIF/ICC/XMP), `jpeg_write_scanlines`,
    `jpeg_finish_compress`, `jpeg_destroy_compress`.
- **PIL / Pillow (`src/libImaging/JpegDecode.c` & `JpegEncode.c`):**
  - Decode: `jpeg_create_decompress`, `jpeg_read_header`, `jpeg_calc_output_dimensions`, draft
    scaling (`scale_num`/`scale_denom`), `jpeg_start_decompress`, `jpeg_read_scanlines`,
    `jpeg_finish_decompress` / `jpeg_abort_decompress`, `jpeg_destroy_decompress` (note
    `CVE-2026-112403` interacted directly with 8-bit lossless SOF3 + draft downscaling!).
  - Encode: `jpeg_create_compress`, `jpeg_set_defaults`, `jpeg_set_quality`, `jpeg_start_compress`,
    `jpeg_write_scanlines`, `jpeg_finish_compress`, `jpeg_destroy_compress`.
- **Browsers, Cloud Services, OpenCV, ImageMagick, FFmpeg, Android/iOS:** Both `libjpeg` (`jpeg_*`)
  and `TurboJPEG` (`tj3Init`, `tj3DecompressHeader`, `tj3Decompress8`, `tj3Compress8`, `tj3Destroy`)
  APIs.
- **Historical CVE Anchors:** `CVE-2021-29390` (buffer overflow in `jdcoefct.c` progressive/12-bit
  coefficient decoding), `CVE-2023-2804` (heap buffer overflow in `jdmrgext.c` merged upsampling on
  12-bit lossless JPEGs), null derefs & div-by-zero in `jdmarker.c`, `jdpostct.c`, `jquant1.c`.

### Tier 1 (P0) — Core 8-Bit JPEG Decompression & Compression (`jpeglib.h`, Prove First)

1. **Decompression lifecycle & marker/header parsing (`jdapimin.c`, `jdapistd.c`, `jdmarker.c`,
   `jdatasrc.c`, `jdinput.c`, `jdmaster.c`, `jerror.c`, `jmemmgr.c`, `jmemnobs.c`):**
   `jpeg_CreateDecompress`, `jpeg_mem_src`, `jpeg_save_markers`, `jpeg_read_header`,
   `jpeg_calc_output_dimensions`, `jpeg_start_decompress`, `jpeg_read_scanlines`,
   `jpeg_skip_scanlines`, `jpeg_crop_scanline`, `jpeg_finish_decompress`, `jpeg_abort_decompress`,
   `jpeg_destroy_decompress`.
2. **Entropy decoders, IDCT, upsampling & color conversion (`jdhuff.c`, `jdphuff.c`, `jdarith.c`,
   `jdcoefct.c`, `jdmainct.c`, `jddctmgr.c`, `jidctint.c`, `jidctfst.c`, `jidctflt.c`, `jidctred.c`,
   `jdsample.c`, `jdmerge.c`, `jdcolor.c`, `jdpostct.c`, `jutils.c`):**
   Baseline sequential, progressive multi-scan, arithmetic-coded, and `scale_denom` 1/2, 1/4, 1/8
   shrink-on-load IDCT paths.
3. **Compression lifecycle & encoder pipeline (`jcapimin.c`, `jcapistd.c`, `jcparam.c`, `jcinit.c`,
   `jcmaster.c`, `jcmarker.c`, `jdatadst.c`, `jchuff.c`, `jcphuff.c`, `jcarith.c`, `jccoefct.c`,
   `jcmainct.c`, `jcprepct.c`, `jcdctmgr.c`, `jfdctint.c`, `jfdctfst.c`, `jcsample.c`, `jccolor.c`):**
   `jpeg_CreateCompress`, `jpeg_mem_dest`, `jpeg_set_defaults`, `jpeg_set_quality`,
   `jpeg_simple_progression`, `jpeg_start_compress`, `jpeg_write_marker`, `jpeg_write_scanlines`,
   `jpeg_finish_compress`, `jpeg_abort_compress`, `jpeg_destroy_compress`.

### Tier 2 (P1) — TurboJPEG Wrapper, Lossless/12-Bit/16-Bit Precision & Raw/Transcode APIs

- **TurboJPEG API (`turbojpeg.c`, `transupp.c`):** `tj3Init`, `tj3DecompressHeader`,
  `tj3Decompress8`, `tj3Compress8`, `tj3Transform`, `tj3Destroy` (plus legacy `tjDecompress2` /
  `tjCompress2`).
- **Lossless (SOF3) & 12-bit/16-bit precision (`jdlossls.c`, `jclossls.c`, `jddiffct.c`,
  `jcdiffct.c`):** High CVE density (`CVE-2023-2804`, `CVE-2026-112403` interaction) — prove
  strict sample-range clamping (`<= MAXJSAMPLE`) and upsampler bounds.
- **2-pass color quantization (`jquant1.c`, `jquant2.c`) & lossless coefficient copy
  (`jpeg_read_coefficients`, `jpeg_write_coefficients`).**

### Explicitly Not Planned

- SIMD assembly directories (`simd/x86_64/`, `simd/arm/`, `simd/powerpc/`, etc.).
- CLI programs (`cjpeg.c`, `djpeg.c`, `jpegtran.c`, `tjbench.c`), Java JNI bindings, and
  perceptual/PSNR image quality equivalence beyond safety invariants.

## Library-Specific Verification Hazards (No Shortcuts)

1. **`setjmp`/`longjmp` error-exit control flow (`jerror.c`, `jmemmgr.c`).**
   Upstream `libjpeg` aborts on fatal parse errors via `ERREXIT` -> `error_exit` -> `longjmp` back
   to the caller, which then calls `jpeg_destroy_*`. Model `error_exit` explicitly as a structured
   abort monad state and prove `jpeg_destroy_decompress` / `jpeg_destroy_compress` frees every
   pool allocation cleanly with zero leak or double-free from **any** `ERREXIT` site!
2. **Custom `jmemmgr.c` pool allocator & virtual-array (`jvirt_barray_ptr`) bounds.**
   `libjpeg-turbo` allocates internal small/large pools (`JPOOL_PERMANENT`, `JPOOL_IMAGE`) and 2D
   sample/coefficient arrays via `alloc_sarray` / `alloc_barray`. Prove every pool slice and
   aligned pointer offset stays within its backing allocation without overflow or dangling pointers.
3. **Huffman bit-buffer lookahead & progressive scan state (`jdhuff.c`, `jdphuff.c`, `jdcoefct.c`).**
   Prove fast-path `HUFF_DECODE`, `jpeg_fill_bit_buffer`, restart-marker (`RST0`–`RST7`) resync,
   truncated-EOF zero-stuffing, and progressive `Ss`/`Se`/`Ah`/`Al` spectral/successive-approximation
   parameters never index outside `block[64]` or `coef_buffers`.
4. **Upsampling, merged YCbCr->RGB & `scale_denom` geometry (`jdsample.c`, `jdmerge.c`, `jdcolor.c`,
   `jdmrgext.c` — `CVE-2023-2804`).**
   Prove non-uniform subsampling factors (`h_samp_factor`/`v_samp_factor` in `1..4`), odd image
   widths/heights, `cinfo.output_width`/`output_components`, and sample-table clamps (`range_limit`
   negative-indexed pointer arithmetic — audit `range_limit` base offset under strict ISO C17!)
   never read/write out of bounds.
5. **Encoder Huffman/bit-emission & `jpeg_mem_dest` dynamic buffer growth (`jchuff.c`, `jcphuff.c`,
   `jdatadst.c`).**
   Prove `emit_bits`, `0xFF -> 0xFF 0x00` byte stuffing, `empty_output_buffer` reallocation, and
   `jpeg_write_marker` length checks (`<= 65533`) never overrun or overflow.

## Bootstrap & Local Commands

When onboarding into `framework/projects.json`: copy `lean-toolchain`,
start `LibjpegTurboF/Runtime/Ptr.lean` from `framework/lean/StrictPtr.lean`, wire
`LibjpegTurboF/Results.lean` and `project.json`, then run:

```bash
lake --dir projects/libjpeg-turbo build --wfail LibjpegTurboF LibjpegTurboF.Results
python3 framework/check_project.py libjpeg-turbo --skip-build
```

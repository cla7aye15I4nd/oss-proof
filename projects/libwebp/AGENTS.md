# Working rules (`projects/libwebp`)

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

- **Status:** Upstream submodule `libwebp/` pinned (not yet registered in `framework/projects.json`;
  Lean runtime bootstrap, C translation, and safety proofs **Not done**).

## Scope (`LibwebpF`)

- **Upstream source:** `libwebp/` pinned submodule
  (`https://chromium.googlesource.com/webm/libwebp` / `https://github.com/webmproject/libwebp`) +
  `patches/*.patch` in name order.
- **Target configuration:** portable scalar, single-threaded x86_64 Linux LP64 build
  (`-DWEBP_ENABLE_SIMD=OFF -DWEBP_USE_THREAD=OFF`, disabling SSE2/SSE4.1/AVX2/NEON/MSA/MIPS DSP
  kernels so all `src/dsp/*.c` paths run the portable C reference kernels).
- **Verification goal:** full safety (no ISO C17 undefined behaviour, no Huffman table heap overflow,
  no VP8/VP8L bitstream/transform OOB read/write, no RIFF/demux/mux integer overflow or UAF, no
  memory leak, stated write frame, and termination) across **both WebP decoding (VP8 + VP8L +
  Demux/Anim) AND WebP encoding (VP8 + VP8L + Mux/Anim)** public APIs.

## Real-World Usage Paths & Function Priority

`libwebp` is directly shared by **Sharp (Node.js)**, **PIL / Pillow (Python)**, **Chrome /
Firefox / Safari / Edge**, **Apple ImageIO**, **Android**, and **Electron** — and was the site of
**CVE-2023-4863** (actively exploited zero-day heap buffer overflow in `BuildHuffmanTable` inside
`src/dec/vp8l_dec.c` / `src/utils/huffman_utils.c` leading to *BLASTPASS* RCE across OSes, browsers,
Sharp, and Pillow!):

- **Sharp / `libvips` (`webpload.c`/`webp2vips.c` & `webpsave.c`/`vips2webp.c`):**
  - Decode: `WebPGetInfo`, `WebPGetFeatures`, `WebPInitDecoderConfig`, `WebPDecode`,
    `WebPINewDecoder`, `WebPIUpdate`, `WebPIDecGetRGB`/`WebPIDecGetYUVA`, `WebPIDelete`,
    `WebPFreeDecBuffer`, `WebPDemux`, `WebPDemuxGetI`, `WebPDemuxGetFrame`, `WebPDemuxGetChunk`
    (EXIF/ICC/XMP), `WebPDemuxDelete`, `WebPAnimDecoderNew`, `WebPAnimDecoderGetNext`,
    `WebPAnimDecoderDelete`.
  - Encode: `WebPConfigInit`, `WebPValidateConfig`, `WebPPictureInit`, `WebPPictureImportRGB` /
    `WebPPictureImportRGBA`, `WebPEncode`, `WebPPictureFree`, `WebPAnimEncoderNew`,
    `WebPAnimEncoderAdd`, `WebPAnimEncoderAssemble`, `WebPAnimEncoderDelete`, `WebPMuxNew`,
    `WebPMuxSetImage`, `WebPMuxSetChunk` (EXIF/ICC/XMP), `WebPMuxAssemble`, `WebPMuxDelete`.
- **PIL / Pillow (`src/_webp.c`):**
  - Decode: `WebPGetInfo`, `WebPGetFeatures`, `WebPDecodeRGBInto`, `WebPDecodeRGBAInto`,
    `WebPDemux`, `WebPDemuxGetI`, `WebPDemuxGetFrame`, `WebPDemuxDelete`, `WebPAnimDecoderNew`,
    `WebPAnimDecoderGetInfo`, `WebPAnimDecoderGetNext`, `WebPAnimDecoderDelete`.
  - Encode: `WebPConfigInit`, `WebPValidateConfig`, `WebPPictureInit`, `WebPPictureImportRGB`/
    `RGBA`, `WebPEncode`, `WebPAnimEncoderNew`, `WebPAnimEncoderAdd`, `WebPAnimEncoderAssemble`,
    `WebPAnimEncoderDelete`, `WebPDataClear`.

### Tier 1 (P0) — Decoding & Demuxing Path (Prove First — Highest RCE Exposure)

1. **VP8L lossless decoder & Huffman tables (`src/dec/vp8l_dec.c`, `src/utils/huffman_utils.c`,
   `src/utils/bit_reader_utils.c`, `src/utils/color_cache_utils.c`, `src/dsp/lossless.c`):**
   The exact site of `CVE-2023-4863`! Prove 2-level Huffman table sizing (`VP8LBuildHuffmanTable`),
   prefix-code meta-Huffman groups, LZ77 backward-copy + color-cache indexing, and inverse spatial
   transforms (Predictor, Cross-Color, Subtract-Green, Color-Indexing palette unpacking).
2. **VP8 lossy decoder + Alpha + Frame/Incremental/Buffer APIs (`src/dec/webp_dec.c`,
   `src/dec/vp8_dec.c`, `src/dec/alpha_dec.c`, `src/dec/frame_dec.c`, `src/dec/io_dec.c`,
   `src/dec/idec_dec.c`, `src/dec/buffer_dec.c`, `src/dec/quant_dec.c`, `src/dec/tree_dec.c`,
   `src/utils/rescaler_utils.c`, `src/dsp/dec.c`, `src/dsp/upsampling.c`, `src/dsp/yuv.c`,
   `src/dsp/alpha_processing.c`, `src/dsp/rescaler.c`):**
   `WebPGetInfo`, `WebPGetFeatures`, `WebPInitDecoderConfig`, `WebPDecode`, `WebPDecodeRGBInto`,
   `WebPDecodeRGBAInto`, `WebPINewDecoder`, `WebPIUpdate`, `WebPIDelete`, `WebPFreeDecBuffer`
   (including Sharp's shrink-on-load `options.use_scaling` / `options.use_cropping`!).
3. **RIFF container demuxer & animated WebP decoder (`src/demux/demux.c`,
   `src/demux/anim_decode.c`):**
   `WebPDemuxInternal`, `WebPDemuxGetI`, `WebPDemuxGetFrame`, `WebPDemuxNextFrame`,
   `WebPDemuxGetChunk`, `WebPDemuxDelete`, `WebPAnimDecoderNewInternal`, `WebPAnimDecoderGetInfo`,
   `WebPAnimDecoderGetNext`, `WebPAnimDecoderReset`, `WebPAnimDecoderDelete`.

### Tier 1 (P0) — Encoding & Muxing Path (Sharp & Pillow Primary Output Path)

1. **Lossy VP8 & Lossless VP8L encoders (`src/enc/webp_enc.c`, `src/enc/config_enc.c`,
   `src/enc/picture_enc.c`, `src/enc/picture_csp_enc.c`, `src/enc/picture_rescale_enc.c`,
   `src/enc/picture_tools_enc.c`, `src/enc/vp8l_enc.c`, `src/enc/backward_references_enc.c`,
   `src/enc/backward_references_cost_enc.c`, `src/enc/histogram_enc.c`, `src/enc/alpha_enc.c`,
   `src/enc/frame_enc.c`, `src/enc/analysis_enc.c`, `src/enc/quant_enc.c`, `src/enc/token_enc.c`,
   `src/enc/tree_enc.c`, `src/enc/syntax_enc.c`, `src/enc/filter_enc.c`, `src/enc/cost_enc.c`,
   `src/enc/iterator_enc.c`, `src/enc/near_lossless_enc.c`, `src/enc/predictor_enc.c`,
   `src/utils/bit_writer_utils.c`, `src/utils/huffman_encode_utils.c`, `src/dsp/enc.c`,
   `src/dsp/lossless_enc.c`, `src/dsp/cost.c`, `src/dsp/ssim.c`):**
   `WebPConfigInit`, `WebPValidateConfig`, `WebPPictureInit`, `WebPPictureImportRGB`/
   `WebPPictureImportRGBA`, `WebPEncode`, `WebPEncodeRGB`/`RGBA`/`LosslessRGB`/`LosslessRGBA`,
   `WebPPictureFree`.
2. **RIFF muxer & animated WebP encoder (`src/mux/muxedit.c`, `src/mux/muxinternal.c`,
   `src/mux/muxread.c`, `src/mux/anim_encode.c`):**
   `WebPMuxNew`, `WebPMuxSetImage`, `WebPMuxSetChunk`, `WebPMuxAssemble`, `WebPMuxDelete`,
   `WebPAnimEncoderNewInternal`, `WebPAnimEncoderAdd`, `WebPAnimEncoderAssemble`,
   `WebPAnimEncoderDelete`, `WebPDataClear`.

### Explicitly Not Planned

- Platform SIMD DSP files (`*_sse2.c`, `*_sse41.c`, `*_avx2.c`, `*_neon.c`, `*_msa.c`, `*_mips*.c`).
- Multi-threaded decoding (`src/utils/thread_utils.c` when `WEBP_USE_THREAD=OFF`), `sharpyuv/`
  (optional Tier 2 if enabled), CLI tools (`examples/`), and perceptual rate-distortion optimality.

## Library-Specific Verification Hazards (No Shortcuts)

1. **VP8L 2-level Huffman table sizing (`vp8l_dec.c`, `huffman_utils.c` — `CVE-2023-4863`).**
   Prove mathematically (via Kraft-sum / root+secondary table-size upper-bound lemmas) that
   `ReadHuffmanCodes` allocates enough `HuffmanCode` entries for **every** possible code-length
   histogram accepted by `VP8LBuildHuffmanTable`, including degenerate, over-subscribed, and
   single-symbol trees!
2. **VP8L inverse transforms & sub-resolution image dimensions (`vp8l_dec.c`, `lossless.c`).**
   Color-indexing transforms shrink effective width by `1 << width_bits` (`1, 2, 4, 8`), and
   recursive sub-images store predictor/cross-color/histogram grids. Prove `SubSampleSize`, palette
   expansion in-place, and `ApplyInverseTransforms` stay strictly inside `dec->pixels`.
3. **VP8 macroblock partitions, boolean range decoder & loop filter (`vp8_dec.c`, `frame_dec.c`,
   `bit_reader_utils.c`).**
   Prove partition offset validation (`num_parts <= 8`), `VP8GetBit` / `VP8LoadNewBytes` end-of-buffer
   bounds, macroblock row cache (`yuv_b`, `f_info`, `mb_info`), and in-loop deblocking edge bounds.
4. **Animated frame blending/disposal & RIFF chunk overflow (`demux.c`, `anim_decode.c`, `mux*.c`).**
   Prove canvas rectangle `(x_offset, y_offset, width, height)` clipping against `(canvas_width,
   canvas_height)`, 32-bit RIFF chunk-size padding overflow (`size + (size & 1)`), and chunk-list
   ownership across `WebPDemuxDelete` / `WebPMuxDelete`.
5. **Incremental decoding (`idec_dec.c`) & rescaler arithmetic (`rescaler_utils.c`).**
   Prove arbitrary 1-byte `WebPIUpdate` splits (including save/restore of `VP8BitReader` state on
   truncation) and Sharp's shrink-on-load scaling (`scaled_width`/`scaled_height`) cannot overflow
   or write past caller buffers.

## Bootstrap & Local Commands

When onboarding into `framework/projects.json`: copy `lean-toolchain`,
start `LibwebpF/Runtime/Ptr.lean` from `framework/lean/StrictPtr.lean`, wire `LibwebpF/Results.lean`
and `project.json`, then run:

```bash
lake --dir projects/libwebp build --wfail LibwebpF LibwebpF.Results
python3 framework/check_project.py libwebp --skip-build
```

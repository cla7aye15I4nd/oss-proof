# Working rules (`projects/libwebp`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), including the strict
ISO C17 undefined-behaviour policy: no `NULL`, wild or dangling pointer `+ 0`, no `NULL - NULL`, no
cross-object pointer subtraction or comparison, no out-of-bounds pointer formation, no zero-length
`memcpy`/`memset` on invalid pointers, every struct pointer field written before it is read, and no
"benign UB" arguments. The runtime starts from `framework/lean/StrictPtr.lean`.

- **Status:** candidate. Upstream submodule `libwebp/` tracks the latest default branch. Not
  registered in `framework/projects.json`; translation and proofs are not done.

## Why it matters

Both Sharp (libvips `foreign/webp2vips.c`, `foreign/webpsave.c`) and Pillow (`src/_webp.c`) bundle
libwebp 1.6.0 and decode every WebP upload with it, still or animated, lossy or lossless.

## Interfaces to prove (P0)

- **Sharp decode:** `WebPInitDecoderConfig`, `WebPDecode`, `WebPFreeDecBuffer`, `WebPDemux`,
  `WebPDemuxGetI`, `WebPDemuxGetFrame`, `WebPDemuxNextFrame`, `WebPDemuxReleaseIterator`,
  `WebPDemuxGetChunk`, `WebPDemuxReleaseChunkIterator` (with scaled decoding for shrink-on-load).
- **Pillow decode:** `WebPGetFeatures`, `WebPAnimDecoderNew`, `WebPAnimDecoderGetInfo`,
  `WebPAnimDecoderGetNext`, `WebPAnimDecoderReset`, `WebPAnimDecoderGetDemuxer`,
  `WebPAnimDecoderDelete`, `WebPDemuxGetChunk`, `WebPDemuxReleaseChunkIterator`, `WebPDataInit`,
  `WebPDataCopy`, `WebPDataClear`. Pillow decodes still images through the animation decoder too.
- **Encode (both):** `WebPConfigInit`, `WebPConfigPreset`, `WebPConfigLosslessPreset`,
  `WebPValidateConfig`, `WebPPictureInit`, `WebPPictureAlloc`, `WebPPictureFree`, `WebPEncode`,
  `WebPMemoryWriterInit`, `WebPMemoryWriterClear`, `WebPAnimEncoderOptionsInit`,
  `WebPAnimEncoderNew`, `WebPAnimEncoderAdd`, `WebPAnimEncoderAssemble`,
  `WebPAnimEncoderGetError`, `WebPAnimEncoderDelete`, `WebPMuxNew`, `WebPMuxCreate`,
  `WebPMuxSetImage`, `WebPMuxSetChunk`, `WebPMuxGetFeatures`, `WebPMuxGetAnimationParams`,
  `WebPMuxSetAnimationParams`, `WebPMuxAssemble`, `WebPMuxDelete`.

## Verification hazards

1. Lossless (VP8L) Huffman table sizing: the allocation must cover every code-length set the table
   builder accepts.
2. VP8L transforms (predictor, cross-colour, subtract-green, colour indexing with packed pixels)
   and the colour cache.
3. Lossy (VP8) partitions, boolean decoder reads at the end of input, and the per-row caches.
4. Alpha (`ALPH`) chunk decoding and filtering.
5. RIFF chunk sizes and padding in the demuxer; animation frame rectangles and blending against
   the canvas.

## Not in scope

SIMD DSP files (build without SSE/NEON), threaded decoding, `sharpyuv` tuning, tools, and
rate-distortion quality.

## Local commands

```bash
lake --dir projects/libwebp build --wfail LibwebpF LibwebpF.Results
python3 framework/check_project.py libwebp --skip-build
```

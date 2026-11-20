# Working rules (`projects/libwebp`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), which is
authoritative on proof soundness, allowed axioms and the strict ISO C17 undefined-behaviour policy.
The runtime starts from `framework/lean/StrictPtr.lean`.

**Status:** candidate. Upstream submodule `libwebp/` tracks the latest default branch; not
registered in `framework/projects.json`; translation and proofs are not done.

## Tier 0

Tier 0 is the code that turns untrusted bytes into pixels or metadata on a default path. It is the
whole scope of this project.

**How it is reached.**

- Sharp: `sharp(webp).jpeg().toBuffer()` → libvips `foreign/webp2vips.c` `read_header` (demux,
  EXIF/ICC chunks) → `read_frame` (decode, scaled for shrink-on-load).
- Pillow: `Image.open(webp)` → `WebPImageFile` → `src/_webp.c` `_anim_decoder_new` /
  `_anim_decoder_get_next`; still images go through the animation decoder too.

**Functions:** `WebPInitDecoderConfig`, `WebPDecode`, `WebPFreeDecBuffer`, `WebPDemux`,
`WebPDemuxGetI`, `WebPDemuxGetFrame`, `WebPDemuxNextFrame`, `WebPDemuxGetChunk`,
`WebPDemuxReleaseIterator`, `WebPDemuxReleaseChunkIterator`, `WebPGetFeatures`,
`WebPAnimDecoderNew`, `WebPAnimDecoderGetInfo`, `WebPAnimDecoderGetNext`,
`WebPAnimDecoderReset`, `WebPAnimDecoderDelete` — and the VP8, VP8L, alpha and demux code behind
them.

**What the proofs must cover.**

1. Lossless (VP8L) Huffman tables are allocated large enough for every code-length set the builder
   accepts; transforms and the colour cache stay in bounds.
2. Lossy (VP8) partitions and the boolean decoder never read past the input.
3. RIFF chunk sizes and animation frame rectangles stay inside the input and the canvas.

## Local commands

```bash
LEAN_NUM_THREADS=4 lake --dir projects/libwebp build --wfail LibwebpF LibwebpF.Results
python3 framework/check_project.py libwebp --skip-build
```

# Working rules (`projects/libavif`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), which is
authoritative on proof soundness, allowed axioms and the strict ISO C17 undefined-behaviour policy.
The runtime starts from `framework/lean/StrictPtr.lean`.

**Status:** candidate. Upstream submodule `libavif/` tracks the latest default branch; not
registered in `framework/projects.json`; translation and proofs are not done.

## Tier 0

Tier 0 is the code that turns untrusted bytes into pixels or metadata on a default path. It is the
whole scope of this project.

**How it is reached.** Pillow's wheels bundle libavif: `Image.open(avif).load()` →
`AvifImageFile` → `src/_avif.c` `AvifDecoderNew` / `_decoder_get_frame`. Sharp reads AVIF through
libheif instead.

**Functions:** `avifDecoderCreate`, `avifDecoderSetIOMemory`, `avifDecoderParse`,
`avifDecoderNthImage`, `avifRGBImageSetDefaults`, `avifRGBImageAllocatePixels`,
`avifImageYUVToRGB`, `avifRGBImageFreePixels`, `avifDecoderDestroy` — and behind them the stream
reader, the ISOBMFF box parser (`read.c`), the AV1 sequence-header parser (`obu.c`), grid assembly
and YUV-to-RGB conversion (`reformat.c`, `alpha.c`). The AV1 codec itself (dav1d) is not included.

**What the proofs must cover.**

1. Box sizes (32-bit, 64-bit and size 0) and item extents stay inside the input.
2. Grid tiles that differ in size, depth or subsampling from the declared grid cannot overrun the
   output planes.
3. YUV-to-RGB strides are correct for odd dimensions and every supported depth.

## Local commands

```bash
LEAN_NUM_THREADS=4 lake --dir projects/libavif build --wfail LibavifF LibavifF.Results
python3 framework/check_project.py libavif --skip-build
```

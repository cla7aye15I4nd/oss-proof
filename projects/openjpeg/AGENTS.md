# Working rules (`projects/openjpeg`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), which is
authoritative on proof soundness, allowed axioms and the strict ISO C17 undefined-behaviour policy.
The runtime starts from `framework/lean/StrictPtr.lean`.

**Status:** candidate. Upstream submodule `openjpeg/` tracks the latest default branch; not
registered in `framework/projects.json`; translation and proofs are not done.

## Tier 0

Tier 0 is the code that turns untrusted bytes into pixels or metadata on a default path. It is the
whole scope of this project.

**How it is reached.** Pillow recognises JPEG 2000 by magic bytes under any file name:
`Image.open(upload).load()` → `Jpeg2KImageFile` → `src/decode.c` `PyImaging_Jpeg2KDecoderNew` →
`src/libImaging/Jpeg2KDecode.c` `ImagingJpeg2KDecode`. Sharp's prebuilt binary does not enable
JPEG 2000.

**Functions** (Pillow decodes tile by tile): `opj_set_default_decoder_parameters`,
`opj_create_decompress`, `opj_setup_decoder`, `opj_stream_create` with its read / skip / seek
callbacks, `opj_read_header`, `opj_read_tile_header`, `opj_decode_tile_data`,
`opj_end_decompress`, `opj_stream_destroy`, `opj_destroy_codec`, `opj_image_destroy` — and the
JP2 box parser, J2K marker parser, tier-2 packet decoder, tier-1 MQ decoder and inverse wavelet
transform behind them.

**What the proofs must cover.**

1. Marker values (origins, subsampling, decomposition levels, code-block sizes) cannot produce
   overflowing or zero-sized geometry.
2. Packet headers and code-block segment lengths stay inside the code-block buffers.
3. The inverse wavelet transform and the JP2 palette / component mapping stay inside the
   allocated components.

## Local commands

```bash
LEAN_NUM_THREADS=4 lake --dir projects/openjpeg build --wfail OpenjpegF OpenjpegF.Results
python3 framework/check_project.py openjpeg --skip-build
```

# Working rules (`projects/xz`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), which is
authoritative on proof soundness, allowed axioms and the strict ISO C17 undefined-behaviour policy.
The runtime starts from `framework/lean/StrictPtr.lean`.

**Status:** candidate. Upstream submodule `xz/` tracks the latest default branch of the upstream
git repository (never a release tarball); not registered in `framework/projects.json`;
translation and proofs are not done.

## Tier 0

Tier 0 is the code that turns untrusted bytes into pixels or metadata on a default path. It is the
whole scope of this project.

**How it is reached.**

- Pillow: an LZMA-compressed TIFF → `ImagingLibTiffDecode` → libtiff `tif_lzma.c` → liblzma.
- Python: `lzma.decompress()` / `LZMADecompressor` (`Modules/_lzmamodule.c`).
- libarchive's xz and lzma read filters.

**Functions** (single-threaded decoding only): `lzma_stream_decoder`, `lzma_auto_decoder`,
`lzma_alone_decoder`, `lzma_raw_decoder`, `lzma_properties_decode`, `lzma_code`, `lzma_end`,
`lzma_memusage`, `lzma_get_check`.

**What the proofs must cover.**

1. Filter chains built and torn down across concatenated streams and blocks, including allocation
   failure in the middle of a chain.
2. Index records and variable-length integers up to `2^63 - 1`, and memory-limit accounting.
3. The LZ dictionary, range decoder and LZMA2 chunk resets across one-byte `lzma_code` calls.

## Local commands

```bash
lake --dir projects/xz build -j 4 --wfail XzF XzF.Results
python3 framework/check_project.py xz --skip-build
```

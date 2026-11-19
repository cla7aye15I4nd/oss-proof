# Working rules (`projects/xz`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), including the strict
ISO C17 undefined-behaviour policy: no `NULL`, wild or dangling pointer `+ 0`, no `NULL - NULL`, no
cross-object pointer subtraction or comparison, no out-of-bounds pointer formation, no zero-length
`memcpy`/`memset` on invalid pointers, every struct pointer field written before it is read, and no
"benign UB" arguments. The runtime starts from `framework/lean/StrictPtr.lean`.

- **Status:** candidate. Upstream submodule `xz/` tracks the latest default branch of the upstream
  git repository (never a release tarball). Not registered in `framework/projects.json`;
  translation and proofs are not done.

## Why it matters

- **Pillow:** the wheels bundle liblzma (5.8.4 in Pillow 13.0.0) for libtiff, so an
  LZMA-compressed TIFF passed to `Image.open` is decoded by liblzma through `libtiff/tif_lzma.c`.
- **Python:** the standard-library `lzma` module (`Modules/_lzmamodule.c`).
- **Archives:** libarchive's xz/lzma filters.

## Interfaces to prove (P0)

Union of what those callers use, single-threaded only:

- **Decode:** `lzma_stream_decoder`, `lzma_auto_decoder`, `lzma_alone_decoder`,
  `lzma_raw_decoder`, `lzma_properties_decode`, `lzma_code`, `lzma_end`, `lzma_memusage`,
  `lzma_get_check`, `lzma_check_is_supported`.
- **Encode:** `lzma_easy_encoder`, `lzma_stream_encoder`, `lzma_alone_encoder`,
  `lzma_raw_encoder`, `lzma_lzma_preset`, `lzma_properties_size`, `lzma_properties_encode`.

## Verification hazards

1. Filter chains (up to four filters) built and torn down across concatenated streams and blocks,
   including allocation failure in the middle of a chain.
2. Index records and variable-length integers up to `2^63 - 1`; memory-limit accounting.
3. LZ dictionary wrap-around in the decoder; hash-chain and binary-tree match finders in the
   encoder.
4. Range decoder reads and LZMA2 chunk/property/dictionary resets across one-byte `lzma_code`
   calls.
5. BCJ filters buffering unconverted bytes between calls.

## Not in scope

Multi-threaded coders (`lzma_stream_encoder_mt` and the threaded decoder), hardware CRC code,
lzip and microlzma, and the `xz` / `xzdec` tools.

## Local commands

```bash
lake --dir projects/xz build --wfail XzF XzF.Results
python3 framework/check_project.py xz --skip-build
```

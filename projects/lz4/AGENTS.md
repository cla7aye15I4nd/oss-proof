# Working rules (`projects/lz4`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), including the strict
ISO C17 undefined-behaviour policy: no `NULL`, wild or dangling pointer `+ 0`, no `NULL - NULL`, no
cross-object pointer subtraction or comparison, no out-of-bounds pointer formation, no zero-length
`memcpy`/`memset` on invalid pointers, every struct pointer field written before it is read, and no
"benign UB" arguments. The runtime starts from `framework/lean/StrictPtr.lean`.

- **Status:** candidate. Upstream submodule `lz4/` tracks the latest default branch. Not
  registered in `framework/projects.json`; translation and proofs are not done.

## Why it matters

Not on a Sharp or Pillow image path. It is a widely embedded compression library (python-lz4,
libarchive, Kafka, Parquet/Arrow, ZFS, the Linux kernel's own copy) and small enough to prove
completely.

## Interfaces to prove (P0)

Union of what python-lz4 (`lz4/block/_block.c`, `lz4/frame/_frame.c`) and libarchive's lz4 filter
call:

- **Block:** `LZ4_decompress_safe`, `LZ4_decompress_safe_usingDict`,
  `LZ4_decompress_safe_withPrefix64k`, `LZ4_compressBound`, `LZ4_resetStream`, `LZ4_loadDict`,
  `LZ4_compress_fast_continue`, `LZ4_resetStreamHC`, `LZ4_loadDictHC`, `LZ4_compress_HC_continue`.
- **Frame:** `LZ4F_createDecompressionContext`, `LZ4F_getFrameInfo`, `LZ4F_decompress`,
  `LZ4F_resetDecompressionContext`, `LZ4F_freeDecompressionContext`,
  `LZ4F_createCompressionContext`, `LZ4F_compressBegin`, `LZ4F_compressUpdate`, `LZ4F_flush`,
  `LZ4F_compressEnd`, `LZ4F_compressFrame`, `LZ4F_compressBound`, `LZ4F_compressFrameBound`,
  `LZ4F_freeCompressionContext`, `LZ4F_isError`, `LZ4F_getErrorName`.

## Verification hazards

1. `int` sizes and capacities in the block API: negative values, `INT_MAX`, and length extensions
   that must never produce a negative copy length.
2. Wild copies that intentionally write past the logical end, guarded by end-of-buffer margins;
   overlapping matches with small offsets.
3. External dictionaries and prefixes living in a different allocation from the output (pointer
   arithmetic across objects is undefined in ISO C17).
4. Frame decoder state across arbitrary input/output splits, block and content checksums.
5. HC hash-chain indices across dictionary loads.

## Not in scope

The deprecated `LZ4_decompress_fast*` functions (no input bound by design), `lz4file.c`, and the
command-line tool.

## Local commands

```bash
lake --dir projects/lz4 build --wfail Lz4F Lz4F.Results
python3 framework/check_project.py lz4 --skip-build
```

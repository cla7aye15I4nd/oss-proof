# libarchive (RAR5 & 7-Zip)

Verification target: `libarchive`'s RAR5 (`archive_read_support_format_rar5.c`) and 7-Zip
(`archive_read_support_format_7zip.c`, `archive_ppmd7.c`) format decoders on default scalar x86_64 Linux LP64.

## Scope

- **RAR5 decoder:** variable-length integer (`vint`) header parsing, solid and multivolume context resets,
  4-table Huffman bitreader progress, circular LZSS window indexing, and E8/E8E9/Delta/ARM post-decompression filters.
- **7-Zip decoder:** two-stage `EncodedHeader` bootstrap, `Folder` / `BindPairs` multi-coder DAG conservation,
  solid `SubStreamsInfo` unpack-size bounds, and the PPMd7 sub-allocator.

## What is proved so far

Top-down state and invariant models (`LibarchiveF.Model`) for both RAR5 and 7-Zip decoders and strict ISO C17
runtime undefined-behaviour rejections (`LibarchiveF.Runtime`) are kernel-checked in Lean 4. Statement-by-statement
C translation and end-to-end `archive_read_*` callback safety proofs are not done.

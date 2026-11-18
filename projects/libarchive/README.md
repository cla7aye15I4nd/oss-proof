# libarchive-f

Kernel-checked Lean 4 top-down modeling and safety verification of `libarchive`'s RAR5
(`archive_read_support_format_rar5.c`) and 7-Zip (`archive_read_support_format_7zip.c`,
`archive_ppmd7.c`) format decoders for the default scalar x86_64 Linux LP64 build.

## Scope

- **RAR5 decoder (`rar5.c`):** `vint` header/extra parsing, solid & multivolume state resets,
  4-table Huffman + bitreader termination, circular LZSS window wrap-around, and E8/E8E9/Delta/ARM
  post-decompression filters.
- **7-Zip decoder (`7zip.c` + `archive_ppmd7.c`):** two-stage `EncodedHeader` bootstrap,
  `Folder`/`BindPairs` multi-coder DAG validation (including BCJ2 4-stream assembly), solid
  `SubStreamsInfo` ledger bounds, and the PPMd custom sub-allocator.

See `AGENTS.md` for working rules and verification architecture, and `LibarchiveF/Model/` for the
top-down state and safety invariant models.

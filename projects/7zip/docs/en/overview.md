# 7-Zip C SDK

Verification target: the official `7-Zip` pure-C SDK (`C/7zArcIn.c`, `C/7zDec.c`, `C/Bcj2.c`,
`C/Ppmd7.c`, `C/Ppmd7Dec.c`, `C/LzmaDec.c`, `C/Lzma2Dec.c`) on portable scalar x86_64 Linux LP64.

## Scope

- **`.7z` container and coder DAG (`7zArcIn.c`, `7zDec.c`):** two-stage `EncodedHeader` parsing,
  `CSzFolder` / `BindPairs` DAG validation, `SubStreams` slicing, and `SzArEx_Extract` solid-folder caching.
- **BCJ2 4-stream x86 filter (`Bcj2.c`):** range-coded relative call/jump reconstruction across four input streams.
- **PPMd7 context decoder and sub-allocator (`Ppmd7.c`, `Ppmd7Dec.c`):** arena partition invariants,
  `SplitBlock` / `GlueFreeBlocks` free lists, and 32-bit offset-pointer context trees.
- **LZMA and LZMA2 decoders (`LzmaDec.c`, `Lzma2Dec.c`):** circular dictionary indexing, fast lookahead margins,
  and per-chunk state resets.

## What is proved so far

Top-down state-machine and arena models (`SevenZipF.Model`) and strict ISO C17 runtime undefined-behaviour
rejections (`SevenZipF.Runtime`) are kernel-checked in Lean 4. Statement-by-statement C translation and
end-to-end public C entry-point safety proofs are not done.

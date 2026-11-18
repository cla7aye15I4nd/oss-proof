# 7zip-f

Kernel-checked Lean 4 top-down modeling and safety verification of the official `7-Zip` pure-C SDK
(`C/7zArcIn.c`, `C/7zDec.c`, `C/Bcj2.c`, `C/Ppmd7.c`, `C/Ppmd7Dec.c`, `C/LzmaDec.c`, `C/Lzma2Dec.c`)
for the portable scalar x86_64 Linux LP64 build.

## Scope

Covers the zero-dependency ANSI C SDK embedded in 7-Zip, ClamAV, UEFI EDK2 firmware, and commercial
mail/endpoint scanners:

- **`.7z` container & coder DAG (`7zArcIn.c`, `7zDec.c`):** two-stage `EncodedHeader` decompression,
  `CSzFolder` / `BindPairs` DAG validation, `SubStreams` slicing, and `SzArEx_Extract` folder cache.
- **BCJ2 4-stream x86 filter (`Bcj2.c`):** synchronized 4-stream range-coded jump reconstruction.
- **PPMd7 context model & custom sub-allocator (`Ppmd7.c`, `Ppmd7Dec.c`):** arena layout,
  `SplitBlock` / `GlueFreeBlocks` free lists, and 32-bit offset-pointer context trees.
- **LZMA / LZMA2 decoders (`LzmaDec.c`, `Lzma2Dec.c`):** range decoder, fast lookahead loop margins,
  and per-chunk state/dictionary resets.

See `AGENTS.md` for working rules and `SevenZipF/Model/` for the top-down Lean 4 state and safety
invariant models.

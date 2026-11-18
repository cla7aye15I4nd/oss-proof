# Zstandard (`libzstd` decoder)

Verification target: Meta Zstandard's standalone C decoder (`lib/zstd.h`, `lib/zstd_errors.h`,
`lib/decompress/*.c`, and the six `lib/common/*.c` units linked by the decoder) on portable scalar
x86_64 Linux LP64 (`-DZSTD_DISABLE_ASM -DDYNAMIC_BMI2=0 -DZSTD_LEGACY_SUPPORT=0`).

## Scope

- **Streaming and context lifecycle:** `ZSTD_createDCtx`, `ZSTD_freeDCtx`, `ZSTD_DCtx_setParameter`,
  `ZSTD_DCtx_reset`, and `ZSTD_decompressStream` across arbitrary input/output buffer splits.
- **One-shot decompression:** `ZSTD_decompress`, `ZSTD_decompressDCtx`, `ZSTD_decompress_usingDict`,
  and `ZSTD_decompress_usingDDict`.
- **Dictionaries and prefixes:** `ZSTD_createDDict`, `ZSTD_freeDDict`, `ZSTD_DCtx_loadDictionary`,
  `ZSTD_DCtx_refDDict`, and `ZSTD_DCtx_refPrefix` (including `0xEC30A437` formatted dictionaries).
- **Frame queries:** `ZSTD_getFrameContentSize`, `ZSTD_findFrameCompressedSize`, and error/version queries.

The compressor (`lib/compress/`), dictionary builder (`lib/dictBuilder/`), legacy v0.1–v0.7 decoders,
and handwritten assembly are not planned.

## What is proved so far

The strict ISO C17 heap and pointer runtime (`ZstdF.Runtime`) is kernel-checked in Lean 4, including
rejection of cross-object `virtualStart` pointer subtraction and zero-offset null/dangling pointer arithmetic.
Statement-by-statement C translation and public decoder safety proofs are not done.

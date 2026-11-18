# Brotli (`libbrotlidec`)

Verification target: Google Brotli's C decoder (`c/include/brotli/decode.h`, `c/dec/*.c`, and its
`c/common/*.c` dependencies) on portable scalar x86_64 Linux LP64 (`BROTLI_BUILD_PORTABLE`).

## Scope

- **Streaming and one-shot decompression:** `BrotliDecoderDecompressStream` across arbitrary suspension and
  resumption states (`SUCCESS`, `NEEDS_MORE_INPUT`, `NEEDS_MORE_OUTPUT`, `ERROR`) and `BrotliDecoderDecompress`.
- **Zero-copy output borrows:** `BrotliDecoderHasMoreOutput` and `BrotliDecoderTakeOutput` ringbuffer slice
  validity until the next mutating call.
- **Lifecycle, parameters, and dictionaries:** `BrotliDecoderCreateInstance`, `BrotliDecoderDestroyInstance`,
  `BrotliDecoderSetParameter`, `BrotliDecoderAttachDictionary`, and error/version queries.

The encoder (`c/enc/`) is not planned.

## What is proved so far

The strict ISO C17 heap and pointer runtime (`BrotliF.Runtime`) is kernel-checked in Lean 4. Statement-by-statement
C translation of `libbrotlidec` and public decoder safety proofs are not done.

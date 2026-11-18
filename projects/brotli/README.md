# brotli-f

Kernel-checked Lean 4 safety verification of Google Brotli's C decoder (`libbrotlidec`:
`c/include/brotli/decode.h`, `c/dec/`, and its `c/common/` dependencies) for the default scalar
x86_64 Linux LP64 build.

## Scope

Full safety — no undefined behaviour, no out-of-bounds access, no dangling zero-copy borrow, no
memory leak, and termination — across every public function of `decode.h` and every call sequence:

- `BrotliDecoderCreateInstance`, `BrotliDecoderDestroyInstance`
- `BrotliDecoderSetParameter`, `BrotliDecoderAttachDictionary`
- `BrotliDecoderDecompressStream`, `BrotliDecoderDecompress`
- `BrotliDecoderHasMoreOutput`, `BrotliDecoderTakeOutput`
- `BrotliDecoderIsUsed`, `BrotliDecoderIsFinished`
- `BrotliDecoderGetErrorCode`, `BrotliDecoderErrorString`, `BrotliDecoderVersion`

See `AGENTS.md` for working rules, translation discipline, and proof acceptance criteria.

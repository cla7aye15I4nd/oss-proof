# Status of the results

Overall library status: **not done**.

| Area | Kind | Status |
| --- | --- | --- |
| Strict ISO C17 pointer and `memset` UB rejection (`BrotliF.Runtime`) | Runtime model | done |
| `BrotliDecoderDecompressStream` streaming state-machine safety | Public C API | not done |
| `BrotliDecoderDecompress` one-shot decompression safety | Public C API | not done |
| `BrotliDecoderTakeOutput` zero-copy borrow validity | Public C API | not done |
| `BrotliDecoderCreateInstance` / `AttachDictionary` / `DestroyInstance` safety | Public C API | not done |
| Encoder (`c/enc/`) | Out of scope | not planned |

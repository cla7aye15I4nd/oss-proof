# Status of the results

Overall library status: **not done**.

| Area | Kind | Status |
| --- | --- | --- |
| Strict ISO C17 pointer and `memset` UB rejection (`ZstdF.Runtime`) | Runtime model | done |
| `ZSTD_decompressStream` and `ZSTD_DCtx` lifecycle safety | Public C API | not done |
| `ZSTD_decompress` and one-shot decompression safety | Public C API | not done |
| `ZSTD_DDict` and borrowed dictionary/prefix safety | Public C API | not done |
| Frame inspection and error/version query safety | Public C API | not done |
| Compressor (`lib/compress/`) and legacy v0.1–v0.7 decoders | Out of scope | not planned |

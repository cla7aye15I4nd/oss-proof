# Status of the results

Overall library status: **not done**.

| Area | Kind | Status |
| --- | --- | --- |
| Strict ISO C17 pointer and `memset` UB rejection (runtime) | Runtime model | done |
| `zlibVersion`, `zlibCompileFlags`, `zError`: safety and values | Public C API | done |
| `zcalloc` / `zcfree`, `zng_alloc_aligned` / `zng_free_aligned`: safety and alignment | Internal helpers | done |
| `adler32`, `adler32_z`: safety and checksum value | Public C API | not done |
| `adler32_combine`, `adler32_combine64`: safety and combination value | Public C API | done |
| `get_crc_table`, `crc32`, `crc32_z`: safety | Public C API | done |
| `crc32_combine`, `crc32_combine64`, `crc32_combine_gen`, `crc32_combine_gen64`, `crc32_combine_op`: safety and rejection values | Public C API | done |
| `compressBound`: safety and exact value | Public C API | done |
| Streaming `deflate*` safety | Public C API | not done |
| `inflateUndermine`: safety | Public C API | done |
| Streaming `inflate*` safety (the other functions) | Public C API | not done |
| `inflateBack*` safety | Public C API | not done |
| `compress`, `compress2` safety | Public C API | not done |
| `uncompress`, `uncompress2`, `uncompress_z`, `uncompress2_z` safety | Public C API | not done |
| `gz*` file functions safety | Public C API | not done |
| `deflate` / `inflate` round trip | Functional | not done |

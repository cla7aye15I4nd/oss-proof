# Status of the results

Overall library status: **not done**.

| Area | Kind | Status |
| --- | --- | --- |
| Strict ISO C17 pointer and `memset` UB rejection (runtime) | Runtime model | done |
| `zlibVersion`, `zlibCompileFlags`, `zError`: safety and values | Public C API | done |
| `zcalloc` / `zcfree`, `zng_alloc_aligned` / `zng_free_aligned`: safety and alignment | Internal helpers | done |
| `adler32`, `adler32_z`: safety | Public C API | done |
| `adler32`, `adler32_z`: checksum value | Public C API | not done |
| `adler32_combine`, `adler32_combine64`: safety and combination value | Public C API | done |
| `get_crc_table`, `crc32`, `crc32_z`: safety | Public C API | done |
| `crc32_combine`, `crc32_combine64`, `crc32_combine_gen`, `crc32_combine_gen64`, `crc32_combine_op`: safety and rejection values | Public C API | done |
| `compressBound`: safety and exact value | Public C API | done |
| `deflateInit_`, `deflateInit2_`: safety | Public C API | done |
| Other streaming `deflate*` functions: safety | Public C API | not done |
| `inflateInit_`, `inflateInit2_`, `inflateUndermine`: safety | Public C API | done |
| `inflate`, `inflateEnd`, `inflateReset`, `inflateReset2`, `inflateResetKeep`, `inflatePrime`, `inflateSetDictionary`, `inflateGetDictionary`, `inflateGetHeader`, `inflateSync`, `inflateSyncPoint`, `inflateCopy`, `inflateValidate`, `inflateMark`, `inflateCodesUsed`: safety | Public C API | done |
| `inflateBackInit_`: safety | Public C API | done |
| `inflateBack`, `inflateBackEnd`: safety | Public C API | done |
| `compress`, `compress2`, `compress_z`, `compress2_z` safety | Public C API | not done |
| `uncompress`, `uncompress2`, `uncompress_z`, `uncompress2_z` safety | Public C API | done |
| `gzopen`, `gzopen64`, `gzdopen`: safety; some `gzopen` call returns a reachable file in each mode | Public C API | done |
| Other `gz*` file functions: safety | Public C API | not done |
| `deflate` / `inflate` round trip | Functional | not done |

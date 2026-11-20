# zlib-ng-f

Kernel-checked Lean 4 verification of zlib-ng, `develop` branch at commit `5f1f4899` (`ZLIB_COMPAT` x86_64 Linux LP64 build with the
generic C kernels: `-DZLIB_COMPAT=ON -DWITH_OPTIM=OFF -DWITH_CRC32_CHORBA=OFF
-DWITH_RUNTIME_CPU_DETECTION=OFF`), with nineteen patches.

Proved so far: safety of the version, error-string, checksum (`adler32*`, `crc32*`) and
`compressBound` functions with functional theorems for most of them, the strict ISO C17 runtime, and
safety of the streaming `inflate*` and `inflateBack*` functions, `uncompress*`, the streaming
`deflate*` functions, and `gzopen`, `gzopen64`, `gzdopen`. One-shot `compress*`, the other `gz*`
functions and the `deflate` / `inflate` round trip are not done; `tests/audit/public-api.json` lists every public function as done or
not done. Differential tests against the real C (`tests/`) are evidence of translation fidelity, not
proof.

Status: https://www.dataisland.org/oss-proof/zlib-ng/en/progress.html

See `AGENTS.md` for working rules.

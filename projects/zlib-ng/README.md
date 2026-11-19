# zlib-ng-f

Kernel-checked Lean 4 verification of zlib-ng 2.3.3 (`ZLIB_COMPAT` x86_64 Linux LP64 build with the
generic C kernels: `-DZLIB_COMPAT=ON -DWITH_OPTIM=OFF -DWITH_CRC32_CHORBA=OFF
-DWITH_RUNTIME_CPU_DETECTION=OFF`), with seven patches.

Proved so far: safety of `zlibVersion`, `zlibCompileFlags`, `zError`, `adler32`, `adler32_z`,
`adler32_combine`, `adler32_combine64`, `get_crc_table`, `crc32`, `crc32_z`, the five
`crc32_combine*` functions and `compressBound`, functional theorems for most of them, and the
strict ISO C17 runtime. Streaming `deflate*` / `inflate*`, one-shot `compress*` / `uncompress*` and
the `gz*` family are not done; `tests/audit/public-api.json` lists every public function as done or
not done. Differential tests against the real C (`tests/`) are evidence of translation fidelity, not
proof.

Status: https://www.dataisland.org/oss-proof/zlib-ng/en/progress.html

See `AGENTS.md` for working rules.

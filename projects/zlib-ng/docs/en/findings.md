# Findings: issues found in zlib-ng

The work found three issues in the zlib-ng `develop` branch at the verified commit. Each is a defect of zlib-ng
itself, is reached through functions that `zlib.h` documents, and is shown by a run of the real C (or, for one, by
the letter of ISO C17). Patches 0003, 0004 and 0006 fix them.

| Issue | What is wrong | Calls that reach it | Evidence | Fix | Upstream |
| --- | --- | --- | --- | --- | --- |
| `inflateCopy` compares unrelated pointers | `inflateCopy` compares a pointer into the static table `lenfix` with a pointer into the heap state using `>=` and `<=`: undefined behaviour (ISO C17 §6.5.8p5). | `inflateCopy` of a stream that is inside a fixed-code block | AddressSanitizer pointer-pair check, `inflate.c:1410` | Patch 0003 | not submitted |
| `gzseek` offset overflow | `gzseek64` with `SEEK_CUR` adds the pending skip to the offset without a bound: signed 64-bit overflow. Before the first read it also adds 0 to the never-set `x.next`. | `gzopen` for writing, `gzseek(file, INT64_MAX, SEEK_SET)`, `gzseek(file, 1, SEEK_CUR)` | UndefinedBehaviorSanitizer, `gzlib.c:412` | Patch 0004 | not submitted |
| `deflateBound` too small with a large gzip extra length | For a user gzip header with an extra field, `deflateBound` adds `2 + extra_len` in 32-bit `unsigned`, which wraps for `extra_len >= 0xfffffffe`, while `deflate` writes `2 + (extra_len & 0xffff)` header bytes. One `deflate(Z_FINISH)` with `avail_out = deflateBound(...)` then does not return `Z_STREAM_END`, against `zlib.h`. | `deflateInit2` for gzip, `deflateSetHeader` with `extra_len = 0xffffffff`, `deflateBound`, `deflate(Z_FINISH)` | A run of the real C returns `Z_OK` instead of `Z_STREAM_END` | Patch 0006 | not submitted |

Issues found in the earlier 2.3.3 release (`gzbuffer` size overflow, `crc32_combine*` not returning for a negative
length, `adler32` with `NULL` and length 1) are fixed on the `develop` branch; their reproductions remain as
regression tests.

The runs were made on an LP64 build of the verified sources in the verified configuration (see the
[overview](index.html)), with every patch except the one that fixes the issue, not on the x86_64 Linux target
itself. With every patch, each of these calls runs without a sanitizer report and returns.

A sanitizer report or a run of the real C is evidence about that run. It is not a proof. The safety theorems are
about the patched source.

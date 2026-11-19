# Findings: issues found in zlib-ng

The work found seven issues in the zlib-ng `develop` branch at the verified commit. Each is a defect of zlib-ng
itself, is reached through functions that `zlib.h` documents, and is shown by a run of the real C (or, where a
sanitizer cannot see it, by the letter of ISO C17 on a traced run). Patches 0003, 0004, 0006, 0007, 0008, 0009 and
0010 fix them.

| Issue | What is wrong | Calls that reach it | Evidence | Fix | Upstream |
| --- | --- | --- | --- | --- | --- |
| `inflateCopy` compares unrelated pointers | `inflateCopy` compares a pointer into the static table `lenfix` with a pointer into the heap state using `>=` and `<=`: undefined behaviour (ISO C17 §6.5.8p5). | `inflateCopy` of a stream that is inside a fixed-code block | AddressSanitizer pointer-pair check, `inflate.c:1410` | Patch 0003 | not submitted |
| `gzseek` offset overflow | `gzseek64` with `SEEK_CUR` adds the pending skip to the offset without a bound: signed 64-bit overflow. Before the first read it also adds 0 to the never-set `x.next`. | `gzopen` for writing, `gzseek(file, INT64_MAX, SEEK_SET)`, `gzseek(file, 1, SEEK_CUR)` | UndefinedBehaviorSanitizer, `gzlib.c:412` | Patch 0004 | not submitted |
| `deflateBound` too small with a large gzip extra length | For a user gzip header with an extra field, `deflateBound` adds `2 + extra_len` in 32-bit `unsigned`, which wraps for `extra_len >= 0xfffffffe`, while `deflate` writes `2 + (extra_len & 0xffff)` header bytes. One `deflate(Z_FINISH)` with `avail_out = deflateBound(...)` then does not return `Z_STREAM_END`, against `zlib.h`. | `deflateInit2` for gzip, `deflateSetHeader` with `extra_len = 0xffffffff`, `deflateBound`, `deflate(Z_FINISH)` | A run of the real C returns `Z_OK` instead of `Z_STREAM_END` | Patch 0006 | not submitted |
| `inflate` compares window and output pointers | When a match reaches back into the sliding window, `inflate` (state `MATCH`) calls `chunkcopy_safe`, and `inflate_fast` calls `CHUNKCOPY_SAFE` and `chunkmemset`, with `from` in the window (inside inflate's own allocation) and `out` in the caller's output buffer. They compare these pointers with `>=`, `<` and subtract them: undefined behaviour (ISO C17 §6.5.8p5, §6.5.6p9). | `inflate` of a valid zlib stream whose matches reach into the window, with a small `avail_out` per call | AddressSanitizer pointer-pair check, `inflate_p.h:224`, `inflate_p.h:225`, `chunkset_tpl.h:119`, `chunkset_tpl.h:125`, `chunkset_tpl.h:319` | Patch 0007 | not submitted |
| `inflateSync` adds 0 to a null `next_in` | With no input (`next_in == NULL`, `avail_in == 0`) but at least 8 bits primed by `inflatePrime`, `inflateSync` runs `strm->next_in += len` with `len == 0`: `NULL + 0` (ISO C17 §6.5.6p8). | `inflateInit`, `inflatePrime(strm, 16, v)`, `inflateSync` | Traced run (returns `Z_DATA_ERROR` after the addition); UndefinedBehaviorSanitizer does not report `NULL + 0` in C | Patch 0008 | not submitted |
| `inflateSetDictionary` accepts a null dictionary | `zlib.h` says a `NULL` dictionary is an invalid parameter (`Z_STREAM_ERROR`). On a raw stream, `inflateSetDictionary(strm, NULL, 0)` instead calls `updatewindow` with `end = NULL + 0`, which computes `end - 0` and calls `memcpy` with a null source and length 0 (ISO C17 §6.5.6p8, §7.24.1p2), and returns `Z_OK`. | `inflateInit2(strm, -15)`, `inflateSetDictionary(strm, NULL, 0)` | Traced run (returns `Z_OK`) | Patch 0009 | not submitted |
| `inflate` moves `next_in` before the input after `inflatePrime` | `inflate_fast` assumes fewer than 8 bits in the bit buffer on entry and, on exit, gives back `bits >> 3` bytes of input (`in -= len`). After `inflatePrime` has put up to 32 bits there, it gives back more bytes than it read: `next_in` points before the caller's buffer (ISO C17 §6.5.6p8), `avail_in` is larger than the caller gave and `total_in` wraps below 0. | `inflateInit2(strm, -15)`, `inflatePrime(strm, 16, 3)`, `inflatePrime(strm, 16, 0)`, `inflate` with 32 bytes of input | A run of the real C: `avail_in` 34 after a call with 32, `total_in` 4294967294 | Patch 0010 | not submitted |

Issues found in the earlier 2.3.3 release (`gzbuffer` size overflow, `crc32_combine*` not returning for a negative
length, `adler32` with `NULL` and length 1) are fixed on the `develop` branch; their reproductions remain as
regression tests.

The runs were made on an LP64 build of the verified sources in the verified configuration (see the
[overview](index.html)), with every patch except the one that fixes the issue, not on the x86_64 Linux target
itself. With every patch, each of these calls runs without a sanitizer report and returns.

A sanitizer report or a run of the real C is evidence about that run. It is not a proof. The safety theorems are
about the patched source.

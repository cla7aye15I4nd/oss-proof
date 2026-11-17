# Findings: issues found in zlib

The work found eight issues in zlib. Each is a defect of zlib itself, is reached through documented
use of the functions `zlib.h` documents, and is shown by a run of the real C. A
[patch](../../patches/README.md) fixes seven of them.
Six are undefined behaviour or a memory error. Two are broken promises of `deflateBound`: the
bound is too small, and no behaviour is undefined.

| Issue | What is wrong | Calls that reach it | Evidence | Fix | Upstream |
| --- | --- | --- | --- | --- | --- |
| `inflateCopy` compares unrelated pointers | `inflateCopy` compares a pointer into a static table with a pointer into the heap state using `>=` and `<=`: undefined behaviour. No wrong result was observed. | `inflateCopy` of a stream that has decoded a fixed block and no dynamic block after it | AddressSanitizer pointer-pair check, `inflate.c:1383` | Patch 0001 | [PR #1369](https://github.com/madler/zlib/pull/1369), answered "Applied"; not in zlib 1.4 |
| `gzseek` after an initial `gzungetc` | The position is -1 after the push, and the range checks of `gzseek64` overflow signed 64-bit arithmetic. | `gzopen`, `gzungetc`, then `gzseek` | UndefinedBehaviorSanitizer, `gzlib.c:395`, `403`, `424` | Patch 0002 | [PR #1361](https://github.com/madler/zlib/pull/1361), open |
| `gzread` copies from a stale `x.next` | When `read()` returns some bytes and then fails, `gz_fetch` returns before it sets `x.next`, and the reader copies from the old pointer: a heap read outside the output buffer. | `gzread` on input that is not gzip, when the descriptor fails after partial data | AddressSanitizer, `gzread.c:369` | Patch 0003 | [PR #1363](https://github.com/madler/zlib/pull/1363), open |
| gz position overflow, reading | The readers add to the signed 64-bit position `x.pos` without a bound: signed overflow in `gz_read`, `gzgetc` and the `gzgetc()` macro. | `gzseek` to near 2^63 on a device whose `lseek` succeeds without moving (Linux `/dev/zero`), then `gzread` or `gzgetc` | UndefinedBehaviorSanitizer on x86_64 Linux | Patch 0004 | Local patch, not submitted |
| gz position overflow, writing | The writers add to `x.pos` without a bound: signed overflow in `gz_write` and `gzputc`. | `gzseek` forward to near 2^63 on a writer that does not compress, to a sink that accepts the zeros (`/dev/null`), then `gzwrite` or `gzputc` | UndefinedBehaviorSanitizer, `gzwrite.c:230`, `352` | Patch 0005 | Local patch, not submitted |
| `gzoffset64` on a negative descriptor offset | `gzoffset64` takes only `-1` from `lseek` as a failure. With another negative result, the subtraction of the buffered input overflows signed 64-bit arithmetic. | `gzdopen` on a descriptor whose `lseek` returns negative offsets (Linux `/proc/<pid>/mem`), `gzread`, the caller moves the descriptor to a large negative offset, then `gzoffset64` | UndefinedBehaviorSanitizer, `gzlib.c:494` | Patch 0006 | Local patch, not submitted |
| `deflateBound` is too small for `Z_FIXED` | Broken promise: one `deflate(Z_FINISH)` call with `deflateBound` bytes of room returns `Z_OK`. For 1,000,000 input bytes the bound is 1,000,318 and the stream needs up to 1,008,570 bytes. | `deflateInit2` with `windowBits` 15, `memLevel` 8, `Z_FIXED`, level 1 to 3; `deflateBound`; `deflate`. `compress`, `compress2` and `compressBound` are not affected. | A run of the real C returns `Z_OK` | Patch 0007 | Local patch, not submitted |
| `deflateBound` with a gzip extra field of length 2^32 − 2 or 2^32 − 1 | Broken promise: `2 + extra_len` wraps at 32 bits, the bound is about 64 KiB too small, and `deflate(Z_FINISH)` with that room returns `Z_OK`. | `deflateSetHeader` with one of the two lengths, `deflateBound`, `deflate`. `zlib.h` puts no upper limit on `extra_len`; a gzip header holds at most 65535 bytes of extra field. | A run of the real C returns `Z_OK` | None | Known upstream ([PR 1360](https://github.com/madler/zlib/pull/1360)) |

The verified source is zlib 1.4 (upstream commit `99623ef7`) with the seven patches. The runs of
the real C were made on `99623ef7` or on upstream commit `757f0527`, its direct parent, each
without the patch that fixes the issue. Between the two commits the C sources of the library
differ only in
the version and copyright strings and in the last two entries of the table `lext` of
`inftrees.c`.

A sanitizer report or a run of the real C is evidence about that run. It is not a proof. The
safety theorems are about the patched source.

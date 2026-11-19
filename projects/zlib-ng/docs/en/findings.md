# Findings: issues found in zlib-ng

The work found five issues in zlib-ng 2.3.3. Each is a defect of zlib-ng itself, is reached
through functions that `zlib.h` documents, and is shown by a run of the real C. Patches 0001 to
0004 and patch 0007 fix them.

| Issue | What is wrong | Calls that reach it | Evidence | Fix | Upstream |
| --- | --- | --- | --- | --- | --- |
| `gzbuffer` size overflow | `gzbuffer` accepts sizes up to `0x7fffffff`. `gz_buffer_alloc` then computes `want * 2` in `int` (signed overflow), and `zng_alloc_aligned` adds `sizeof(void *) + size + align` in 32 bits, which wraps to 8: it allocates 8 bytes and writes the saved pointer outside the block. | `gzopen` for writing, `gzbuffer(file, 0x55555540)`, `gzwrite` | UndefinedBehaviorSanitizer, `gzlib.c:76`; AddressSanitizer heap-buffer-overflow, `zutil.c:135` | Patch 0001 | not submitted |
| `crc32_combine*` do not return | With a negative `len2`, `x2nmodp` shifts `-1` right forever; with `op == 0`, `multmodp` never finds a set bit. | `crc32_combine(crc1, crc2, -1)`, `crc32_combine_gen(-1)`, `crc32_combine_op(crc1, crc2, 0)` | A run of the real C does not return within 10 seconds | Patch 0002 | not submitted |
| `inflateCopy` compares unrelated pointers | `inflateCopy` compares a pointer into the static table `lenfix` with a pointer into the heap state using `>=` and `<=`: undefined behaviour (ISO C17 §6.5.8p5). | `inflateCopy` of a stream that is inside a fixed-code block | AddressSanitizer pointer-pair check, `inflate.c:1399` | Patch 0003 | not submitted |
| `gzseek` offset overflow | `gzseek64` with `SEEK_CUR` adds the pending skip to the offset without a bound: signed 64-bit overflow. | `gzopen` for writing, `gzseek(file, INT64_MAX, SEEK_SET)`, `gzseek(file, 1, SEEK_CUR)` | UndefinedBehaviorSanitizer, `gzlib.c:388` | Patch 0004 | not submitted |
| `adler32` with `NULL` and length 1 | `zlib.h` says that `adler32` with `buf == Z_NULL` returns the initial value. zlib-ng handles `len == 1` before it tests for `NULL`, and reads through the null pointer. | `adler32(1, Z_NULL, 1)` | UndefinedBehaviorSanitizer null load, `adler32_p.h:22`; AddressSanitizer SEGV | Patch 0007 | not submitted |

The runs were made on an LP64 build of the zlib-ng 2.3.3 sources in the verified configuration
(see the [overview](index.html)), with every patch except the one that fixes the issue, not on the
x86_64 Linux target itself. With every patch, each of these calls runs without a sanitizer report
and returns.

A sanitizer report or a run of the real C is evidence about that run. It is not a proof. The
safety theorems are about the patched source.

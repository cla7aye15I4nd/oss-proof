# Patches

The verified source is zlib-ng 2.3.3 plus the patches below, applied in name order. Every patch is
**local and pending**: none has been submitted upstream yet. Each is replaced by the upstream fix
once one exists, and deleted once the pin moves past it.

| Patch | Files | What it changes | Defect it addresses | Confirmed on real C |
| --- | --- | --- | --- | --- |
| `0001-gzbuffer-aligned-alloc-overflow.patch` | `gzlib.c`, `zutil.c` | `gzbuffer` rejects `size > INT_MAX / 3`; `gz_buffer_alloc` computes sizes in `uint32_t`; `zng_alloc_aligned` returns `NULL` for `align == 0` or when `sizeof(void *) + size + align` would exceed `SIZE_MAX`, and computes the size in `size_t`. | `gzbuffer` accepts sizes up to `0x7fffffff`; `gz_buffer_alloc` then overflows `int` (`want * 2`), and `zng_alloc_aligned` wraps its 32-bit size, allocates too little and writes the saved pointer outside the block. | yes (signed overflow and heap overflow) |
| `0002-crc32-combine-negative-len-hang.patch` | `crc32_braid_comb.c` | `crc32_combine_gen_` returns 0 for `len2 < 0`; `crc32_combine_op_` returns 0 for `op == 0`; `crc32_combine_` is expressed through those two. | `x2nmodp` never ends for a negative length, and `multmodp` never ends for `op == 0`. | yes (the calls do not return) |
| `0003-inflate-copy-pointer-equality.patch` | `inflate.c` | `inflateCopy` tests `state->lencode == state->codes` instead of a `>=` / `<=` range test. | The range test compares a pointer into the static fixed-code table with a pointer into the heap state (ISO C17 §6.5.8p5). | yes (pointer-pair check) |
| `0004-gzseek-and-gzoffset-overflow.patch` | `gzguts.h`, `gzlib.c` | `gzseek64` computes the target position with explicit range checks against `GZ_OFF_MAX`, skips the buffer update when `n == 0`, and tests the raw-area condition without overflow; `gzoffset64` treats every negative `lseek` result as failure. | Signed 64-bit overflow in the offset arithmetic of `gzseek64` and `gzoffset64`. | `gzseek64` yes; `gzoffset64` part not confirmed |
| `0005-gzread-stale-next.patch` | `gzread.c` | In `gz_fetch`, case `COPY`, sets `state->x.next = state->out` before `gz_load` instead of after it. | When `gz_load` fails after a partial read, `x.next` keeps a stale value. | not confirmed |
| `0006-deflatebound-gzip-extra-length.patch` | `deflate.c` | `deflateBound` adds `2 + (extra_len & 0xffff)` for a user gzip header with an extra field. | `2 + extra_len` is computed in 32-bit `unsigned` and can wrap. | not confirmed |
| `0007-adler32-null-before-len-1.patch` | `arch/generic/adler32_c.c` | `adler32_c` tests `buf == NULL` (returning 1) before the `len == 1` fast path instead of after it. | `zlib.h` documents that a `Z_NULL` buffer returns the initial value for any length, but `adler32_c` handles `len == 1` first and reads `buf[0]` through the null pointer. | yes (null load) |

Confirmed defects are described in the findings page of the project documentation.

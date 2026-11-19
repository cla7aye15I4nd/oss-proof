# Patches

The verified source is the zlib-ng `develop` branch at commit `5f1f4899` plus the patches below, applied in name
order. Every patch is **local and pending**: none has been submitted upstream yet. Each is replaced by the upstream
fix once one exists, and deleted once the pin moves past it.

| Patch | Files | What it changes | Defect it addresses | Confirmed on real C |
| --- | --- | --- | --- | --- |
| `0003-inflate-copy-pointer-equality.patch` | `inflate.c` | `inflateCopy` tests `state->lencode == state->codes` instead of a `>=` / `<=` range test. | The range test compares a pointer into the static fixed-code table with a pointer into the heap state (ISO C17 §6.5.8p5). | yes (pointer-pair check) |
| `0004-gzseek-overflow.patch` | `gzguts.h`, `gzlib.c` | `gzseek64` computes the target position with explicit range checks against `GZ_OFF_MAX`, and skips the buffer update when `n == 0`. | Signed 64-bit overflow in the offset arithmetic of `gzseek64` (`SEEK_CUR` adds the pending skip without a bound); `state->x.next += 0` on a never-set `x.next` when `gzseek` is called before the first read (wild pointer `+ 0`, ISO C17 §6.5.6p8). | overflow yes (UBSan); `x.next + 0` by the letter of the standard |
| `0006-deflatebound-gzip-extra-length.patch` | `deflate.c` | `deflateBound` adds `2 + (extra_len & 0xffff)` for a user gzip header with an extra field. | `2 + extra_len` is computed in 32-bit `unsigned` and wraps for `extra_len >= 0xfffffffe`, so the bound is below what one `deflate(Z_FINISH)` writes, against the promise of `zlib.h`. Not undefined behaviour. | yes (`deflate` does not return `Z_STREAM_END`) |
| `0007-inflate-window-copy.patch` | `inflate.c`, `inffast_tpl.h` | A match copied from the sliding window to the output is copied with `memcpy(out, from, n); out += n;` instead of `chunkcopy_safe` / `CHUNKCOPY_SAFE` (state `MATCH` of `inflate`, and the four window copies of `inflate_fast`). The copy length already fits the output (`copy <= left`; `inflate_fast` keeps 258 bytes of room, or bails out to `MATCH` in safe mode), and the window and the output never overlap, so the result is the same. | `chunkcopy_safe`, `CHUNKCOPY_SAFE` and `chunkmemset` compare (`>=`, `<`) and subtract a pointer into the window and a pointer into the caller's output, which point into different objects (ISO C17 §6.5.8p5, §6.5.6p9). | yes (pointer-pair check) |
| `0008-inflatesync-null-next-in.patch` | `inflate.c` | `inflateSync` advances `next_in` only when `syncsearch` consumed bytes. | With `next_in == NULL`, `avail_in == 0` and at least 8 primed bits, `strm->next_in += 0` is `NULL + 0` (ISO C17 §6.5.6p8). | by the letter of the standard on a traced run (no sanitizer reports `NULL + 0` in C) |
| `0009-inflatesetdictionary-null.patch` | `inflate.c` | `inflateSetDictionary` returns `Z_STREAM_ERROR` for a `NULL` dictionary, as `zlib.h` documents, before any other step. | `inflateSetDictionary(strm, NULL, 0)` on a raw stream computes `NULL + 0`, `NULL - 0` and calls `memcpy` from `NULL` (ISO C17 §6.5.6p8, §7.24.1p2), and returns `Z_OK`. | by the letter of the standard on a traced run; the return value differs (`Z_OK` vs `Z_STREAM_ERROR`) |
| `0010-inflate-fast-primed-bits.patch` | `inflate.c` | `inflate` (state `LEN`) calls `inflate_fast` only when fewer than 8 bits are held (`bits < 8`), which `inflate_fast` assumes; otherwise it decodes the code in `inflate` itself. Without `inflatePrime` fewer than 8 bits are always held there, so nothing else changes. | When `inflatePrime` has left 8 or more bits in the bit buffer, `inflate_fast` returns `bits >> 3` bytes of input on exit (`in -= len`, `inffast_tpl.h:327`), more than it read: `next_in` moves before the caller's buffer (ISO C17 §6.5.6p8), `avail_in` grows past what the caller gave and `total_in` wraps. | yes (`avail_in` and `total_in` after the call); no sanitizer reports the pointer itself |

Patches of the earlier 2.3.3 pin that are gone:

| Patch | Verdict | Evidence |
| --- | --- | --- |
| `0001` (`gzbuffer` size, `zng_alloc_aligned` wrap) | fixed upstream | `gzbuffer` clamps the size to `GZBUFSIZE_MAX` (1 GiB), so `gz_buffer_alloc` asks for at most `3 * 2^30` bytes and `zng_alloc_aligned` cannot wrap; the reproduction runs clean without a patch. |
| `0002` (`crc32_combine*` hangs) | fixed upstream | `crc32_combine_` and `crc32_combine_gen_` return 0 for `len2 < 0`. `crc32_combine_op` with `op == 0` still does not return, but `zlib.h` only allows an `op` made by `crc32_combine_gen` from a non-negative length, which is never 0. |
| `0005` (`gzread` stale `x.next`) | not a defect | `gz_load` reports a read error through `gz_error`, which sets `x.have = 0`, so the stale `x.next` is never read. |
| `0007` (`adler32` with `NULL` and length 1) | fixed upstream | `adler32` and `adler32_z` test `buf == NULL` before calling `adler32_c`. |

Confirmed defects are described in the findings page of the project documentation.

# Truncate gzhead->extra_len to 16 bits in deflateBound()

## Problem

In `deflateBound_z()`, when a user gzip header specifies `extra != NULL`:

```c
wraplen += 2 + s->gzhead->extra_len;
```

`deflate()` writes only the low 16 bits of `gzhead->extra_len` (`put_short()` and the `EXTRA_STATE` copy loop both mask with `0xffff`; valid gzip headers cap extra fields at 65,535 bytes). Because `extra_len` is 32-bit unsigned (`uint32_t` / `unsigned int`), `2 + s->gzhead->extra_len` is evaluated in 32-bit unsigned arithmetic on every platform before widening to `z_size_t`:

- For `0x10000 <= extra_len <= 0xfffffffd`, `deflateBound()` overestimates by up to 4 GiB.
- For the exact two values `0xfffffffe` and `0xffffffff`, `2 + extra_len` wraps to `0` or `1` instead of `65536` or `65537`, so a single `deflate(strm, Z_FINISH)` with `avail_out == deflateBound()` returns `Z_OK` instead of `Z_STREAM_END` (no buffer overflow occurs).

## Fix

Mask `extra_len` to 16 bits in `deflate.c` to match `deflate()`:

```c
wraplen += 2 + (s->gzhead->extra_len & 0xffff);
```

Because `(s->gzhead->extra_len & 0xffff) <= 65535`, the sum is at most `65537` and cannot wrap in 32-bit unsigned arithmetic, so no cast is needed.

Add `deflate_bound.gzip_extra_len_truncated` in `test/test_deflate_bound.cc` verifying `0xffff`, `UINT32_MAX` (including `deflate(Z_FINISH) == Z_STREAM_END` with an output buffer sized to `deflateBound()`), `0x10000`, and `0`.

## Related Upstream References

- Updates open PR: https://github.com/zlib-ng/zlib-ng/pull/2523
- Related open `madler/zlib` PR: https://github.com/madler/zlib/pull/1360 (`#1360` retains a `(z_size_t)` cast; this PR omits the cast per review feedback and adds GoogleTest coverage).

## Review Feedback Addressed

- Removed the unnecessary cast (`wraplen += 2 + (s->gzhead->extra_len & 0xffff);`).
- Corrected the commit message and description to clarify that 32-bit unsigned wraparound happens on every platform (not only 32-bit `unsigned long`), specify the exact two underestimating values (`0xfffffffe` and `0xffffffff`), and note this is bound-consistency cleanup with no buffer overflow.
- Added an explicit `deflate(Z_FINISH)` check using `avail_out = deflateBound()`.

## Testing

- Clang (`ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, ASan + UBSan) and Clang (`ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`, ASan + UBSan):
  - Before fix: `deflate_bound.gzip_extra_len_truncated` fails (`deflate(Z_FINISH)` returns `Z_OK` instead of `Z_STREAM_END`, and bounds disagree).
  - After fix: passes in both builds.

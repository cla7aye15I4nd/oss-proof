# Mask the gzip extra length in deflateBound()

## Problem

For a user gzip header with `extra != NULL`, `deflateBound_z()` adds `2 + s->gzhead->extra_len`, but `deflate()`
writes only the low 16 bits of `extra_len` (`put_short()` of the `uint16_t` cast, and the `EXTRA_STATE` copy loop
masks with `0xffff`). `2 + extra_len` is `unsigned int` arithmetic on every platform, evaluated before the sum is
widened to `z_size_t`:

- for `0x10000 <= extra_len <= 0xfffffffd` the bound is larger than needed;
- for `0xfffffffe` and `0xffffffff` the sum wraps to `0` or `1`, so the bound is 65536 bytes too small and a single
  `deflate(Z_FINISH)` into `deflateBound()` bytes returns `Z_OK` instead of `Z_STREAM_END`.

No buffer overflow and no undefined behaviour: `deflate()` never writes past `avail_out`. The effect is a bound that
does not keep the promise of `zlib.h` for those two values.

## Fix

Files: `deflate.c`, `test/test_deflate_bound.cc`.

```c
wraplen += 2 + (s->gzhead->extra_len & 0xffff);
```

The masked sum is at most `65537`, so it cannot wrap; the `+=` widens it to `z_size_t`. One commit with the test
`deflate_bound.gzip_extra_len`: for `extra_len` `0xffff`, `0x10000`, `0xfffffffe` and `0xffffffff` it checks that
`deflateBound()` equals the bound of the same header with the 16-bit length, and that one `deflate(Z_FINISH)` into
that many bytes returns `Z_STREAM_END`. It is guarded by `#ifndef TEST_STOCK_ZLIB`, since stock zlib on LP64 adds
the length in `unsigned long` and so overestimates for lengths above 16 bits.

## Related Upstream References

- zlib-ng PR https://github.com/zlib-ng/zlib-ng/pull/2523 (open) carries this fix; this series is the form the
  maintainer asked for there.
- madler/zlib PR https://github.com/madler/zlib/pull/1360 (open) carries the same fix with a `(z_size_t)` cast.

## Review Feedback Addressed

- The cast is dropped: `wraplen += 2 + (s->gzhead->extra_len & 0xffff);`, the exact form requested on #2523.
- The commit message now says that the sum is `unsigned int` arithmetic on every platform, that only `0xfffffffe`
  and `0xffffffff` give a bound that is too small, and that there is no buffer overflow.
- A GoogleTest regression test is added.

## Testing

- `deflate_bound.gzip_extra_len` built with upstream's CMake under AddressSanitizer and UndefinedBehaviorSanitizer:
  it fails without the `deflate.c` change (the bounds for `0x10000`, `0xfffffffe` and `0xffffffff` differ from the
  16-bit bound, and `deflate(Z_FINISH)` returns `Z_OK` for the two wrapping values) and passes with it.

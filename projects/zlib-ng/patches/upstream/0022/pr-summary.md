# Account only consumed zero fill in gz_zero() on write errors

## Problem

In `gz_zero()` (`gzwrite.c`), each zero-fill chunk added the full batch size `n` to `state->x.pos` before calling `gz_comp(state, Z_NO_FLUSH)` and subtracted `n` from `state->skip` only after `gz_comp()` succeeded:

```c
strm->avail_in = n;
strm->next_in = state->in;
state->x.pos += n;
if (gz_comp(state, Z_NO_FLUSH) == -1)
    return -1;
state->skip -= n;
```

When `gz_comp()` failed (for example on `EBADF` or `EAGAIN` on a non-blocking pipe):
1. The failed chunk remained counted in both `state->x.pos` and `state->skip`, so `gztell()` (`x.pos + skip`) exceeded the seeked offset and triggered signed 64-bit overflow after a seek to `GZ_OFF_MAX` (ISO C17 §6.5p5).
2. Calling `gzclearerr()` and retrying a write emitted the unconsumed zero-fill chunk twice, corrupting stream length and `gztell()`.

## Commits & Fix

1. **M0nd0R** (adapted from `madler/zlib@51c7cd2c`): compute consumed bytes (`n -= strm->avail_in`) after `gz_comp(state, Z_NO_FLUSH)`, update both `state->x.pos` and `state->skip` by `n`, and on `ret == -1` discard unconsumed zero-fill bytes (`strm->avail_in = 0; strm->next_in = state->in;`) before returning `-1`.
2. **Zheng Yu**: add `gzip.write_pending_seek_error_preserves_tell` (`O_RDONLY` fd seeked to `off_max`) and `gzip.write_pending_seek_eagain_retry` (non-blocking `pipe()` hitting `EAGAIN` on `gz_zero()`, draining, clearing the error, retrying, and verifying exact output length) in `test/test_gzio.cc`.

## Testing

- Clang (`ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, ASan + UBSan) and Clang (`ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`, ASan + UBSan):
  - Before fix: `gzip.write_pending_seek_error_preserves_tell` aborts under UBSan (`signed integer overflow` in `gztell64()`), and `gzip.write_pending_seek_eagain_retry` writes `14099` bytes instead of `10003`.
  - After fix: both tests pass in both builds.

# PR 0022: Account only consumed zero fill in `gz_zero()` on write errors

- **Proposed PR Title**: `Account only consumed zero fill in gz_zero() on write errors`
- **Target Base**: `zlib-ng/zlib-ng` `develop` (`5f1f4899`)
- **Upstream PR**: Ready to submit (aligns with local proof patch `0022-gzwrite-zero-skip-on-failure.patch`)
- **Commits**: 1 (`upstream.patch`)
- **Files**: `gzwrite.c`, `test/test_gzio.cc`

## Problem & Root Cause

In `gz_zero()` (`gzwrite.c`), each zero-fill chunk added the full chunk size `n` to `state->x.pos` *before* calling `gz_comp(state, Z_NO_FLUSH)` and subtracted `n` from `state->skip` *after*:

```c
strm->avail_in = n;
strm->next_in = state->in;
state->x.pos += n;
if (gz_comp(state, Z_NO_FLUSH) == -1)
    return -1;
state->skip -= n;
```

When `gz_comp()` failed (for example on `EBADF` from an `O_RDONLY` descriptor or `EAGAIN` on a full non-blocking pipe):
1. The failed chunk remained counted in **both** `state->x.pos` and `state->skip`, so `gztell()` (`x.pos + skip`) exceeded the seek target and triggered signed 64-bit overflow after a seek to `GZ_OFF_MAX`.
2. Calling `gzclearerr()` and retrying a write emitted the failed zero chunk twice (producing duplicate zero bytes in the stream and inflating `gztell()`).

## Fix Summary

Adapted from `madler/zlib@51c7cd2c`:

```c
int ret = gz_comp(state, Z_NO_FLUSH);
n -= strm->avail_in;
state->x.pos += n;
state->skip -= n;
if (ret == -1) {
    strm->avail_in = 0;
    strm->next_in = state->in;
    return -1;
}
```

Both `state->x.pos` and `state->skip` advance/decrement by the exact consumed byte count (`n - strm->avail_in`), and unconsumed zero-fill input is discarded on failure before returning `-1`.

Add two GoogleTest cases in `test/test_gzio.cc`:
- `gzip.write_pending_seek_error_preserves_tell` (`O_RDONLY` `gzdopen(..., "wbT")` seeked to `off_max`, failing write + `gzclearerr()` + `gzputc()` preserving `gztell == off_max`);
- `gzip.write_pending_seek_eagain_retry` (non-blocking `pipe()` filled to trigger `EAGAIN` on `gz_zero()` after `gzseek(10000)`, drained, `gzclearerr()`, `gzwrite("abc", 3)`, verifying exact 10,003 bytes written and `gztell == 10003` with no duplicate zeros).

## Overlaps & Dependencies

- **Internal (`gzwrite.c` & `test/test_gzio.cc`)**: completely disjoint from `0014` (`#2527`), `0016`, and `0017`.

## Verification

- `build-compat-san` & `build-native-san`:
  - Before fix (`5f1f4899`): **both** `write_pending_seek_error_preserves_tell` (UBSan signed overflow at `gzlib.c`) and `write_pending_seek_eagain_retry` (`gztell == 14096` / `14099` bytes instead of `10003`) fail.
  - After fix: both tests pass (`[  PASSED  ] 2 tests.`), and pass stacked alongside `0004+0014+0016+0017` (`85 compat / 83 native`).

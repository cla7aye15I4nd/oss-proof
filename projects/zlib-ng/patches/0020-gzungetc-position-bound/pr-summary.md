# Bound the position lowered by gzungetc()

## Problem

`gzungetc()` (`gzread.c`) lowers `x.pos` for each character pushed back. A push into a full output buffer fails with `Z_DATA_ERROR` ("out of room to push characters"); `gz_error()` then drops the buffered characters (`x.have = 0`) but `x.pos` stays lowered. After `gzclearerr()` pushing starts again, so a loop of pushes, a failed push and `gzclearerr()` lowers `x.pos` without a bound, and `x.pos--` overflows after about `2^63` pushes (ISO C17 §6.5p5).

## Fix

`gzungetc()` returns -1 without pushing when `x.pos <= -GZ_OFF_MAX` (after the test `c < 0`), so `x.pos` stays above the minimum value. The bound is `-GZ_OFF_MAX` rather than the minimum because `gzseek64()` negates a negative position. Below the bound nothing changes.

Add `gzfile_api_errors.ungetc_overflow_clearerr_cycles` in `test/test_gzfile_api_errors.cc`: with an 8-byte buffer, three cycles of 16 pushes, a rejected push (`Z_DATA_ERROR`) and `gzclearerr()`; after each cycle `gztell()` is 16 lower, and pushing and reading still work afterwards. The bound itself takes about `2^63` calls to reach, so the test does not fail without the fix; it checks the cycle that lowers the position, which the fix leaves unchanged below the bound.

## Related Upstream References

- None in zlib-ng or madler/zlib: madler/zlib `develop` has no bound on the position lowered by `gzungetc()`.
- Not yet submitted to zlib-ng.

## Review Feedback Addressed

- None yet (not submitted).

## Testing

- Clang, `ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, `-O0`, AddressSanitizer + UndefinedBehaviorSanitizer: passes with the fix.
- Clang, `ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`, same sanitizers: passes.
- The overflow is not reachable in a test (about `2^63` calls). The test shows the mechanism on the C, with and without the fix: `gztell()` decreases by the number of characters pushed in each cycle.

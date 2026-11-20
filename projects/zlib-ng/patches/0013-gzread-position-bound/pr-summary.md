# Bound the read position of the gz readers at GZ_OFF_MAX

## Problem

The gz readers add the bytes they deliver to the signed 64-bit `state->x.pos` without a bound. After `gzseek()` to near the largest `z_off64_t` on a descriptor that accepts the seek and keeps delivering data (Linux `/dev/zero`, or a device), `x.pos += n` in `gz_read()` (`gzread.c`) overflows (ISO C17 §6.5p5). The `gzgetc()` macro of `zlib.h` takes bytes from the output buffer and increments `pos` in the caller's code, so bounding only `gz_read()` is not enough: after `gzseek(file, INT64_MAX - 2, SEEK_SET)` and a `gzread()` of 4 bytes that returns 2, the output buffer still holds bytes and the macro overflows the position in the caller.

## Fix

- `gz_fetch()` asks for at most `GZ_OFF_MAX - x.pos` bytes of output (the `gz_load()` length in copy mode, `avail_out` when inflating) when `x.pos > 0`, and fails with `Z_DATA_ERROR` ("read position does not fit in z_off64_t") at `x.pos == GZ_OFF_MAX`.
- `gz_read()` limits each step to `GZ_OFF_MAX - x.pos` bytes (its direct reads into the caller's buffer bypass the output buffer) and, when that is 0, sets the same error and returns what it has.

So `x.pos + x.have <= GZ_OFF_MAX` holds whenever a call returns: the `gzgetc()` macro reaches at most `GZ_OFF_MAX` and then calls `gzgetc()`, which returns -1. `gzgetc()`'s and `gzgets()`' own copies need no bound (they take at most `x.have` bytes), and neither does `gz_look()`'s copy of the first input (it runs before any data is delivered). Both tests compare in `uint64_t`, since `z_off64_t` may be as narrow as `unsigned` (a 32-bit build without large-file support) and `n` may then not fit in it. Below `GZ_OFF_MAX - 2 * size` nothing changes. `GZ_OFF_MAX` is defined in `gzread.c` unless already defined (the `gzseek64()` fix in https://github.com/zlib-ng/zlib-ng/pull/2525 adds it to `gzguts.h`).

Add `gzip.read_position_limit` in `test/test_gzio.cc`. It opens `/dev/zero` (copy mode), seeks to `GZ_OFF_MAX - 4` (or `- 2`) and reads up to the largest position with `gzgetc()` (the macro in the `zlib.h` API), `gzread()` and `gzgets()`; each stops there with `Z_DATA_ERROR` and `gztell()` returns `GZ_OFF_MAX`. It is skipped where `gzseek()` does not take a `z_off64_t` offset or where `/dev/zero` does not accept the seek.

## Related Upstream References

- Not yet submitted to zlib-ng. The same overflow is reported to madler/zlib in https://github.com/madler/zlib/pull/1405 (open, not merged), in a different form: a helper `gz_room()` that also bounds `gz_look()`'s copy and `gzgets()`, and at the largest position still fetches one byte to tell the end of the input from data past it (`Z_DATA_ERROR` "position overflow" only when there is such data). This series fails at the largest position without reading. madler/zlib `develop` has no bound on the read position.

## Review Feedback Addressed

- None yet (not submitted).

## Testing

- Clang, `ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, `-O0`, AddressSanitizer + UndefinedBehaviorSanitizer, on Linux:
  - Before the fix: aborts with "runtime error: signed integer overflow: 9223372036854775807 + 1" in the test's `gzgetc()` macro.
  - After the fix: passes.
- Clang, `ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`, same sanitizers: passes.

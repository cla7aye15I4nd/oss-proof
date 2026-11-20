# Do not leave next_in pointing at the caller's buffer in gz_write()

## Problem

The direct path of `gz_write()` (`gzwrite.c`; a write of at least the buffer size, compressed or transparent) points `state->strm.next_in` at the caller's buffer. When `gz_comp(state, Z_NO_FLUSH)` failed (for example `EAGAIN` on a full non-blocking pipe), `gz_write()` returned 0 and left `next_in` there with `avail_in` nonzero, after `gzwrite()` had returned to the caller:

1. `gzclose()` (`gz_comp(state, Z_FINISH)`), `gzflush()` and `gzsetparams()` then wrote or compressed `avail_in` bytes of the caller's buffer, which the caller may have freed (AddressSanitizer: heap-use-after-free).
2. After `gzclearerr()`, a small `gzwrite()`, `gzputc()` or `gzprintf()` computed `(next_in + avail_in) - state->in`, a subtraction of pointers into two different objects (ISO C17 §6.5.6p9; AddressSanitizer: invalid-pointer-pair), and copied past the end of the input buffer (heap-buffer-overflow without the pointer-pair check).

## Fix

On failure, `gz_write()` sets `avail_in = 0` and `next_in = state->in` before returning 0; after the direct path succeeds it sets `next_in = state->in` (`avail_in` is already 0 there). On every path without a failure the stream holds what it held before, except a `next_in` that no code reads while `avail_in` is 0.

The added lines are the ones madler/zlib added to its `gz_write()` with `df84af25` (failure path) and `6be4bcda` (after the loop). Neither commit is cherry-picked:

- `df84af25` patches madler's non-blocking `gz_write()` loop from `81cc0be` (`ret = gz_comp(...)`, `n -= state->strm.avail_in` before `state->x.pos += n`, `return state->again ? put - len : 0`), which zlib-ng does not have; it does not apply to zlib-ng's `gzwrite.c`. Taking that structure would also change what `gztell()` reports after a failed direct write, beyond this defect.
- `6be4bcda` also moves `strm->next_in = NULL` out of the `!direct` branch of madler's `gz_init()` (so that its `gz_vacate()`, which zlib-ng does not have, compares only pointers into its own buffer); it does not apply to zlib-ng's `gzwrite.c` either. The `gz_write()` line of that commit is the after-loop line here.

Add `gzfile_api_errors.write_failed_direct_close` and `gzfile_api_errors.write_failed_direct_clearerr` in `test/test_gzfile_api_errors.cc`. Each fails a 100-byte direct `gzwrite()` (buffer size 8, transparent) on a full non-blocking pipe, frees the buffer, and then either drains the pipe and closes (the file must stay empty) or clears the error, writes one byte, drains and closes (the file must hold that byte only).

## Related Upstream References

- Updates open PR: https://github.com/zlib-ng/zlib-ng/pull/2527
- madler/zlib `df84af25` ("Fix buffer overflow bug in non-blocking gzwrite.", CVE-2026-85091) and `6be4bcda` ("Avoid undefined pointer comparisons in gz_vacate().") contain the same `gz_write()` lines.
- Note: https://github.com/zlib-ng/zlib-ng/pull/2517 also appends to `test/test_gzfile_api_errors.cc`.

## Review Feedback Addressed

- Commit message added, and the madler/zlib commits named in it and above.
- The standalone reproducers are replaced by GoogleTest cases in `test/test_gzfile_api_errors.cc`.
- The code comment is one line.

## Testing

- Clang, `ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, `-O0`, `-fsanitize=address,pointer-compare,pointer-subtract,undefined` on C (`address,undefined` on C++), `ASAN_OPTIONS=detect_invalid_pointer_pairs=2`:
  - Before the fix: `write_failed_direct_close` aborts with AddressSanitizer heap-use-after-free (in `write()` called by `gzclose()`); `write_failed_direct_clearerr` aborts with AddressSanitizer invalid-pointer-pair.
  - After the fix: both pass with no report.
- Clang, `ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`, AddressSanitizer + UndefinedBehaviorSanitizer: both pass.

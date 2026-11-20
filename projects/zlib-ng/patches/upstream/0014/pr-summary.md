# Discard stale caller input after a failed direct gzwrite

## Problem

On the direct write path of `gz_write()` (`len >= state->size`), `state->strm.next_in` points directly into the caller's `buf`. When `gz_comp(state, Z_NO_FLUSH)` fails (for example on `EBADF` or `EAGAIN`), `gz_write()` returns `0` while leaving `state->strm.next_in` pointing into `buf` with `avail_in > 0`:

1. Freeing `buf` and calling `gzclose()` causes `gz_comp(state, Z_FINISH)` to read the freed caller buffer (heap-use-after-free).
2. Calling `gzclearerr()` followed by a small buffered write computes `have = (unsigned)((state->strm.next_in + state->strm.avail_in) - state->in)` across distinct objects (ISO C17 §6.5.6p9), causing invalid pointer subtraction and heap-buffer-overflow.
3. In `gz_write_init()`, `strm->next_in = NULL` was only initialized inside `if (!state->direct)`.

## Commits & Fix

1. **Mark Adler** (adapted from `madler/zlib@df84af25`, `CVE-2026-85091`): in `gz_write()`, compute consumed bytes (`n -= state->strm.avail_in`) after `gz_comp(state, Z_NO_FLUSH)`, and on `ret == -1` reset `state->strm.avail_in = 0` and `state->strm.next_in = state->in` before returning `0`.
2. **Mark Adler** (adapted from `madler/zlib@6be4bcda`): initialize `strm->next_in = NULL` unconditionally in `gz_write_init()` and restore `state->strm.next_in = state->in` after the direct write loop finishes.
3. **Zheng Yu**: add `gzfile_api_errors.write_failed_direct_close` and `gzfile_api_errors.write_failed_direct_clearerr` in `test/test_gzfile_api_errors.cc`.

## Related Upstream References

- Updates open PR: https://github.com/zlib-ng/zlib-ng/pull/2527
- Note: https://github.com/zlib-ng/zlib-ng/pull/2517 also appends to `test/test_gzfile_api_errors.cc`.

## Review Feedback Addressed

- Cherry-picked/adapted `madler/zlib@df84af25` and `madler/zlib@6be4bcda` as clean commits with original author attribution and proper commit messages, followed by a separate GoogleTest commit.
- Replaced standalone C reproducer files with GoogleTest cases in `test/test_gzfile_api_errors.cc` and removed verbose file header comments.

## Testing

- Clang (`ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, ASan + UBSan + C pointer-pair, `ASAN_OPTIONS=detect_invalid_pointer_pairs=2`):
  - Before fix: `write_failed_direct_close` aborts with ASan `heap-use-after-free`; `write_failed_direct_clearerr` aborts with ASan `invalid-pointer-pair` / UBSan overflow.
  - After fix: both tests pass.
- Clang (`ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`, ASan + UBSan): both tests pass.

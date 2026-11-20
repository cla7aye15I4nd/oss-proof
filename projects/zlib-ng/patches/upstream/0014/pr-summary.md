# PR 0014: Discard stale caller input after a failed direct `gzwrite`

- **Proposed PR Title**: `Discard stale caller input after a failed direct gzwrite`
- **Target Base**: `zlib-ng/zlib-ng` `develop` (`5f1f4899`)
- **Upstream PR**: https://github.com/zlib-ng/zlib-ng/pull/2527 (open; needs updated force-push)
- **Commits**: 1 (`upstream.patch`)
- **Files**: `gzwrite.c`, `test/test_gzfile_api_errors.cc`

## Problem & Root Cause

In `gz_write()`, the direct path (`len >= state->size`) points `state->strm.next_in` directly at the caller's `buf` and sets `state->strm.avail_in = n`. When `gz_comp(state, Z_NO_FLUSH)` returns `-1` (e.g. write failure on a read-only fd or full pipe), `gz_write()` returns `0` while leaving `state->strm.next_in` pointing at `buf` with `avail_in > 0`:

1. If the caller frees `buf` and calls `gzclose()`, `gz_comp(state, Z_FINISH)` dereferences the freed caller buffer (heap-use-after-free).
2. If the caller clears the error via `gzclearerr()` and issues a small buffered write (`gzwrite` / `gzputc`), `gz_write()` computes `have = (unsigned)((state->strm.next_in + state->strm.avail_in) - state->in)` across distinct objects (ISO C17 §6.5.6p9), causing cross-object pointer subtraction and heap-buffer-overflow.
3. Also move `strm->next_in = NULL;` initialization in `gz_write_init()` before `if (!state->direct)` so direct-mode streams do not leave `next_in` indeterminate (adapted from `madler/zlib@6be4bcda`).

## Fix Summary

Adapting `madler/zlib@df84af25` and `madler/zlib@6be4bcda`:

- Initialize `strm->next_in = NULL;` unconditionally in `gz_write_init()`.
- On the direct write path of `gz_write()`, update `n -= state->strm.avail_in; state->x.pos += n; len -= n;` after `gz_comp(state, Z_NO_FLUSH)`. If `ret == -1`, reset `state->strm.avail_in = 0; state->strm.next_in = state->in;` before returning `0`. After the loop completes, restore `state->strm.next_in = state->in;`.
- Add both `gzfile_api_errors.write_failed_direct_close` (free caller buffer before `gzclose()`) and `gzfile_api_errors.write_failed_direct_clearerr` (`gzclearerr()` + follow-up small write) in `test/test_gzfile_api_errors.cc`.

## Review Feedback Addressed (`nmoinvaz` on `#2527`)

- **Proper commit message & `madler/zlib` attribution (`nmoinvaz` #1, #4)**: Added detailed commit message citing `madler/zlib@df84af25` and `madler/zlib@6be4bcda`.
- **GoogleTest conversion & remove standalone reproducer files (`nmoinvaz` #2)**: Squashed into a single clean commit with both GoogleTest tests directly in `test/test_gzfile_api_errors.cc` and no standalone C reproducer files.
- **No wordy top-of-file comments (`nmoinvaz` #3)**: Omitted all verbose file header comments.

## Overlaps & Dependencies

- **Internal (`gzwrite.c`)**: disjoint from `0017` and `0022`.
- **Internal (`test/test_gzfile_api_errors.cc`)**: `0015` also appends to `test/test_gzfile_api_errors.cc`.
- **External (`#2517`)**: https://github.com/zlib-ng/zlib-ng/pull/2517 also appends to `test/test_gzfile_api_errors.cc`.

## Verification

- `build-compat-san` (`detect_invalid_pointer_pairs=2`):
  - Before fix (`5f1f4899`): `write_failed_direct_close` crashes with ASan `heap-use-after-free`; `write_failed_direct_clearerr` fails with ASan `invalid-pointer-pair` / UBSan overflow.
  - After fix: both pass (`[  PASSED  ] 2 tests.`).
- `build-native-san` (`WITH_OPTIM=ON`): both pass (`[  PASSED  ] 2 tests.`).

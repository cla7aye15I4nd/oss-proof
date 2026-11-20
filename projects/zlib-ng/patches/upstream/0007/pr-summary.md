# PR 0007: Avoid comparing `inflate` output with a separate sliding window

- **Proposed PR Title**: `Avoid comparing inflate output with a separate sliding window`
- **Target Base**: `zlib-ng/zlib-ng` `develop` (`5f1f4899`)
- **Upstream PR**: Ready to submit
- **Commits**: 1 (`upstream.patch`)
- **Files**: `inffast_tpl.h`, `inflate.c`, `test/test_inflate_back.cc`, `test/test_inflate_far_distance.cc`

## Problem & Root Cause

When `inflate()` copies historical match bytes from its internal sliding window (`state->window`) into the caller's output buffer (`strm->next_out`), `inflate.c` (`MATCH` state) and `inffast_tpl.h` call `chunkcopy_safe()` / `CHUNKCOPY_SAFE()`. Those helpers perform relational pointer comparisons (`out - from`, `from >= safe`, etc.) to detect overlapping self-copies, which compares and subtracts pointers into two separate allocations (ISO C17 §6.5.6p9, §6.5.8p5). Under Clang `ASAN_OPTIONS=detect_invalid_pointer_pairs=2`, upstream's existing `test/test_inflate_far_distance.cc` already triggers `invalid-pointer-pair` in both `inflate.c` (`MATCH`) and `chunkset_tpl.h` (`inflate_fast`).

Meanwhile, `inflateBack()` calls `inflate_fast_safe()` (`USE_SAFE_MODE` defined) with output inside the caller-supplied window (`window == beg`), where copies *can* overlap.

## Fix Summary

- In `inflate.c` (`MATCH` state, window copy only): replace `chunkcopy_safe(put, from, copy, put + left)` with `memcpy(put, from, copy); put += copy;`.
- In `inffast_tpl.h`:
  - In the `#ifndef USE_SAFE_MODE` fast path (called exclusively by `inflate()`, never `inflateBack()`), use `memcpy()` unconditionally for all window-originated copies with no runtime `window == beg` branch.
  - In the `#ifdef USE_SAFE_MODE` path (shared with `inflateBack()`), guard window copies with `if (window == beg)` to retain `CHUNKCOPY_SAFE()` / `chunkcopy_safe()` for overlapping `inflateBack()` window copies and use `memcpy()` otherwise.
- Add `inflate.copies_matches_from_history_window` in `test/test_inflate_far_distance.cc` (chunk sizes 1 and 300) and `inflate_back.wrapping_window_overlap` in `test/test_inflate_back.cc` (hand-encoded RFC 1951 fixed-Huffman streams across `windowBits = 8, 9, 15` with wrapping and overlapping matches).

## Review Feedback / Draft Cleanup

- Relocated tests out of `test/test_inflate_copy.cc` into `test/test_inflate_far_distance.cc` and `test/test_inflate_back.cc` to eliminate merge conflicts with `0003` and `0011`.
- Dropped the unnecessary `if (window == beg)` branch under `#ifndef USE_SAFE_MODE` (`infback.c` only calls `inflate_fast_safe`).
- Replaced `deflateInit2(..., -wb, ...)` with a hand-encoded fixed-Huffman encoder in `wrapping_window_overlap` so `windowBits = 8` (`256`-byte window) and `dist == wsize` are exercised directly without `deflateInit2` window restrictions.

## Overlaps & Dependencies

- **Internal (`inflate.c`)**: disjoint from `0003`, `0008`, and `0011`.
- **External (`#2432`)**: https://github.com/zlib-ng/zlib-ng/pull/2432 modifies the non-safe loop in `inffast_tpl.h`; coordinate rebase if `#2432` lands first.

## Verification

- `build-compat-san` (`detect_invalid_pointer_pairs=2`):
  - Before fix (`5f1f4899`): fails (`invalid-pointer-pair` in `inflate_far_distance.*` and `copies_matches_from_history_window`).
  - After fix: all 13 tests pass (`inflate_far_distance.*`, `inflate.copies_matches_from_history_window`, and all `inflate_back.*` including `wrapping_window_overlap`).
- `build-native-san` (`WITH_OPTIM=ON`): all 13 tests pass (`[  PASSED  ] 13 tests.`).

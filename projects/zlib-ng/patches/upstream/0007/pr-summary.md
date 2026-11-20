# Avoid comparing inflate output with a separate sliding window

## Problem

When `inflate()` copies match bytes from its internal sliding window (`state->window`) into the caller's output buffer (`strm->next_out`), `inflate.c` (`MATCH` state) and `inffast_tpl.h` invoke `chunkcopy_safe()` / `CHUNKCOPY_SAFE()`. Those helpers compare and subtract their source and destination pointers to detect self-overlapping copies, which invokes relational pointer comparisons and subtraction across two distinct allocations (ISO C17 §6.5.6p9, §6.5.8p5). Under Clang with `-fsanitize=address,pointer-compare,pointer-subtract` and `ASAN_OPTIONS=detect_invalid_pointer_pairs=2`, `test/test_inflate_far_distance.cc` already fails with `invalid-pointer-pair` in both `inflate.c` and `chunkset_tpl.h`.

Meanwhile, `inflateBack()` calls `inflate_fast_safe()` (`USE_SAFE_MODE` defined) with output inside the caller-supplied window (`window == beg`), where copies inside the window can legitimately overlap.

## Fix

- In `inflate.c` (`MATCH` state, sliding-window copy): replace `chunkcopy_safe(put, from, copy, put + left)` with `memcpy(put, from, copy); put += copy;`.
- In `inffast_tpl.h`:
  - In the `#ifndef USE_SAFE_MODE` path (used only by `inflate()`, never `inflateBack()`), copy window-originated bytes with `memcpy()` unconditionally with no runtime branch.
  - In the `#ifdef USE_SAFE_MODE` path (shared with `inflateBack()`), retain `CHUNKCOPY_SAFE()` / `chunkcopy_safe()` when `window == beg` so overlapping `inflateBack()` copies stay overlap-safe, and use `memcpy()` when `window != beg`.
- Add `inflate.copies_matches_from_history_window` in `test/test_inflate_far_distance.cc` (chunk sizes `1` and `300`) and `inflate_back.wrapping_window_overlap` in `test/test_inflate_back.cc` (hand-encoded RFC 1951 fixed-Huffman streams covering `windowBits = 8, 9, 15` with wrapping and full-window matches).

## Related Upstream References

- Note: https://github.com/zlib-ng/zlib-ng/pull/2432 also modifies the non-safe loop in `inffast_tpl.h`.

## Testing

- Clang (`ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, `-fsanitize=address,pointer-compare,pointer-subtract,undefined` on C, `ASAN_OPTIONS=detect_invalid_pointer_pairs=2`):
  - Before fix: `inflate/inflate_far_distance.*` and `inflate.copies_matches_from_history_window` abort with `AddressSanitizer: invalid-pointer-pair`.
  - After fix: all 13 tests across `inflate/inflate_far_distance.*`, `inflate.copies_matches_from_history_window`, and `inflate_back.*` pass.
- Clang (`ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`, ASan + UBSan): all 13 tests pass.

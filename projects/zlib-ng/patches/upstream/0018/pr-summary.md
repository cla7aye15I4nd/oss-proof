# PR 0018: Keep open fixed-block start representable during window slides

- **Proposed PR Title**: `Keep open fixed-block start representable during window slides`
- **Target Base**: `zlib-ng/zlib-ng` `develop` (`5f1f4899`)
- **Upstream PR**: Ready to submit
- **Commits**: 1 (`upstream.patch`)
- **Files**: `deflate.c`, `test/test_deflate_cve.cc`

## Problem & Root Cause

At level 1 with `Z_FIXED`, `deflate_quick()` keeps one static block open across window slides without flushing. Every slide in `fill_window()` executes:

```c
s->block_start -= (int)slide_len;
```

Once more than 2 GiB of input passes in one stream without a flush, `s->block_start` underflows `INT_MIN` (signed integer overflow, ISO C17 §6.5p5). Meanwhile, any exit path from `deflate_quick()` (`Z_FINISH`, flush, or `deflateParams`) closes the block and resets `block_start = strstart` before `(int)strstart - block_start` is used.

## Fix Summary

Clamp the subtraction in `fill_window()` (`deflate.c`) so `block_start` never goes below `-(2^30 + 2^16)`:

```c
if (s->block_start >= (int)slide_len - (1 << 30) - (1 << 16))
    s->block_start -= (int)slide_len;
```

So `(int)strstart - block_start` also stays safely within signed 32-bit range (`strstart <= 65536`). Add an opt-in regression test `deflate_quick.fixed_block_across_large_input` (`ZLIB_NG_TEST_LARGE_FIXED_BLOCK=1`) in `test/test_deflate_cve.cc` feeding 2,151,677,952 bytes (> 2 GiB).

## Draft Cleanup

- Moved `deflate_quick.fixed_block_across_large_input` out of `test/test_deflate_quick_block_open.cc` into `test/test_deflate_cve.cc` to avoid colliding with `deflate-reset-block-open`.

## Overlaps & Dependencies

- Independent (`deflate.c` `fill_window()` and `test/test_deflate_cve.cc` do not collide with any other series).

## Verification

- Normal CI (without `ZLIB_NG_TEST_LARGE_FIXED_BLOCK`): skips cleanly (`GTEST_SKIP()`).
- With `ZLIB_NG_TEST_LARGE_FIXED_BLOCK=1`:
  - Before fix (`5f1f4899`): fails under UBSan in `fill_window()` (`signed integer overflow`).
  - After fix: passes on both `build-compat-san` and `build-native-san` (`[  PASSED  ] 1 test.`), and passes inside the combined stack.

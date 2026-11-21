# Keep open fixed-block start representable during window slides

## Problem

At compression level 1 with strategy `Z_FIXED`, `deflate_quick()` opens a single static Huffman block and keeps it open across window slides without flushing. Each slide in `fill_window()` (`deflate.c`) executes:

```c
s->block_start -= (int)slide_len;
```

After more than 2 GiB of input in one stream without a flush, `s->block_start` underflows `INT_MIN` (signed 32-bit integer overflow, ISO C17 §6.5p5). Every exit from the static `deflate_quick()` path (`Z_FINISH`, a flush, or `deflateParams()`) closes the block and resets `block_start = strstart` before `(int)strstart - block_start` is used.

## Fix

Clamp the subtraction in `fill_window()` (`deflate.c`) so `s->block_start` never drops below `-(2^30 + 2^16)`:

```c
if (s->block_start >= (int)slide_len - (1 << 30) - (1 << 16))
    s->block_start -= (int)slide_len;
```

This prevents signed overflow in both `s->block_start -= (int)slide_len` and `(int)strstart - s->block_start` (`strstart <= 65536`), with no change to compressed output on streams that do not exceed `2^30` bytes in one open block.

Add an opt-in regression test `deflate_quick.fixed_block_across_large_input` in `test/test_deflate_cve.cc` gated by `ZLIB_NG_TEST_LARGE_FIXED_BLOCK` (feeds `2,151,677,952` bytes at level 1 / `Z_FIXED`).

## Related Upstream References

- Not yet submitted upstream.

## Review Feedback Addressed

- None yet (not submitted).

## Testing

- Under default test runs (without `ZLIB_NG_TEST_LARGE_FIXED_BLOCK`), the test skips via `GTEST_SKIP()`.
- With `ZLIB_NG_TEST_LARGE_FIXED_BLOCK=1`, with `tests/patch-gtest.sh` (clang, `ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, AddressSanitizer + UndefinedBehaviorSanitizer):
  - Without the fix: aborts under UndefinedBehaviorSanitizer in `fill_window()` (`signed integer overflow: -2147483648 - 32768`).
  - With the fix: passes.
- Reproduction in the project's regression suite: `fixed-block-start-overflow`.

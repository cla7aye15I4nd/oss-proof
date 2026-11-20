# Keep block_start bounded and check block_open in deflateParams()

## Problem

At compression level 1 with strategy `Z_FIXED`, `deflate_quick()` emits symbols directly into the bit buffer and keeps a single static Huffman block open (`s->block_open != 0`) across window slides without flushing. Each slide in `fill_window()` (`deflate.c`) executes:

```c
s->block_start -= (int)slide_len;
```

This causes two failures on long `Z_NO_FLUSH` streams:

1. **Signed integer overflow past 2 GiB (UBSan)**: `s->block_start -= (int)slide_len` underflows `INT_MIN` (`-2147483648 - 32768`, ISO C17 §6.5p5).
2. **Mid-block `deflateParams()` level switch past 4 GiB (without sanitizers)**: after 4096 MiB (`2^32` bytes), `s->block_start` wraps back to `+32768`. Calling `deflateParams()` with `avail_out == 0` evaluates `((int)s->strstart - s->block_start) + s->lookahead` to `(32753 - 32768) + 15 == 0`, so `deflateParams()` returns `Z_OK` and switches compression levels while `deflate_quick()`'s static block is still open (`block_open == 1`, no end-of-block symbol emitted), corrupting the stream.

## Fix

- In `deflate_quick.c` (right after `PREFIX(fill_window)(s);`):
  ```c
  if (static_emit)
      s->block_start = (int)strstart;
  ```
  In the `static_emit` (`Z_FIXED`) path, `s->block_start` is not used for stored-block fallback, so resyncing it after `fill_window()` keeps it bounded without touching `fill_window()` and adds zero overhead to non-`Z_FIXED` paths (`static_emit` is a compile-time constant).
- In `deflateParams()` (`deflate.c`):
  ```c
  if (strm->avail_in || s->block_open || ((int)s->strstart - s->block_start) + s->lookahead || !DEFLATE_DONE(strm, flush))
  ```
  Explicitly checking `s->block_open` guarantees that `deflateParams()` never switches levels while a static block is still open.
- Add an always-on regression test `deflate_quick.fixed_block_across_large_input` in `test/test_deflate_cve.cc` (guarded by `#ifndef TEST_STOCK_ZLIB`). Feeding 4 GiB of all-zero data from a 1 MiB static buffer takes ~0.5s at `-O2` and verifies both no UBSan overflow and that `deflateParams()` with `avail_out == 0` returns `Z_BUF_ERROR`.

## Related Upstream References

- Upstream zlib-ng PR: [#2533](https://github.com/zlib-ng/zlib-ng/pull/2533) (open).

## Review Feedback Addressed

- Replaced the earlier `fill_window()` clamp with the 3-line fix in `deflate_quick.c` and `deflate.c`, and replaced the opt-in `GTEST_SKIP()` test with an always-on 4 GiB all-zero test.

## Testing

- Built with Clang (`-O2`, with and without `-fsanitize=undefined`):
  - Without the fix: under UBSan, aborts at 2 GiB in `fill_window()` (`signed integer overflow: -2147483648 - 32768`); without sanitizers, fails at 4 GiB because `deflateParams()` with `avail_out == 0` returns `Z_OK` instead of `Z_BUF_ERROR` (`level=6, block_open=1`).
  - With the fix: passes in ~0.5s under `-O2` with UBSan (`deflateParams()` returns `Z_BUF_ERROR` and `deflate(Z_FINISH)` returns `Z_STREAM_END`).
- Reproduction in the project's regression suite: `fixed-block-start-overflow`.

# Reset block_open in deflateResetKeep()

## Problem

At level 1 with strategy `Z_FIXED`, `deflate_quick()` writes symbols straight into the bit buffer with the static
trees and keeps its block open (`s->block_open` is 1, or 2 for the last block) across `Z_NO_FLUSH` calls, until a
flush or `Z_FINISH` ends it. `block_open` is cleared only by `deflateInit2()`. `deflateResetKeep()`, which
`deflateReset()` calls, resets the pending output, the bit buffer (`zng_tr_init()`) and `last_flush`, but not
`block_open`. After `deflateReset()` in the middle of such a block, the first `deflate_quick()` call of the next
stream therefore writes no block header: its symbols follow the new zlib or gzip header directly. `deflate()`
returns `Z_STREAM_END`, and `inflate()` rejects the output with `Z_DATA_ERROR`.

Reached through documented calls only: `deflateInit2(level 1, Z_FIXED)`, `deflate(Z_NO_FLUSH)` with input,
`deflateReset()`, `deflate(Z_FINISH)`. The same happens with a gzip or raw wrapper, with `deflatePrime()` or
`deflateSetDictionary()` between the reset and the next `deflate()`, after `deflateCopy()` of the open stream and a
reset of the copy, and when the reset stream is switched to another level with `deflateParams()` (no flush is done
right after a reset) and back to level 1 with `Z_FIXED` later. No memory error: the output is wrong, not unsafe.

`block_open` is the only state of `deflate_quick()` that survives a reset: `strstart`, `block_start` and the
lookahead are reset by `lm_init()`, the bit buffer and the symbol buffer by `zng_tr_init()`. A stream that ended
with `Z_STREAM_END` has `block_open == 0`, so a reset after a completed stream was not affected.

## Fix

Files: `deflate.c`, `test/test_deflate_quick_block_open.cc`.

```c
s->block_open = 0;
```

in `deflateResetKeep()`, next to the other per-stream state it resets. One commit with the test
`deflate_quick.reset_clears_block_open`: it compresses 3000 bytes with `Z_NO_FLUSH` at level 1 with `Z_FIXED`, calls
`deflateReset()`, compresses 1000 bytes with `Z_FINISH`, and checks that `inflate()` returns `Z_STREAM_END` with the
1000 bytes.

## Related Upstream References

- No zlib-ng issue or pull request addresses it. `block_open` exists only in zlib-ng.
- madler/zlib commit 1e4178b ("Fix deflateResetKeep() when used in the middle of a stream") fixes a different
  defect of the same function (the window positions kept by `deflateResetKeep()` alone); it does not touch this field.

## Review Feedback Addressed

- Not yet submitted upstream.

## Testing

- `deflate_quick.reset_clears_block_open` built with upstream's CMake under AddressSanitizer and
  UndefinedBehaviorSanitizer: it fails without the `deflate.c` change (`inflate()` returns `Z_DATA_ERROR`) and passes
  with it.
- On the build host, the verified source with and without the change, with `inflate()` of every output: without it
  the reset cases above (zlib, gzip and raw wrappers, `deflatePrime()`, `deflateSetDictionary()`, `deflateCopy()`
  then reset, reset then `deflateParams()` to level 6 and back to level 1 with `Z_FIXED`) all give a stream that
  `inflate()` rejects; with it every case round-trips. A reset after `Z_STREAM_END`, and finishing an open block (also
  in a copy), round-trip with and without it.

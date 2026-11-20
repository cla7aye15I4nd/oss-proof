# Reset block_open in deflateResetKeep()

## Problem

At compression level 1 with strategy `Z_FIXED`, `deflate_quick()` sets `s->block_open = 1` and keeps the static Huffman block open across `Z_NO_FLUSH` calls until a flush or `Z_FINISH`. `s->block_open` is initialized in `deflateInit2()`, but `deflateResetKeep()` (called by `deflateReset()`) never resets `s->block_open` back to `0`.

Consequently, after calling `deflateReset()` on an open fixed block, the next stream writes symbols immediately after the new zlib/gzip header without opening a deflate block header, producing an invalid stream that `inflate()` rejects with `Z_DATA_ERROR`.

## Fix

Clear `s->block_open = 0;` inside `deflateResetKeep()` (`deflate.c`).

Add `deflate_quick.reset_clears_block_open` in `test/test_deflate_quick_block_open.cc` (feeds 3,000 bytes with `Z_NO_FLUSH` at level 1 / `Z_FIXED`, calls `deflateReset()`, compresses 1,000 bytes with `Z_FINISH`, and verifies `inflate()` recovers the exact 1,000-byte payload).

## Testing

- Clang (`ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, ASan + UBSan) and Clang (`ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`, ASan + UBSan):
  - Before fix: `deflate_quick.reset_clears_block_open` fails (`inflate()` returns `Z_DATA_ERROR` instead of `Z_STREAM_END`).
  - After fix: passes in both builds.

# PR (deflate-reset-block-open): Reset `block_open` in `deflateResetKeep()`

- **Proposed PR Title**: `Reset block_open in deflateResetKeep()`
- **Target Base**: `zlib-ng/zlib-ng` `develop` (`5f1f4899`)
- **Upstream PR**: Ready to submit (Finding 18 in [../../docs/en/findings.md](../../docs/en/findings.md); not yet assigned a numbered local proof patch)
- **Commits**: 1 (`upstream.patch`)
- **Files**: `deflate.c`, `test/test_deflate_quick_block_open.cc`

## Problem & Root Cause

With compression level 1 and strategy `Z_FIXED`, `deflate_quick()` opens a static Huffman block (`s->block_open = 1`) and keeps it open across `Z_NO_FLUSH` calls until a flush or `Z_FINISH`. `s->block_open` is initialized in `deflateInit2()`, but `deflateResetKeep()` (called by `deflateReset()`) never resets `s->block_open` to `0`.

As a result, after calling `deflateReset()` on such a stream, the next `deflate()` emits raw symbols immediately after the fresh zlib/gzip header without opening a deflate block header, producing corrupt compressed data rejected by `inflate()` (`Z_DATA_ERROR`: `"invalid stored block lengths"`).

## Fix Summary

Reset `s->block_open = 0;` alongside `s->last_flush = -2;` inside `deflateResetKeep()` (`deflate.c`).

Add `deflate_quick.reset_clears_block_open` in `test/test_deflate_quick_block_open.cc` (feeds 3,000 bytes with `Z_NO_FLUSH` at level 1 / `Z_FIXED`, calls `deflateReset()`, compresses 1,000 bytes with `Z_FINISH`, and verifies `inflate()` recovers the exact 1,000-byte payload).

## Overlaps & Dependencies

- Independent (`deflate.c` `deflateResetKeep()` and `test/test_deflate_quick_block_open.cc` are untouched by all other series; `0018`'s test was moved out of this test file to avoid colliding here).

## Verification

- `build-compat-san` & `build-native-san`:
  - Before fix (`5f1f4899`): `deflate_quick.reset_clears_block_open` fails (`inflate()` returns `Z_DATA_ERROR` instead of `Z_STREAM_END`).
  - After fix: passes on both builds (`[  PASSED  ] 1 test.`).

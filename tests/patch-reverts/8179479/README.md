# 8179479: a one-byte window after `inflateSync` with `windowBits` 0

- **Fix:** upstream commit `8179479c6274c0041189882b8746a33e2376eaf0`, "Use the maximum window size after
  inflateSync() if not yet known" (Trail of Bits, TOB-ZLIB-004), in zlib 1.4.
- **Revert** (`revert.patch`, `lean.patch`): the eight lines the commit added to `inflateSync` go
  (when `wbits` is 0: free the window and set `wbits` to 15). The later commit `40e399f` moved
  neighbouring lines, so the commit does not reverse-apply as it is, but no later commit depends on
  these lines: the revert is exactly the removal of what `8179479` added, and `40e399f` stays.
- **Calls** (`trigger.c`, `model.lean`): `inflateInit2(0)` (window size from the header);
  `inflateSync` on `00 00 ff ff` followed by a raw fixed-code block, before any header; `inflate`
  of that block, which allocates a window of `1 << 0` bytes; `inflateReset`, which keeps it
  (`wbits` equals the requested 0); `inflate` of a zlib stream of 135 bytes without its four check
  bytes, whose header sets `wbits` to 15; `inflate` of the check bytes; `inflateEnd`.
- **C:** with the revert, ASan reports a heap-buffer-overflow write of 135 bytes into the one-byte
  window in `updatewindow`. Without it, no report, and both streams decode.
- **Model:** with the revert, `Fault.ub` "memcpy outside its objects". Without it, the line
  `trigger.c` prints.
- **Domain:** inside the safety goal of `inflate`: the stream is reached by `inflateInit2` with
  `windowBits` 0 (which `zlib.h` allows), `inflateSync`, `inflate` and `inflateReset`, all stream
  operations of `StreamReachable`, with valid buffers. Checked by reading the premises.

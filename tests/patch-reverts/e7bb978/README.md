# e7bb978: a primed inflate stream on the fast path

- **Fix:** upstream commit `e7bb9788e0f0e9252de04fc52c3ada4ddede2f7d`, "Keep primed inflate streams
  off of the fast path" (Trail of Bits, TOB-ZLIB-014), in zlib 1.4.
- **Revert** (`revert.patch`, `lean.patch`): in `case LEN`, `inflate` calls `inflate_fast` when
  `have >= 6 && left >= 258`, without `bits < 8`.
- **Calls** (`trigger.c`, `model.lean`): `inflateInit2(-15)`; two `inflatePrime(16, ...)` calls with the
  first four bytes of a raw stream of two fixed-code blocks ("a", then "bcdefghijklmnop", final);
  `inflate` with the other 15 bytes, in a buffer of exactly that size, and 1000 bytes of room. The
  first block lies entirely in the primed bits. `inflate_fast` decodes it without reading input and
  then gives back the whole bytes it still holds, which moves `next_in` before the input buffer.
- **C:** with the revert, ASan reports a heap-buffer-overflow read in `inflate_fast`, one byte before
  the input buffer, when the second block takes the fast path. Without it, no report, and the
  stream decodes to its 16 bytes.
- **Model:** with the revert, `Fault.ub` "pointer arithmetic outside its object". Without it, the line
  `trigger.c` prints.
- **Domain:** inside the safety goal of `inflate`: the stream is reached by `inflateInit2` and
  `inflatePrime` (a stream operation of `StreamReachable`), and `inflate` gets valid buffers
  (`StreamBuffers`). Checked by reading the premises.

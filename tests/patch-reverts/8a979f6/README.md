# 8a979f6: the flush rank shifts a negative value

- **Fix:** upstream commit `8a979f6c7986574e37316148cd8ca440c3bc08a3`, "Avoid left shift of a negative
  value in flush rank calculation", in zlib 1.2.8.1.
- **Revert** (`revert.patch`, `lean.patch`): `RANK(f)` is `((f) << 1) - ((f) > 4 ? 9 : 0)` again.
- **Calls** (`trigger.c`, `model.lean`): `deflateInit(-1)`; `deflate(Z_NO_FLUSH)` with no input and
  nothing pending, which compares `RANK(Z_NO_FLUSH)` with `RANK(last_flush)`, and `last_flush` starts
  at -2; `deflate(Z_FINISH)` of "hello"; `deflateEnd`. When the fix was made `last_flush` started at
  `Z_NO_FLUSH`; it starts at -2 since a later change, which makes the first call reach the shift.
- **C:** with the revert, UBSan reports "left shift of negative value -2" in `deflate`. Without it, no
  report, and the stream ends with 13 bytes.
- **Model:** with the revert, `Fault.ub` "invalid shift of an int". Without it, the line `trigger.c`
  prints.
- **Domain:** inside the safety goal of `deflate`: the stream is reached by `deflateInit`, and
  `deflate` gets valid buffers (`next_in` NULL with `avail_in` 0). Checked by reading the
  premises.

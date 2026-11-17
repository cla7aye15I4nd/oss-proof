# 4346a16: `deflatePrime` with a negative number of bits

- **Fix:** upstream commit `4346a16853e19b45787ce933666026903fb8f3f8`, "Assure that the number of bits
  for deflatePrime() is valid", in zlib 1.2.11.1.
- **Revert** (`revert.patch`, `lean.patch`): `deflatePrime` no longer returns `Z_BUF_ERROR` for `bits`
  outside 0..16. The later commit `12d7b90` rewrote the line into a statement of its own, so the
  revert is the removal of that statement; the room check of `12d7b90` stays.
- **Calls** (`trigger.c`, `model.lean`): `deflateInit`; `deflatePrime(1, 1)`; `deflatePrime(-1, 0)`, which
  passes the room check (`need` is 0) and makes `put` -1 in the loop; `deflateEnd`.
- **C:** with the revert, UBSan reports "shift exponent -1 is negative" in `deflatePrime`
  (`1 << put`). Without it, no report, and the second call returns `Z_BUF_ERROR`.
- **Model:** with the revert, `Fault.ub` "invalid shift of an int". Without it, the line `trigger.c`
  prints.
- **Domain:** inside `Goal.deflatePrime_safety`: the stream has not started (`DeflateNotStarted`), and
  `deflatePrime` takes any `bits` and `value`. Checked by reading the premises.

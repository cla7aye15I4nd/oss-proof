# a9e14e8: `windowBits` `INT_MIN` overflows on negation

- **Fix:** upstream commit `a9e14e85415eb326000f352bce3fcb04a125406d`, "Avoid undefined negation
  behavior if windowBits is INT_MIN", in zlib 1.2.13.
- **Revert** (`revert.patch`, `lean.patch`): `inflateReset2` and `deflateInit2_` no longer return
  `Z_STREAM_ERROR` for a `windowBits` below -15 before they negate it.
- **Calls** (`trigger.c`, `model.lean`): `inflateInit2(INT_MIN)` (which calls `inflateReset2`); then,
  in a separate process (a separate run in the model), `deflateInit2` with `windowBits` `INT_MIN`.
- **C:** with the revert, UBSan reports "negation of -2147483648" in `inflateReset2` and in
  `deflateInit2_`. Without it, no report, and both calls return `Z_STREAM_ERROR`.
- **Model:** with the revert, `Fault.ub` "signed integer overflow" (`inflate.c`) and "signed int
  overflow" (`deflate.c`). Without it, the lines `trigger.c` prints.
- **Domain:** inside `Goal.inflateInit2__safety` and `Goal.deflateInit2__safety`, which hold for every
  `windowBits`. Checked by reading the premises.

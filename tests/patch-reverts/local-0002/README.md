# local-0002: `gzseek` after `gzungetc` overflows the position

- **Fix:** patch 0002 (`patches/0002-gzseek-negative-position-overflow.patch`), the `gzlib.c` part of
  upstream PR 1361.
- **Revert** (`revert.patch`, `lean.patch`): `gzseek64` evaluates `offset > GZ_OFF_MAX - pos` for every
  `pos` again, and no longer refuses a displacement from a negative position that does not fit.
- **Calls** (`trigger.c`, `model.lean`): `gzopen` of a three-byte transparent file for reading;
  `gzungetc('Q')`, which sets the position to -1; `gzseek(f, 1, SEEK_CUR)`; `gzclose`.
- **C:** with the revert, UBSan reports a signed integer overflow in `gzseek64` (`GZ_OFF_MAX - pos`
  with `pos` = -1). Without it, no report, and the seek returns 0.
- **Model:** with the revert, `Fault.ub` "signed overflow (long)". Without it, the line `trigger.c`
  prints.
- **Domain:** inside `Goal.gzseek_safety` (`GzCallSafety`): the handle has a history (`gzopen`, then
  `gzungetc`), and `gzseek` takes any offset and whence. Checked by reading the premises.

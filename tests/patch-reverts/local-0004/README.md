# local-0004: the gz position overflows at `INT64_MAX`

- **Fix:** patch 0004 (`patches/0004-gz-position-overflow.patch`), local, not submitted upstream.
- **Revert** (`revert.patch`, `lean.patch`): the whole patch. `gz_room` goes, and with it the bounds
  of `gz_look`, `gz_fetch`, `gz_read` and `gzgets`; `gz_write`, the fast path of `gzputc` and
  `gzvprintf` no longer refuse a write past `GZ_OFF_MAX`.
- **Calls** (`trigger.c`, `model.lean`): `open("/dev/zero")`, `gzdopen(fd, "r")`; `gzread` of one byte
  (a transparent copy); `gzseek(f, INT64_MAX, SEEK_SET)`; `gzread` of 16 bytes; `gzclose`. On Linux
  `lseek` on `/dev/zero` returns 0 without moving, so the seek succeeds; in the model the `lseek`
  oracle of the file model does the same, and `/dev/zero` is a file of zeros.
- **C:** with the revert, UBSan reports a signed integer overflow in `gz_read` (`state->x.pos += n`).
  Without it, no report; the second `gzread` returns -1 with `Z_DATA_ERROR` "position overflow".
  Linux only.
- **Model:** with the revert, `Fault.ub` "signed overflow (long)". Without it, the line `trigger.c`
  prints.
- **Domain:** inside `Goal.gzread_safety` (`GzCallSafety`): the handle has a history (`gzdopen`,
  `gzread`, `gzseek`), and the goal holds for every world of the file model, including one whose
  `lseek` returns without moving. Checked by reading the premises.

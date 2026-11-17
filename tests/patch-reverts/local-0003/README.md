# local-0003: a transparent read that fails half way leaves a stale `x.next`

- **Fix:** patch 0003 (`patches/0003-gzread-partial-copy-read-error.patch`), the change of upstream
  PR 1363.
- **Revert** (`revert.patch`, `lean.patch`): in the `COPY` case of `gz_fetch`,
  `state->x.next = state->out` follows the `gz_load` call again, so a failing `gz_load` returns
  before it. Patch 0004 rewrote the same lines, so the revert is made against the source with all
  patches.
- **Calls** (`trigger.c`, `model.lean`): `gzopen` of a 128-byte transparent file for reading;
  `gzbuffer(f, 16)`; 48 calls of the function `gzgetc`; then `read()` returns one byte and fails with
  `EIO` (in C a replaced `read()`, in the model the read oracle of the file model); `gzread` of one
  byte; `gzclose`.
- **C:** with the revert, ASan reports a heap-buffer-overflow read in `gz_read` (one byte past the
  output buffer). Without it, no report; `gzread` returns 1 and keeps `Z_ERRNO`.
- **Model:** with the revert, `Fault.ub` "memcpy outside its objects". Without it, the line
  `trigger.c` prints.
- **Domain:** inside `Goal.gzread_safety` (`GzCallSafety`): the handle has a history (`gzopen`,
  `gzbuffer`, `gzgetc`), the buffer holds the requested byte, and the goal holds for every world of
  the file model, including one whose `read` fails after a short read. Checked by reading the
  premises.

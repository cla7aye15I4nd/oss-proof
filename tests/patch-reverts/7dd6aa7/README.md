# 7dd6aa7: `gzungetc` right after `gzopen` stores through an unset pointer

- **Fix:** upstream commit `7dd6aa72455ef1f2aacdc28a00d1eaf632d59593`, "Fix bug when gzungetc() is used
  immediately after gzopen()", in zlib 1.3.
- **Revert** (`revert.patch`, `lean.patch`): `gzungetc` no longer calls `gz_look` when nothing is
  buffered yet. A later commit (`9d314c3`) rewrote the neighbouring lines, so the commit does not
  reverse-apply as it is; the revert is the removal of that call.
- **Calls** (`trigger.c`, `model.lean`): `gzopen` of a three-byte transparent file for reading;
  `gzungetc('x')`; `gzgetc`; `gzread` of up to seven bytes; `gzclose`.
- **C:** with the revert, the buffers are not allocated yet (`size` is 0, `state->out` was never
  written), and `gzungetc` stores the byte at `state->out + (state->size << 1) - 1`. ASan reports a
  SEGV at that store in `gzungetc`. Without it, no report; the byte comes back, then "abc".
- **Model:** with the revert, `Fault.ub` "arithmetic on a null pointer" (a pointer field of fresh
  memory is `NULL` in the model). Without it, the line `trigger.c` prints.
- **Domain:** inside `Goal.gzungetc_safety` (`GzCallSafety`): the handle has a history (`gzopen`), and
  `gzungetc` takes any character. Checked by reading the premises.

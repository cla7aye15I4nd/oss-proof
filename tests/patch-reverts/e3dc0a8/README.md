# e3dc0a8: `gzprintf` as the first write does arithmetic on a null `next_in`

- **Fix:** upstream commit `e3dc0a85b7032e98380dec011bc8f2c2ee0d8fca`, "Avoid undefined behavior in
  gzwrite.c", in zlib 1.4.
- **Revert** (`revert.patch`, `lean.patch`): `gz_vacate` no longer returns at once when `next_in` is
  NULL; it computes `strm->next_in + strm->avail_in` and compares it with
  `state->in + state->size`.
- **Calls** (`trigger.c`, `model.lean`): `gzopen("out.gz", "w")`; `gzprintf(f, "hello")`, the first
  write, whose `gz_init` sets `next_in` to NULL before `gz_vacate`; `gzclose`; then `gzopen` for
  reading, `gzread` and `gzclose` to check the file. In the model `vsnprintf` is an oracle of the
  file model; it is given the output glibc gives, "hello".
- **C:** with the revert, ASan reports `invalid-pointer-pair` (NULL and the input buffer) in
  `gz_vacate` (GCC, pointer-pair check). UBSan does not report the null pointer plus a zero offset
  here, with GCC or clang. Without it, no report, and the file holds "hello".
- **Model:** with the revert, `Fault.ub` "comparison of null pointers". (`NULL + 0` itself is allowed
  in the model by decision.) Without it, the line `trigger.c` prints.
- **Domain:** inside `Goal.gzprintf_safety` (`GzCallSafety`): the handle has a history (`gzopen` for
  writing), and the format is a NUL-terminated string with no conversions. Checked by reading the
  premises.

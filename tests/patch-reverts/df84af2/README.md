# df84af2: a stalled large `gzwrite` leaves `next_in` in the caller's buffer

- **Fix:** upstream commit `df84af25dc1942490e1d1c899a07619152a46148`, "Fix buffer overflow bug in
  non-blocking gzwrite" (CVE-2026-85091), in zlib 1.4.
- **Revert** (`revert.patch`, `lean.patch`): when `gz_comp` fails in the direct path of `gz_write`,
  the function returns without setting `avail_in` to 0 and `next_in` to `state->in`.
- **Calls** (`trigger.c`, `model.lean`): `gzopen("out.dat", "wT")`; `gzbuffer(f, 64)`; `gzwrite` of a
  100-byte heap buffer, during which `write()` fails once with `EAGAIN` (in C a replaced `write()`,
  in the model the write oracle of the file model); `gzwrite` of one byte; `gzclose`; `free` of the
  100-byte buffer.
- **C:** with the revert, the small `gzwrite` takes `next_in + avail_in - in`, a difference of
  pointers into different objects, as its copy position, and adds its byte to `avail_in`.
  On x86_64 Linux ASan then reports a heap-buffer-overflow read one byte past the caller's buffer,
  when `gzclose` writes the 101 bytes from `next_in`. On arm64 macOS the copy itself lands on an
  unmapped address. Without the revert, no report; the file holds the one byte.
- **Model:** with the revert, `Fault.ub` "difference of pointers into different objects", at the
  copy position. Without it, the line `trigger.c` prints.
- **Domain:** inside `Goal.gzwrite_safety` (`GzCallSafety`): the handle has a history (`gzopen`,
  `gzbuffer`, `gzwrite`), the buffers hold the bytes written, and the goal holds for every world of
  the file model, including one whose `write` fails with `EAGAIN`. Checked by reading the premises.

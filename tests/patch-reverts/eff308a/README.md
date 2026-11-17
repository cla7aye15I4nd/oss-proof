# eff308a with 1eb7682: a gzip extra field longer than the caller's buffer

- **Fix:** upstream commit `eff308af425b67093bab25f80f1ae950166bece1`, "Fix a bug when getting a gzip
  header extra field with inflate()", with its follow-up `1eb7682f845ac9e9bf9ae35bbfb3bad5dacbd91d`,
  "Fix extra field processing bug that dereferences NULL state->head", both in zlib 1.2.13; the
  fix of CVE-2022-37434. The case is the pair: `1eb7682` repairs a NULL dereference that `eff308a`
  introduced, so reverting `eff308a` alone does not apply, and reverting `1eb7682` alone gives that
  other defect. Reverting both gives the code before the fix.
- **Revert** (`revert.patch`, `lean.patch`): in `case EXTRA`, `inflate` copies into the caller's extra
  buffer at `len = extra_len - length` without checking `len < extra_max` first; the copy length
  `extra_max - len` then wraps.
- **Calls** (`trigger.c`, `model.lean`): `inflateInit2(31)`; `inflateGetHeader` with an extra buffer of
  10 bytes (`extra_max` 10); `inflate` of the first 42 bytes of a gzip stream whose extra field has
  100 bytes (the header and 30 bytes of the field); `inflate` of the rest; `inflateEnd`.
- **C:** with the revert, the second call copies with `len` 30 and a length of about 2^32; ASan
  reports a global-buffer-overflow of the copy (it checks the source range first). Without it, no
  report; the extra buffer holds the first 10 bytes of the field and the stream decodes.
- **Model:** with the revert, `Fault.ub` "pointer arithmetic outside its object" (`extra + 30`).
  Without it, the line `trigger.c` prints.
- **Domain:** inside the safety goal of `inflate`: the stream is reached by `inflateInit2` and
  `inflateGetHeader` with a header record whose extra buffer holds `extra_max` bytes
  (`ActiveHeader`), and `inflate` gets valid buffers. Checked by reading the premises.

# Do not fetch in gzgets() while a skip is pending

## Problem

`gz_skip()` (`gzread.c`) stops at the end of the input with the skip still pending. `gzgets()` then called `gz_fetch()` anyway, which in copy mode reads again although the end of file was seen. When the file had grown meanwhile (another writer appending to it), `gzgets()` returned the appended bytes, which lie before the position sought, and added them to `x.pos` with the skip still pending. After a seek to the largest position, `gztell()` then computed `x.pos + skip` with signed overflow (ISO C17 §6.5p5). `gz_read()` does not have the problem: when the skip is still pending and nothing is buffered, it reports the end of file.

## Fix

`gzgets()` calls `gz_fetch()` only when no skip is pending (`state->x.have == 0 && state->skip == 0 && gz_fetch(state) == -1`). A skip is still pending after `gz_skip()` only when it stopped at the end of the input with nothing buffered; `gzgets()` then reports the end of file (`past = 1`, and `NULL` when nothing was copied), as `gz_read()` does. Otherwise `gz_skip()` has done the whole skip and nothing changes.

madler/zlib changed the same situation differently with `f40786e3` ("Clear gz skip when forced seek reaches EOF.", TOB-ZLIB-006): `gz_skip()` clears the skip and sets `past` when it reaches the end of the input. That commit is not cherry-picked: it does not apply to zlib-ng's `gzread.c` with its context (only without any), and it changes what `gztell()` reports after any seek past the end of the input (the end of the file instead of the position sought), for every reader, which is beyond this defect. With this fix, `gztell()` keeps reporting the position sought until a read reaches the end of the file.

Add `gzip.seek_past_end_then_gets` in `test/test_gzseek.cc`: on a plain file of 3 bytes, a seek to the largest position, `gzungetc(-1, file)` to do the pending seek, the file grows by `"de\n"`, then `gzgets()` must return `NULL` and `gztell()` 3. It is skipped where `gzseek()` does not take a `z_off64_t` offset.

## Related Upstream References

- madler/zlib `f40786e3` (in zlib 1.4): a related change to `gz_skip()` at the end of the input, described above.
- Not yet submitted to zlib-ng.

## Review Feedback Addressed

- None yet (not submitted).

## Testing

- Clang, `ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, `-O0`, AddressSanitizer + UndefinedBehaviorSanitizer:
  - Before the fix: `gzgets()` returns the appended line, and the test aborts with "runtime error: signed integer overflow: 6 + 9223372036854775804" in `gztell64()`.
  - After the fix: passes.
- Clang, `ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`, same sanitizers: passes.

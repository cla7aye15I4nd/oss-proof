# Avoid signed overflow in gzseek() offset arithmetic

## Problem

`gzseek64()` does its offset arithmetic in `z_off64_t` without bounds (ISO C17 §6.5p5, signed overflow):

1. `SEEK_CUR` adds the pending skip to `offset` (`gzseek(file, INT64_MAX, SEEK_SET)` then `gzseek(file, 1, SEEK_CUR)`
   on a writer).
2. `SEEK_SET` subtracts `state->x.pos`, which is negative after `gzungetc()` at position 0
   (`gzseek(file, INT64_MAX, SEEK_SET)` after one `gzungetc()`).
3. The test of the raw area adds `state->x.pos` to the offset, and in transparent mode the `lseek()` offset subtracts
   the buffered output `state->x.have` (both near `2^63`, on a descriptor such as Linux `/dev/zero`).

Also, before the first read `state->x.next` has never been set, and a seek on a reader adds 0 to it: using an
indeterminate pointer value is undefined (C17 §6.2.4p2, §6.5.6p8) even with a zero offset. No sanitizer reports this
one.

madler/zlib fixed the overflows of items 1 and 3 in `6995c67b` and made a refused seek leave the position unchanged in
`6ed77c48`. Ported as they are, two cases remain: with `state->x.pos < 0` (after `gzungetc()` at the start)
`GZ_OFF_MAX - pos` overflows for any `SEEK_CUR`, and a target more than `GZ_OFF_MAX` past the negative position
overflows `pos - state->x.pos` (and the `lseek()` offset in transparent mode). The unset `state->x.next` is still
offset by 0.

## Fix

Five commits:

1. **Mark Adler**, madler/zlib `6995c67b` adapted to zlib-ng: define `GZ_OFF_MAX` in `gzguts.h`, compute the absolute
   target `pos` and refuse a target that does not fit in `z_off64_t` or lies before the start; transparent reads always
   seek with `lseek()`. Header documentation in `zlib.h.in` and `zlib-ng.h.in`.
2. **Mark Adler**, madler/zlib `6ed77c48` adapted: do not clear the pending skip before the checks, so a refused seek
   leaves the stream position unchanged; "If gzseek returns -1, the stream position is unchanged." in both headers.
3. Tests for 1 and 2 in `test/test_gzseek.cc`: `gzip.seek_offset_overflow`, `gzip.seek_failure_keeps_position`.
4. Test `GZ_OFF_MAX - pos` only when `pos > 0` (when `pos <= 0` the test cannot be true), and at a negative position
   refuse a target more than `GZ_OFF_MAX` past `state->x.pos`, so that `pos - state->x.pos` and the `lseek()` offset
   fit. Test `gzip.seek_from_negative_position` (transparent and gzip reads, after `gzungetc()` at the start).
5. Update the output buffer only when there is output and something to skip
   (`state->mode == GZ_READ && state->x.have && offset != 0`), so the unset `state->x.next` is never offset. Test
   `gzip.seek_before_first_read`.

After the series every step is in range for every reachable state: `pos` is `0` or `x.pos + skip` with
`x.pos + skip <= GZ_OFF_MAX` and `x.pos > -GZ_OFF_MAX - 1`; the refusals leave `0 <= pos <= GZ_OFF_MAX` and
`pos - x.pos <= GZ_OFF_MAX`; the `lseek()` offset `pos - x.pos - x.have` is at least `-(x.pos + x.have)`. Every refusal
returns before any store.

Changes of behaviour, both from zlib: a refused seek keeps the pending skip (before, a refused `SEEK_CUR` dropped it), and
after `gzungetc()` at position 0 a `SEEK_SET` to a negative offset is refused (before, it consumed pushed-back bytes and
returned a negative position). A seek more than `GZ_OFF_MAX` past a negative position is refused.

## Related Upstream References

- Updates open PR: https://github.com/zlib-ng/zlib-ng/pull/2525
- madler/zlib `6995c67b` ("Avoid signed-overflow undefined behaviors in gzseek.") and `6ed77c48` ("Leave the stream
  position unchanged when gzseek() fails."), both in zlib's `develop` branch.
- Related open madler/zlib PR for the negative-position overflow: https://github.com/madler/zlib/pull/1361

## Review Feedback Addressed

- The series now starts with `6995c67b` and `6ed77c48` as separate commits with the original author, adapted to
  zlib-ng; the earlier rewrite of `gzseek()` is dropped.
- `state->skip = 0` before the checks is gone (from `6ed77c48`); the sentence "If gzseek returns -1, the stream position
  is unchanged." is in `zlib.h.in` and `zlib-ng.h.in`. The writer test of the refused `SEEK_CUR` (`gzwrite` of one byte,
  `gzseek(100, SEEK_CUR)` returns 101, `gzseek(-200, SEEK_CUR)` returns -1, `gztell` stays 101) is in
  `gzip.seek_failure_keeps_position`; no test leaves a skip near `GZ_OFF_MAX` pending at `gzclose()`.
- Each extra change is its own commit with a test: the negative-position checks (commit 4: after a pushback,
  `gzseek(file, off_max, SEEK_SET)` returns -1; without the commit it overflows, `9223372036854775807 - -1`), and the
  `x.have && offset != 0` guard (commit 5; its test cannot fail without the commit, see Testing).
- `GZ_OFF_MAX` is zlib's definition from `6995c67b`; there is no separate commit for it.

## Testing

- Clang, `ZLIB_COMPAT=ON` and `WITH_OPTIM=OFF`, AddressSanitizer with `detect_invalid_pointer_pairs=2`
  (`-fsanitize=pointer-compare,pointer-subtract` on C) and UndefinedBehaviorSanitizer, `-O0`:
  - Without the series: `gzip.seek_offset_overflow` and `gzip.seek_from_negative_position` stop with
    `signed integer overflow` (`gzlib.c:412`, `gzlib.c:410`); `gzip.seek_failure_keeps_position` fails (`gztell` 1, not
    101, after the refused seek).
  - With commits 1-3 only: `gzip.seek_from_negative_position` stops with `signed integer overflow`
    (`9223372036854775807 - -1`).
  - With all five commits: the four tests pass.
- Clang, `ZLIB_COMPAT=OFF`, same sanitizers: the four tests pass.
- `gzip.seek_before_first_read` passes with and without commit 5: adding 0 to an unset pointer is undefined by the
  letter of C17 but no sanitizer reports it (AddressSanitizer fills new allocations, so the pointer is not `NULL`). The
  test guards the behaviour of seeks before the first read.
- Random sequences of `gzseek()` (offsets near `INT64_MIN` and `INT64_MAX`, both `whence` values), `gzungetc()` (also
  until the buffer is full), `gzread()`, `gzgetc()`, `gzgets()`, `gzclearerr()`, `gzrewind()` and `gzwrite()` on gzip
  and transparent readers and on writers, under the same sanitizers: no report with the series, and no refused seek
  changed `gztell()`. With commits 1-2 only the same runs report `signed integer overflow` at `gzlib.c:411`.

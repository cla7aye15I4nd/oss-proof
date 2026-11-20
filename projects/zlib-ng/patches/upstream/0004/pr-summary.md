# Avoid signed overflow in gzseek() offset arithmetic

## Problem

1. `gzseek64()` adds `state->skip` to `offset` on `SEEK_CUR` and subtracts `state->x.pos` on `SEEK_SET` without checking against the maximum representable `z_off64_t` (`GZ_OFF_MAX`), causing signed 64-bit integer overflow (ISO C17 §6.5p5).
2. Clearing `state->skip = 0` before validating the target offset discarded pending skips when `gzseek()` returned `-1`, changing subsequent `gztell()` results.
3. After `gzungetc()` at position zero (`state->x.pos == -1`), evaluating `GZ_OFF_MAX - pos` or `pos - state->x.pos` (both in `COPY`-mode `LSEEK` and when consuming pushback) can still overflow `z_off64_t` when seeking toward `GZ_OFF_MAX`.
4. Before the first read (`state->x.have == 0`), `state->x.next` is uninitialized; evaluating `state->x.next += 0` is undefined behavior in ISO C17 §6.5.6p8.

## Commits & Fix

1. **Mark Adler** (adapted from `madler/zlib@6995c67b`): define `GZ_OFF_MAX` in `gzguts.h`, guard `gzseek64()` offset arithmetic against signed overflow in `gzlib.c`, and document overflow returns in `zlib.h.in` and `zlib-ng.h.in`.
2. **Mark Adler** (adapted from `madler/zlib@6ed77c48`): preserve `state->skip` when `gzseek()` fails and document `"If gzseek returns -1, the stream position is unchanged."` in `zlib.h.in` and `zlib-ng.h.in`.
3. **Zheng Yu**: guard `state->x.pos < 0` (after `gzungetc()` at position zero) across `SEEK_CUR`, `COPY`-mode `LSEEK` offset calculation, and pushback discard prior to `pos - state->x.pos`; add `gzip.seek_offset_overflow` and `gzip.seek_from_negative_read_position` in `test/test_gzseek.cc`.
4. **Zheng Yu**: skip updating `state->x.next` when `state->x.have == 0` or zero buffered bytes are consumed.

## Related Upstream References

- Updates open PR: https://github.com/zlib-ng/zlib-ng/pull/2525
- Related open `madler/zlib` PR (covering commit 3's `gzungetc` negative-position overflow handling): https://github.com/madler/zlib/pull/1361

## Review Feedback Addressed

- Restructured to cherry-pick/adapt `madler/zlib@6995c67b` and `madler/zlib@6ed77c48` first as clean commits with original author attribution and header documentation in both `zlib.h.in` and `zlib-ng.h.in`, placing each additional change in its own commit on top.
- Fixed the dropped pending skip on failed seeks and added a regression check (`gzwrite("a", 1)` + `gzseek(100, SEEK_CUR)` + failed `gzseek(-200, SEEK_CUR)` preserving `gztell()`), cancelling the pending skip before `gzclose()`.
- Added `gzip.seek_from_negative_read_position` covering `gzungetc()` at position zero with `SEEK_CUR` and `SEEK_SET` to `off_max` on both raw and gzip streams (fails under UBSan on commits 1–2 alone, passes with commit 3).

## Testing

- Clang (`ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, ASan + UBSan + C pointer-pair) and Clang (`ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`, ASan + UBSan):
  - Before fix: fails under UBSan (`signed integer overflow`).
  - With commits 1–2 only: `gzip.seek_from_negative_read_position` fails under UBSan (`off_max - (-1)`).
  - Full 4-commit series: `gzip.seek_offset_overflow` and `gzip.seek_from_negative_read_position` both pass.

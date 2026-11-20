# PR 0004: Avoid signed overflow and unset pointer arithmetic in `gzseek()`

- **Proposed PR Title**: `Avoid signed overflow in gzseek() offset arithmetic`
- **Target Base**: `zlib-ng/zlib-ng` `develop` (`5f1f4899`)
- **Upstream PR**: https://github.com/zlib-ng/zlib-ng/pull/2525 (open; needs updated force-push)
- **Related `madler/zlib` PR**: https://github.com/madler/zlib/pull/1361 (open; corresponds to Commit 3/4's negative-position `gzungetc` overflow handling after `6995c67b`/`6ed77c48`)
- **Commits**: 4 (`upstream.patch`)
- **Files**: `gzguts.h`, `gzlib.c`, `zlib.h.in`, `zlib-ng.h.in`, `test/test_gzseek.cc`

## Problem & Root Cause

1. In `gzseek64()`, `SEEK_CUR` adds `state->skip` to `offset` and `SEEK_SET` subtracts `state->x.pos` without checking `GZ_OFF_MAX`, causing signed 64-bit overflow (ISO C17 §6.5p5).
2. Calling `gzseek()` when `state->skip` is active previously cleared `state->skip = 0` before checking failure conditions, corrupting subsequent `gztell()` results after a failing seek.
3. After `gzungetc()` at stream position zero (`state->x.pos == -1`), computing `GZ_OFF_MAX - pos` or `pos - state->x.pos` (in `COPY` `LSEEK` mode and in GZIP pushback consumption) still overflows when seeking toward `GZ_OFF_MAX`.
4. Before the first read (`state->x.have == 0`), `state->x.next` is uninitialized; evaluating `state->x.next += 0` is undefined behavior in ISO C17 §6.5.6p8.

## Commit Structure & Fix Summary

1. **Commit 1/4** (`Mark Adler`, adapted from `madler/zlib@6995c67b`): define `GZ_OFF_MAX` in `gzguts.h`, compute absolute `pos` safely for normal non-negative positions in `gzlib.c`, and document overflow returns in both `zlib.h.in` and `zlib-ng.h.in`.
2. **Commit 2/4** (`Mark Adler`, adapted from `madler/zlib@6ed77c48`): preserve `state->skip` when `gzseek()` fails and document `"If gzseek returns -1, the stream position is unchanged."` in `zlib.h.in` and `zlib-ng.h.in`.
3. **Commit 3/4** (`Zheng Yu`): harden `pos < 0` (`gzungetc` at position 0) across `SEEK_CUR`, `COPY`-mode `LSEEK` offset calculation, and pushback discard prior to `pos - state->x.pos`; add `gzip.seek_offset_overflow` and `gzip.seek_from_negative_read_position` in `test/test_gzseek.cc`.
4. **Commit 4/4** (`Zheng Yu`): guard the output buffer consumption block with `if (state->mode == GZ_READ && state->x.have)` and `if (n)` so unset `state->x.next` is never incremented by zero.

## Review Feedback Addressed (`nmoinvaz` & CodeRabbit on `#2525`)

- **Clean `madler/zlib` commit attribution & split structure (`nmoinvaz` #1)**: Cherry-picked/adapted `6995c67b` and `6ed77c48` cleanly first with original author attribution and NO tests mixed into upstream commits, followed by dedicated hardening commits on top.
- **Removed premature `state->skip = 0` + failure `gztell()` test (`nmoinvaz` #2)**: Fixed via `6ed77c48` (Commit 2/4) and added the `gzwrite("a", 1)` + `gzseek(100, SEEK_CUR)` + failed `gzseek(-200, SEEK_CUR)` + `gztell() == 102` check in `test/test_gzseek.cc`.
- **Cancel pending skip before closing (`nmoinvaz` #3)**: Cancelled the 100-byte pending skip via `gzseek(wfile, 2, SEEK_SET)` before `gzclose()`.
- **Negative `x.pos` test reaching `off_max` without overflow (`nmoinvaz` #4 & CodeRabbit)**: Commit 2/4 (`6995c67b + 6ed77c48`) fails `gzip.seek_from_negative_read_position` under UBSan (`off_max - (-1)` signed overflow in both `COPY` and `GZIP` modes), and Commit 3/4 passes by discarding pushback prior to subtraction rather than computing `9223372036854775807 - (-1)`.
- **Test file location & dual headers**: Moved tests into `test/test_gzseek.cc` and updated both `zlib.h.in` and `zlib-ng.h.in`.

## Overlaps & Dependencies

- **Merge before `0016` and `0017`**: `0004` introduces `GZ_OFF_MAX` in `gzguts.h`, which `0016` and `0017` reuse.
- **Shared test file**: `0020` and `0021` also append to `test/test_gzseek.cc` (EOF-only).

## Verification

- `build-compat-san` & `build-native-san`:
  - Before fix (`5f1f4899`): fails under UBSan (`signed integer overflow`).
  - Commit 2/4 (`6995c67b + 6ed77c48` only): fails `gzip.seek_from_negative_read_position` under UBSan as expected.
  - Full 4-commit series: `gzip.seek_offset_overflow` and `gzip.seek_from_negative_read_position` both pass (`[  PASSED  ] 2 tests.`), and stacked with `0014+0016+0017+0022` (`85 compat / 83 native` passed).

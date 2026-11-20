# PR 0021: Do not fetch past EOF or a pending skip in `gzgets()`

- **Proposed PR Title**: `Clear gz skip at EOF and do not fetch past it in gzgets()`
- **Target Base**: `zlib-ng/zlib-ng` `develop` (`5f1f4899`)
- **Upstream PR**: Ready to submit (rebase on `0020` if `0020` merges first)
- **Commits**: 2 (`upstream.patch`)
- **Files**: `gzread.c`, `test/test_gzseek.cc`

## Problem & Root Cause

Two related bugs occur when a pending `gzseek()` skip hits EOF on a `COPY` (or transparent) read stream:

1. In `gz_skip()`, reaching `state->eof && state->strm.avail_in == 0` stops without clearing `state->skip` or setting `state->past = 1`, so forced skips (such as `gzungetc(-1, file)`) cause `gztell()` to report the unreached seek target instead of the actual EOF offset (TOB-ZLIB-006, `madler/zlib@f40786e3`).
2. Unlike `gz_read()`, `gzgets()` did not check `state->skip || (state->eof && state->strm.avail_in == 0)` before calling `gz_fetch()`. If a pending skip reached EOF or the file later appended data without `gzclearerr()`, `gzgets()` re-fetched and returned pre-seek bytes while `state->skip` remained near `GZ_OFF_MAX`, overflowing `gztell()` (`state->x.pos + state->skip`, ISO C17 §6.5p5).

## Commit Structure & Fix Summary

1. **Commit 1/2** (`ronald.eytchison@trailofbits.com`, adapted from `madler/zlib@f40786e3`): clear `state->skip = 0;` and set `state->past = 1;` when `gz_skip()` stops at EOF.
2. **Commit 2/2** (`Zheng Yu`): in `gzgets()`, check `if (state->x.have == 0 && (state->skip || (state->eof && state->strm.avail_in == 0)))` to set `state->past = 1` and break before calling `gz_fetch()`, and add `gzip.gets_pending_skip_after_eof` in `test/test_gzseek.cc`.

## Overlaps & Dependencies

- **Merge after `0020`**: both edit `gz_skip()` in `gzread.c` (`0020` introduces `gz_skip_have()`; `0021` modifies the `else if (state->eof && ...)` branch cleanly).
- **`test/test_gzseek.cc`**: shares file EOF with `0004` (`#2525`) and `0020`.

## Verification

- `build-compat-san` & `build-native-san`:
  - Before fix (`5f1f4899`): `gzip.gets_pending_skip_after_eof` fails (`gztell` overflows / returns `off_max` instead of `3`, and `gzgets()` reads appended `"de\n"` from offset 3 instead of returning `NULL`).
  - After fix: passes on both builds (`[  PASSED  ] 1 test.`).

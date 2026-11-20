# Clear gz skip at EOF and do not fetch past it in gzgets()

## Problem

Two related issues arise when a pending `gzseek()` skip reaches EOF while reading:

1. In `gz_skip()`, stopping at `state->eof && state->strm.avail_in == 0` left `state->skip` non-zero and `state->past` unset, so forced skips (e.g., via `gzungetc(-1, file)`) caused `gztell()` to report the unreached seek target instead of the actual EOF offset (TOB-ZLIB-006).
2. Unlike `gz_read()`, `gzgets()` did not check `state->skip || (state->eof && state->strm.avail_in == 0)` before calling `gz_fetch()`. If a file grew after EOF without `gzclearerr()`, `gzgets()` fetched and returned pre-seek bytes and could advance `state->x.pos` while `state->skip` remained pending near `GZ_OFF_MAX`, overflowing `gztell()` (ISO C17 §6.5p5).

## Commits & Fix

1. **ronald.eytchison@trailofbits.com** (adapted from `madler/zlib@f40786e3`, TOB-ZLIB-006): set `state->skip = 0;` and `state->past = 1;` when `gz_skip()` reaches EOF.
2. **Zheng Yu**: in `gzgets()`, stop with `state->past = 1` before calling `gz_fetch()` when `state->x.have == 0 && (state->skip || (state->eof && state->strm.avail_in == 0))`, matching `gz_read()`, and add `gzip.gets_pending_skip_after_eof` in `test/test_gzseek.cc`.

## Testing

- Clang (`ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, ASan + UBSan) and Clang (`ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`, ASan + UBSan):
  - Before fix: `gzip.gets_pending_skip_after_eof` fails (`gztell()` returns `off_max` instead of `3`, and `gzgets()` reads appended data past EOF).
  - After fix: passes in both builds.

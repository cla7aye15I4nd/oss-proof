# PR 0020: Apply and guard pending skips in `gzdirect()`

- **Proposed PR Title**: `Apply a pending skip in gzdirect() after gz_look()`
- **Target Base**: `zlib-ng/zlib-ng` `develop` (`5f1f4899`)
- **Upstream PR**: Ready to submit
- **Commits**: 2 (`upstream.patch`)
- **Files**: `gzread.c`, `test/test_gzseek.cc`

## Problem & Root Cause

On a non-gzip (transparent) input, seeking forward before the first read sets `state->skip`, then calling `gzdirect()` triggers `gz_look()`, which buffers available bytes into `state->x.have` while leaving `state->skip` non-zero. Because the public `gzgetc()` macro consumes buffered bytes directly when `x.have != 0` without running `gz_skip()`, subsequent reads return pre-seek bytes and increment `state->x.pos` while `state->skip` remains active near `GZ_OFF_MAX`, causing `gztell()` (`state->x.pos + state->skip`) to overflow (ISO C17 §6.5p5).

Also, calling `gz_skip_have()` unconditionally right after `gz_look()` when `state->x.have == 0` and `state->skip == 0` evaluates `state->x.next += 0` on an unset pointer when empty or unseeked (ISO C17 §6.5.6p8).

## Commit Structure & Fix Summary

1. **Commit 1/2** (`M0nd0R`, adapted from `madler/zlib@b2596bde`): extract `gz_skip_have(gz_state *)` from `gz_skip()` and call it in `gzdirect()` after `gz_look()`.
2. **Commit 2/2** (`Zheng Yu`): guard `if (state->x.have && state->skip)` before calling `gz_skip_have(state)`, and add `gzip.direct_read_keeps_pending_seek` in `test/test_gzseek.cc` covering both normal seeks and seeks to `off_max`.

## Overlaps & Dependencies

- **Merge before `0021`**: both touch `gzread.c` (`gz_skip` / `gzdirect` vs `gz_skip` / `gzgets`). Rebase `0021` cleanly on top of `0020`.
- **`gzread.c`**: disjoint hunks from `0016`.
- **`test/test_gzseek.cc`**: shares file EOF with `0004` (`#2525`) and `0021`.

## Verification

- `build-compat-san` & `build-native-san`:
  - Before fix (`5f1f4899`): `gzip.direct_read_keeps_pending_seek` fails (`gzgetc()` returns pre-seek bytes and triggers UBSan `signed integer overflow` inside `gztell64()`).
  - After fix: passes on both builds (`[  PASSED  ] 1 test.`).

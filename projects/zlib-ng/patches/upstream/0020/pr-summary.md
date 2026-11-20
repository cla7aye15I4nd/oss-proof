# Apply a pending skip in gzdirect() after gz_look()

## Problem

On non-gzip (transparent) input, seeking forward before the first read records `state->skip`. Calling `gzdirect()` then invokes `gz_look()`, which buffers available bytes into `state->x.have` while leaving `state->skip` active. Because `gzgetc()` (and the public `gzgetc()` macro) consumes buffered bytes directly when `state->x.have != 0` without running `gz_skip()`, subsequent reads return pre-seek bytes and advance `state->x.pos` while `state->skip` stays near `GZ_OFF_MAX`, causing `gztell()` (`state->x.pos + state->skip`) to overflow signed 64-bit arithmetic (ISO C17 §6.5p5).

Additionally, calling `gz_skip_have()` unconditionally after `gz_look()` when `state->x.have == 0` evaluates `state->x.next += 0` on an unset pointer (ISO C17 §6.5.6p8).

## Commits & Fix

1. **M0nd0R** (adapted from `madler/zlib@b2596bde`): extract `gz_skip_have(gz_state *)` from `gz_skip()` and apply it in `gzdirect()` after `gz_look()`.
2. **Zheng Yu**: guard the call with `if (state->x.have && state->skip)` to avoid pointer arithmetic on an unset `state->x.next`, and add `gzip.direct_read_keeps_pending_seek` in `test/test_gzseek.cc` covering both normal seeks and seeks to `off_max`.

## Testing

- Clang (`ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, ASan + UBSan) and Clang (`ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`, ASan + UBSan):
  - Before fix: `gzip.direct_read_keeps_pending_seek` fails (`gzgetc()` returns pre-seek bytes and triggers UBSan `signed integer overflow` in `gztell64()`).
  - After fix: passes in both builds.

# Bound gzip read position on every public read path

## Problem

After seeking near `GZ_OFF_MAX` (`2^63 - 1`) on a seekable descriptor that continues supplying bytes (such as `/dev/zero`):

1. `gz_look()` (`COPY` mode) and `gz_fetch()` (`COPY` and `GZIP` modes) buffer up to `state->size << 1` bytes so `state->x.pos + state->x.have` can exceed `GZ_OFF_MAX`.
2. The public `gzgetc()` macro in `zlib.h.in` / `zlib-ng.h.in` increments `(g)->pos++` directly in caller code whenever `(g)->have != 0`, overflowing signed 64-bit `z_off64_t` (ISO C17 §6.5p5) without entering library code.
3. `gz_read()` and `gzgets()` also add delivered byte counts to `state->x.pos` without checking remaining representable range.

## Fix

Maintain the invariant `state->x.pos + state->x.have <= GZ_OFF_MAX` via a helper `gz_room(gz_state *state, unsigned max)` (handling negative `state->x.pos` after `gzungetc()` at position zero as well):

- **`gz_look()`** (`COPY` setup): cap `state->x.have = gz_room(state, strm->avail_in)` and report `Z_DATA_ERROR` (`"position overflow"`) if unbuffered input remains.
- **`gz_fetch()`**: limit buffered fetches to `room = gz_room(state, state->size << 1)` bytes; when `room == 0` (already at `GZ_OFF_MAX`), fetch at most 1 byte solely to distinguish clean EOF from excess data (which `gz_read()` / `gzgets()` rejects with `Z_DATA_ERROR`, leaving `state->x.have == 0` so the public `gzgetc()` macro never executes `pos++` at `GZ_OFF_MAX`).
- **`gz_read()` & `gzgets()`**: clamp each step with `gz_room()` and raise `Z_DATA_ERROR` (`"position overflow"`) when extra data is present at `GZ_OFF_MAX`.

Add Linux regression test `gzip.read_position_overflow` in `test/test_gzio.cc` covering the public `gzgetc()` macro, `gzread()`, and `gzgets()` on `/dev/zero`.

## Related Upstream References

- Related open `madler/zlib` PR: https://github.com/madler/zlib/pull/1405 (shares the same `gz_room()` design in `gzread.c`, extended here with `state->x.pos < 0` handling and GoogleTest coverage).
- Note: defines `GZ_OFF_MAX` in `gzguts.h` identically to https://github.com/zlib-ng/zlib-ng/pull/2525 so this PR builds standalone; if `#2525` merges first, that hunk can be dropped cleanly.

## Testing

- Clang (`ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, ASan + UBSan) and Clang (`ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`, ASan + UBSan) on Linux:
  - Before fix: aborts under UBSan (`signed integer overflow: 9223372036854775807 + 1`) inside the public `gzgetc()` macro.
  - After fix: `gzip.read_position_overflow` passes in both builds.

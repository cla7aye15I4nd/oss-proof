# PR 0016: Bound gzip read position on every public read path

- **Proposed PR Title**: `Bound gzip read position on every public read path`
- **Target Base**: `zlib-ng/zlib-ng` `develop` (`5f1f4899`)
- **Upstream PR**: Ready to submit (depends on `GZ_OFF_MAX` from `#2525` or drops `gzguts.h` hunk after `#2525` merges)
- **Commits**: 1 (`upstream.patch`)
- **Files**: `gzguts.h`, `gzread.c`, `test/test_gzio.cc`

## Problem & Root Cause

After seeking near `GZ_OFF_MAX` (`2^63 - 1`) on a seekable stream that delivers data past that offset (e.g., `/dev/zero` or a sparse/streaming descriptor):

1. `gz_look()` (`COPY` mode) and `gz_fetch()` (`COPY` and `GZIP` modes) buffer up to `state->size << 1` bytes so `state->x.pos + state->x.have` can exceed `GZ_OFF_MAX`.
2. Even more critically, the public **`gzgetc()` macro** in `zlib.h.in` / `zlib-ng.h.in` fast-paths directly on caller expansion whenever `state->x.have != 0`:
   ```c
   ((g)->have ? ((g)->have--, (g)->pos++, *((g)->next)++) : (gzgetc)(g))
   ```
   When `gz_look()`/`gz_fetch()` buffers bytes past `GZ_OFF_MAX`, `(g)->pos++` overflows signed 64-bit `z_off64_t` directly in the caller (which cannot be changed without breaking ABI/headers).
3. `gz_read()` and `gzgets()` also increment `state->x.pos` without checking remaining representable range.

## Fix Summary

Maintain the invariant **`state->x.pos + state->x.have <= GZ_OFF_MAX`** via a helper `gz_room(gz_state *state, unsigned max)`:

- **`gz_look()`** (`COPY` setup): cap initial `state->x.have = gz_room(state, strm->avail_in);` and report `Z_DATA_ERROR` (`"position overflow"`) if unbuffered input remains.
- **`gz_fetch()`**: fetch at most `room = gz_room(state, state->size << 1)` bytes (`COPY` `gz_load` and `GZIP` `avail_out`); if `room == 0` (already at `GZ_OFF_MAX`), fetch 1 byte solely to distinguish clean EOF (`0` bytes -> clean EOF) from extra data (`1` byte -> `gz_read`/`gzgets` reports `Z_DATA_ERROR`). Because `x.pos == GZ_OFF_MAX` implies `state->x.have <= 1`, and at `room == 0` callers cannot take the buffered fast path without calling `gz_read()`/`gzgets()` (`x.have == 0` at `GZ_OFF_MAX` is preserved before returning to caller), the `gzgetc()` macro never executes `pos++` at `GZ_OFF_MAX`!
- **`gz_read()` & `gzgets()`**: clamp `n = gz_room(state, n)`; if `n == 0` (when `have != 0`), clear `state->x.have = 0`, raise `Z_DATA_ERROR` (`"position overflow"`), and break.

Add Linux regression test `gzip.read_position_overflow` in `test/test_gzio.cc` testing `/dev/zero` across the public `gzgetc()` macro, `gzread()`, and `gzgets()` at `off_max`.

## Overlaps & Dependencies

- **`gzguts.h` (`GZ_OFF_MAX`)**: shared identically with `0004` (`#2525`) and `0017`. Once `#2525` lands, drop the `gzguts.h` hunk in this PR.
- **`gzread.c`**: disjoint hunks from `0020` and `0021`.
- **`test/test_gzio.cc`**: shares file with `0017` and `0022`.

## Verification

- `build-compat-san` & `build-native-san`:
  - Before fix (`5f1f4899`): fails on `/dev/zero` under UBSan (`signed integer overflow` in public `gzgetc()` macro: `9223372036854775807 + 1`).
  - After fix: `gzip.read_position_overflow` passes on both builds (`[  PASSED  ] 1 test.`), and passes cleanly when stacked with `0004+0014+0017+0022`.

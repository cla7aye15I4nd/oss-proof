# PR 0017: Bound gzip write position without truncating remaining capacity

- **Proposed PR Title**: `Bound gzip write position without truncating remaining capacity`
- **Target Base**: `zlib-ng/zlib-ng` `develop` (`5f1f4899`)
- **Upstream PR**: Ready to submit (separated from `0022` `gz_zero` fix; reuses `GZ_OFF_MAX` from `#2525`)
- **Related `madler/zlib` PR**: https://github.com/madler/zlib/pull/1406 (open; uses `z_size_t` round-trip check in `madler/zlib`, whereas this `zlib-ng` series uses explicit `uint64_t` comparison across `gz_write()` and `gzvprintf()` plus a 4 GiB boundary test)
- **Commits**: 1 (`upstream.patch`)
- **Files**: `gzguts.h`, `gzwrite.c`, `test/test_gzio.cc`

## Problem & Root Cause

`gz_write()`, `gzputc()`, and `gzvprintf()` increment `state->x.pos` (signed `z_off64_t`) without checking whether the write exceeds `GZ_OFF_MAX`. On writable streams whose descriptor continues accepting bytes or rejecting writes (`gzfwrite` + `gzclearerr`), `state->x.pos` overflows signed 64-bit arithmetic (ISO C17 §6.5p5).

Additionally, comparing remaining capacity via `(size_t)(GZ_OFF_MAX - state->x.pos)` truncates on ILP32 targets with 64-bit `off64_t` (`_FILE_OFFSET_BITS=64`): at `x.pos = 0xffffffff`, `GZ_OFF_MAX - x.pos` truncates in 32-bit `size_t` to `0`, falsely rejecting a valid 1-byte write across the 4 GiB boundary.

## Fix Summary

- Compare `(uint64_t)len > (uint64_t)(GZ_OFF_MAX - state->x.pos)` in both `gz_write()` and `gzvprintf()` (`gz_write_init` already ran and `x.pos >= 0`, so `GZ_OFF_MAX - state->x.pos` is non-negative), failing with `Z_DATA_ERROR` (`"write position does not fit in z_off64_t"`) before touching the caller buffer.
- Guard `gzputc()`'s buffer fast path with `have < state->size && state->x.pos != GZ_OFF_MAX` so reaching `GZ_OFF_MAX` falls into `gz_write()` and raises `Z_DATA_ERROR`.
- Add `gzip.write_across_4gb_boundary` in `test/test_gzio.cc` (seeks to `0xffffffff` on `/dev/null` `"wbT"` with `gzbuffer(..., 1 << 26)` and writes 1 byte, confirming `gztell == 0x100000000` in ~20 ms and catching 32-bit `size_t` truncation regressions).

## Changes Since Draft

- **Split `gz_zero()` failure accounting out to `0022`**: Commit 1 of the earlier draft (`madler/zlib@51c7cd2c` `gz_zero` accounting) now lives in its own independent series [0022](../0022/pr-summary.md).
- **Used `uint64_t` consistently** in both `gz_write()` and `gzvprintf()`.

## Overlaps & Dependencies

- **`gzguts.h` (`GZ_OFF_MAX`)**: shared identically with `0004` (`#2525`) and `0016`. Drop the `gzguts.h` hunk once `#2525` merges.
- **`gzwrite.c` & `test/test_gzio.cc`**: disjoint from `0014` and `0022`.

## Verification

- `build-compat-san` & `build-native-san`:
  - `gzip.write_across_4gb_boundary` passes on both builds (`[  PASSED  ] 1 test.`), and passes stacked with `0004+0014+0016+0022`.
  - Note: on LP64 `5f1f4899`, triggering `x.pos` overflow past `2^63 - 1` via repeated failing `gzfwrite()` + `gzclearerr()` calls takes ~7 minutes and is documented in [../../README.md](../../README.md); this test guards against the 32-bit `size_t` truncation regression cleanly in CI.

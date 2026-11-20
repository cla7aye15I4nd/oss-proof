# Bound gzip write position without truncating remaining capacity

## Problem

`gz_write()`, `gzputc()`, and `gzvprintf()` advance `state->x.pos` (signed `z_off64_t`) without checking whether the resulting position exceeds `GZ_OFF_MAX` (ISO C17 §6.5p5).

Additionally, comparing remaining capacity via `(size_t)(GZ_OFF_MAX - state->x.pos)` truncates on ILP32 targets with 64-bit `off64_t` (`_FILE_OFFSET_BITS=64`): at `x.pos = 0xffffffff`, `GZ_OFF_MAX - x.pos` truncates in 32-bit `size_t` to `0`, falsely refusing a valid 1-byte write across the 4 GiB boundary.

## Fix

- In `gz_write()` and `gzvprintf()`, compare `(uint64_t)len > (uint64_t)(GZ_OFF_MAX - state->x.pos)` (after `gz_write_init()` ensures `state->x.pos >= 0`) and report `Z_DATA_ERROR` (`"write position does not fit in z_off64_t"`) before modifying the stream or reading the caller buffer.
- In `gzputc()`, guard the buffered fast path with `have < state->size && state->x.pos != GZ_OFF_MAX` so writes at `GZ_OFF_MAX` fall through to `gz_write()` and return `Z_DATA_ERROR`.
- Add `gzip.write_across_4gb_boundary` in `test/test_gzio.cc` seeking to `0xffffffff` on `/dev/null` (`"wbT"`, `gzbuffer(..., 1 << 26)`) and writing 1 byte to verify `gztell() == 0x100000000` without 32-bit truncation.

## Related Upstream References

- Related open `madler/zlib` PR: https://github.com/madler/zlib/pull/1406 (`#1406` checks whether `room` round-trips through `z_size_t`, whereas this PR compares directly in `uint64_t` across `gz_write()` and `gzvprintf()` and adds a 4 GiB boundary GoogleTest).
- Note: defines `GZ_OFF_MAX` in `gzguts.h` identically to https://github.com/zlib-ng/zlib-ng/pull/2525 so this PR builds standalone; if `#2525` merges first, that hunk can be dropped cleanly.

## Testing

- Clang (`ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, ASan + UBSan) and Clang (`ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`, ASan + UBSan): `gzip.write_across_4gb_boundary` passes in both builds.

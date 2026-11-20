# PR 0006: Truncate `gzhead->extra_len` to 16 bits in `deflateBound()`

- **Proposed PR Title**: `Truncate gzhead->extra_len to 16 bits in deflateBound()`
- **Target Base**: `zlib-ng/zlib-ng` `develop` (`5f1f4899`)
- **Upstream PR**: https://github.com/zlib-ng/zlib-ng/pull/2523 (open; needs updated force-push)
- **Related `madler/zlib` PR**: https://github.com/madler/zlib/pull/1360 (open; `#1360` retains `(z_size_t)` before bitwise mask, whereas this `zlib-ng` PR drops the cast per `nmoinvaz`'s inline feedback and adds GoogleTest coverage)
- **Commits**: 1 (`upstream.patch`)
- **Files**: `deflate.c`, `test/test_deflate_bound.cc`

## Problem & Root Cause

In `deflateBound_z()`, when a user gzip header provides a non-NULL `extra` buffer:

```c
wraplen += 2 + s->gzhead->extra_len;
```

`deflate()` writes only `extra_len & 0xffff` (the low 16 bits, both in `put_short()` and in the `EXTRA_STATE` copy loop; a valid gzip header extra field cannot exceed 65,535 bytes). Because `extra_len` has type `uint32_t` (`unsigned int`), `2 + s->gzhead->extra_len` evaluates in 32-bit unsigned arithmetic on every platform (both 32-bit and 64-bit) before widening to `z_size_t`:

- For `0x10000 <= extra_len <= 0xfffffffd`, `deflateBound()` overestimates by up to 4 GiB.
- For the exact two values `extra_len == 0xfffffffe` and `extra_len == 0xffffffff`, `2 + extra_len` wraps in 32-bit unsigned arithmetic to `0` or `1` bytes instead of `65536` or `65537`, causing a single `deflate(strm, Z_FINISH)` with `avail_out == deflateBound()` to return `Z_OK` instead of `Z_STREAM_END` (contract failure against `zlib.h`; no buffer overflow occurs).

## Fix Summary

Mask `extra_len` to 16 bits in `deflate.c`:

```c
wraplen += 2 + (s->gzhead->extra_len & 0xffff);
```

Because `(s->gzhead->extra_len & 0xffff) <= 65535`, `2 + ... <= 65537` never wraps in `uint32_t`, so no cast is needed.

Add `deflate_bound.gzip_extra_len_truncated` in `test/test_deflate_bound.cc` checking `0xffff`, `UINT32_MAX` (including `deflate(Z_FINISH) == Z_STREAM_END` with `avail_out == bound_u32max`), `0x10000`, and `0`.

## Review Feedback Addressed (`nmoinvaz` on `#2523`)

- **Maintainer question (*"in what case will this occur?"*)**: Occurs on any 32-bit or 64-bit build if a caller sets `gzhead->extra != NULL` and `gzhead->extra_len >= 0x10000` — specifically underestimating only at `0xfffffffe` and `0xffffffff` (cleanup / `deflateBound()` contract consistency; valid gzip headers have `extra_len <= 0xffff`).
- **Remove unnecessary cast (`nmoinvaz` inline #1)**: Removed the cast cleanly (`wraplen += 2 + (s->gzhead->extra_len & 0xffff);`).
- **Fix commit message & description (`nmoinvaz` #2)**: Removed the inaccurate claim about 32-bit `unsigned long`, clarified 32-bit `unsigned int` (`uint32_t`) wraparound on every platform, and listed the exact two underestimating values (`0xfffffffe` and `0xffffffff`).
- **Strengthen test**: Added an actual `deflate(Z_FINISH)` call using `avail_out = bound_u32max` to assert `Z_STREAM_END`.

## Overlaps & Dependencies

- None (`deflate.c` `deflateBound_z()` and `test/test_deflate_bound.cc` are untouched by all other series).

## Verification

- `build-compat-san` & `build-native-san`:
  - Before fix (`5f1f4899`): `deflate_bound.gzip_extra_len_truncated` fails (`bound_u32max != bound_16bit`, `deflate(Z_FINISH)` returns `Z_OK != Z_STREAM_END`, `bound_64k != bound(0)`).
  - After fix: passes on both (`[  PASSED  ] 1 test.`).

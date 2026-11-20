# Refuse gz writes that would move the position past GZ_OFF_MAX

## Problem

The gz writers add each length to the signed 64-bit `state->x.pos` without a bound, and they do it before writing, so a failed write keeps the addition. After `2^63` bytes in all, failed writes included, `x.pos += n` in `gz_write()` (`gzwrite.c`) overflows (ISO C17 §6.5p5). This is reachable through documented calls only: a transparent writer whose descriptor rejects every write, `2^31 + 1` calls of `gzfwrite()` with `2^32 - 1` bytes each, each followed by `gzclearerr()` (UndefinedBehaviorSanitizer reports the overflow in `gz_write()` at the last call; about 7 minutes).

## Fix

- `gz_write()` refuses a write that would move `x.pos` past `GZ_OFF_MAX` (`(uint64_t)len > (uint64_t)(GZ_OFF_MAX - x.pos)`, after a pending seek is done) with `Z_DATA_ERROR` and the message "write position does not fit in z_off64_t", before it touches the caller's buffer.
- `gzputc()` takes its buffer fast path only while `x.pos != GZ_OFF_MAX` (otherwise `gz_write()` refuses).
- `gzvprintf()` refuses a formatted length above `GZ_OFF_MAX - x.pos` the same way.

`x.pos` is never negative when writing, so `GZ_OFF_MAX - x.pos` does not overflow. `gz_write()` compares in `uint64_t`, which holds every `size_t` and every non-negative `z_off64_t`: where `size_t` has 32 bits and `z_off64_t` 64 (a 32-bit build with `_FILE_OFFSET_BITS=64`), converting the room left to `size_t` would keep its low 32 bits and refuse legal writes. Below `GZ_OFF_MAX` nothing changes. `gz_zero()` needs no bound: the `gzseek64()` fix keeps `x.pos + skip <= GZ_OFF_MAX`, and the `gz_zero()` fix ("Take each batch of zeros off skip before writing it") keeps it when a write of the zeros fails. `GZ_OFF_MAX` is defined in `gzwrite.c` unless already defined (the `gzseek64()` fix in https://github.com/zlib-ng/zlib-ng/pull/2525 adds it to `gzguts.h`).

Add `gzip.write_position_past_4gb` in `test/test_gzio.cc`: a transparent writer on `/dev/null` seeks to `2^32 - 1` (writing that many zeros) and writes one byte; the write must succeed and `gztell()` must return `2^32`. The overflow itself takes too long for a test, so this test does not fail without the fix; it fails on a 32-bit `size_t` build if the bound is compared in `size_t`. It is skipped where `gzseek()` does not take a 64-bit offset.

## Related Upstream References

- Not yet submitted to zlib-ng. The same overflow is reported to madler/zlib in https://github.com/madler/zlib/pull/1406 (open, not merged), with the same three checks in a different form (the room is kept in `z_off64_t` and tested for fitting in `z_size_t`; message "position overflow"). madler/zlib `develop` has no bound on the write position.

## Review Feedback Addressed

- None yet (not submitted).

## Testing

- Clang, `ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, `-O0`, AddressSanitizer + UndefinedBehaviorSanitizer: `gzip.write_position_past_4gb` passes with the fix, and also without it (LP64).
- Clang, `ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`, same sanitizers: passes.
- The overflow was reproduced through the call sequence in Problem (UndefinedBehaviorSanitizer, `gz_write()`); with the fix that call is refused with `Z_DATA_ERROR`.

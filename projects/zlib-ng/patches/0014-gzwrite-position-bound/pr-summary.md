# Refuse gz writes that would move the position past GZ_OFF_MAX

Status: tests and upstream-style commit message pending

## Problem

The writers added each length to the signed 64-bit `x.pos` without a bound, before writing (a failed write keeps the addition): after `2^63` bytes in all, `x.pos += n` overflowed (ISO C17 §6.5p5).

## Fix

Files: `gzwrite.c`.

`gz_write` refuses a write that would move `x.pos` past `GZ_OFF_MAX` (`(uint64_t)len > (uint64_t)(GZ_OFF_MAX - x.pos)`, after a pending seek is done) with `Z_DATA_ERROR` and the message "write position does not fit in z_off64_t", before it touches the caller's buffer; `gzputc` takes its buffer fast path only while `x.pos != GZ_OFF_MAX` (else `gz_write` refuses); `gzvprintf` refuses a formatted length above `GZ_OFF_MAX - x.pos` the same way. `x.pos` is never negative when writing, so `GZ_OFF_MAX - x.pos` does not overflow, and both sides of the `gz_write` test are converted to `uint64_t`, which holds every `size_t` and every non-negative `z_off64_t` value. Below that position nothing changes. `gz_zero` needs no bound: patch 0002 keeps `x.pos + skip <= GZ_OFF_MAX`, and patch 0019 keeps it when a write of the zeros fails.

## Related Upstream References

- Related madler/zlib PR: https://github.com/madler/zlib/pull/1406 (open).

## Review Feedback Addressed

- None yet.

## Testing

- Reproduction in the project's regression suite: `gzwrite-position-32bit`.
- Confirmed on real C: yes, through documented calls only (UndefinedBehaviorSanitizer, `gzwrite.c:210`, at the 2147483649th failing `gzfwrite` of `2^32 - 1` bytes, followed each time by `gzclearerr`, on a transparent writer whose descriptor rejects every write: about 7 minutes; with the patch that call is refused with `Z_DATA_ERROR`).
- No GoogleTest case in this series yet.

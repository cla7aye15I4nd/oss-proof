# Call inflate_fast() from inflate() only with fewer than 8 bits held

Status: tests and upstream-style commit message pending

## Problem

When `inflatePrime` has left 8 or more bits in the bit buffer, `inflate_fast` returns `bits >> 3` bytes of input on exit (`in -= len`, `inffast_tpl.h:327`), more than it read: `next_in` moves before the caller's buffer (ISO C17 §6.5.6p8), `avail_in` grows past what the caller gave and `total_in` wraps.

## Fix

Files: `inflate.c`.

`inflate` (state `LEN`) calls `inflate_fast` only when fewer than 8 bits are held (`bits < 8`), which `inflate_fast` assumes; otherwise it decodes the code in `inflate` itself. Without `inflatePrime` fewer than 8 bits are always held there, so nothing else changes.

## Related Upstream References

- Covered by open zlib-ng PR https://github.com/zlib-ng/zlib-ng/pull/2526 (another contributor), which fixes the exit of `inflate_fast()` instead; madler/zlib fixed it the way this directory does (`e7bb9788`).

## Review Feedback Addressed

- None yet.

## Testing

- Reproduction in the project's regression suite: `inflate-fast-primed-bits`.
- Confirmed on real C: yes (`avail_in` and `total_in` after the call); no sanitizer reports the pointer itself.
- No GoogleTest case in this series yet.

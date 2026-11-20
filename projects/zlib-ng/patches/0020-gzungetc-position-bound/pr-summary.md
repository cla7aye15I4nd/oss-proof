# Bound the position lowered by gzungetc()

Status: tests and upstream-style commit message pending

## Problem

`gzungetc` lowers `x.pos` for each push; a failed push when the buffer is full (`gz_error`) drops the pushed bytes but keeps the lowered `x.pos`, and after `gzclearerr` the pushes start again, so `x.pos` goes down without a bound and `x.pos--` overflows after about `2^63` pushes (ISO C17 §6.5p5). The bound is `-GZ_OFF_MAX` rather than the minimum value because `gzseek64` (`SEEK_CUR`, patch 0002) negates a negative position.

## Fix

Files: `gzread.c`.

`gzungetc` returns -1 without pushing when `x.pos <= -GZ_OFF_MAX` (after the test `c < 0`), so `x.pos` stays above `INT64_MIN`. Below the bound nothing changes: a push needs about `2^63` calls to reach it.

## Related Upstream References

- Not yet submitted upstream.

## Review Feedback Addressed

- None yet.

## Testing

- No reproduction in the regression suite (the overflow needs about `2^63` calls).
- Confirmed on real C: the mechanism yes (`gztell` decreases without a bound); the overflow itself no (about `2^59` cycles).
- No GoogleTest case in this series yet.

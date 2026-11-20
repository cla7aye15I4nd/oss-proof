# Skip buffered output covered by a pending seek in gzdirect()

Status: tests and upstream-style commit message pending

## Problem

`gzgetc` (the function and the `gzgetc()` macro of `zlib.h`, which cannot be changed) takes bytes from the output buffer without checking for a skip request, which is only right while a pending skip implies an empty output buffer. `gzdirect` after `gzseek` broke that: `gzgetc` returned bytes from before the position sought and added them to `x.pos`, so `gztell` computed `x.pos + skip` past `GZ_OFF_MAX` (signed overflow, ISO C17 §6.5p5). The fix is in `gzdirect` because it is the one caller of `gz_look` that leaves output buffered without doing the pending skip (`gzungetc` calls `gz_skip` after `gz_look`, and the readers call `gz_skip` first).

## Fix

Files: `gzread.c`.

When `gzdirect` has called `gz_look` and a seek is pending (`skip != 0`) while `gz_look` left output (`x.have != 0`), it skips the buffered bytes the seek covers, as `gzseek` and `gz_skip` do: `n = min(x.have, skip)`, then `x.have -= n`, `x.next += n`, `x.pos += n`, `skip -= n`. Afterwards a pending skip again means no buffered output. It does no input or output of its own; the rest of the skip is done by the next read, as before.

## Related Upstream References

- Not yet submitted upstream. madler/zlib `b2596bde` does the same drain through a helper.

## Review Feedback Addressed

- None yet.

## Testing

- Reproduction in the project's regression suite: `gzdirect-pending-skip`.
- Confirmed on real C: yes (UndefinedBehaviorSanitizer, `gzlib.c:496`).
- No GoogleTest case in this series yet.

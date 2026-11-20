# Do not fetch in gzgets() while a skip is pending

Status: tests and upstream-style commit message pending

## Problem

`gz_skip` stops at the end of file with the skip still pending; `gzgets` then called `gz_fetch`, which in copy mode reads again after the end of file. On a file that grew meanwhile it returned bytes from before the position sought and added them to `x.pos` with the skip still pending, so `gztell` computed `x.pos + skip` past `GZ_OFF_MAX` (signed overflow, ISO C17 §6.5p5).

## Fix

Files: `gzread.c`.

`gzgets` calls `gz_fetch` only when no skip is pending (`state->x.have == 0 && state->skip == 0 && gz_fetch(state) == -1`). A skip is still pending after `gz_skip` only when it stopped at the end of the input with nothing buffered; `gzgets` then reports the end of file (`past = 1`, and `NULL` when nothing was copied), as `gz_read` does. Otherwise `gz_skip` has done the whole skip and nothing changes.

## Related Upstream References

- Not yet submitted upstream. madler/zlib `f40786e3` (TOB-ZLIB-006) changes `gz_skip()` at end of file as well.

## Review Feedback Addressed

- None yet.

## Testing

- Reproduction in the project's regression suite: `gzgets-pending-skip`.
- Confirmed on real C: yes (UndefinedBehaviorSanitizer, `gzlib.c:496`).
- No GoogleTest case in this series yet.

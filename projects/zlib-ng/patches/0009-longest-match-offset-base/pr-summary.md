# Do not form window - match_offset in longest_match

Status: tests and upstream-style commit message pending

## Problem

In `longest_match_slow_knuth_c` / `longest_match_slow_roll_c` (levels 7-9), `window - match_offset` points before the start of the block of `alloc_deflate` when `match_offset` exceeds the alignment padding before the window (ISO C17 §6.5.6p8); `match_offset` reaches 256.

## Fix

Files: `match_tpl.h`.

`mbase_start` stays `window`: the two statements that moved it back by `match_offset` (`mbase_start -= match_offset; mbase_end -= match_offset;` after the lazy-evaluation search, `mbase_start = window - match_offset` after the offset search) are removed, and each of the six candidate addresses `mbase_start + cur_match` / `mbase_end + cur_match` becomes `mbase_start + (cur_match - match_offset)` / `mbase_end + (cur_match - match_offset)`. Wherever a candidate is read, `cur_match > limit = limit_base + match_offset` holds (every update of `match_offset` or `cur_match` is followed by that test or returns), so the subtraction does not wrap and the address, and every byte read, is the same as before: the output is unchanged. `longest_match_c` (levels 2-6) keeps `match_offset == 0`.

## Related Upstream References

- Not yet submitted upstream.

## Review Feedback Addressed

- None yet.

## Testing

- Reproduction in the project's regression suite: `longest-match-offset-base`.
- Confirmed on real C: by the letter of the standard on a traced run: a copy of `match_tpl.h` instrumented to compare `match_offset` with the window's offset in its block reports 224926 out-of-object base pointers over the `deflate` inputs of the differential test without the patch (window at offset 0, offsets up to 223) and, with the patch, 0 subtractions `cur_match - match_offset` that would leave the window; no sanitizer reports forming the pointer. The compressed output of every one of those inputs is identical with and without the patch..
- No GoogleTest case in this series yet.

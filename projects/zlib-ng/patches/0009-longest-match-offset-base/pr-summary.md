# Do not form window - match_offset in longest_match

## Problem

In `longest_match_slow_knuth_c` / `longest_match_slow_roll_c` (levels 7-9), `mbase_start` and `mbase_end` were moved back by `match_offset` after the offset search. `window - match_offset` points before the start of the block of `alloc_deflate` when `match_offset` exceeds the alignment padding before the window (ISO C17 §6.5.6p8), although only `window + cur_match - match_offset` is ever read; `match_offset` reaches 256.

## Fix

Files: `match_tpl.h`.

`mbase_start` stays `window`: the two statements that moved it back by `match_offset` (`mbase_start -= match_offset; mbase_end -= match_offset;` after the lazy-evaluation search, `mbase_start = window - match_offset` after the offset search) are removed, and each of the six candidate addresses `mbase_start + cur_match` / `mbase_end + cur_match` becomes `mbase_start + (cur_match - match_offset)` / `mbase_end + (cur_match - match_offset)`. Wherever a candidate is read, `cur_match > limit = limit_base + match_offset` holds (every update of `match_offset` or `cur_match` is followed by that test or returns), so the subtraction does not wrap and the address, and every byte read, is the same as before: the output is unchanged. `longest_match_c` (levels 2-6) keeps `match_offset == 0`.

The series is one commit with the library change and one GoogleTest case.

## Related Upstream References

- Not yet submitted upstream. The code is zlib-ng's own (no madler/zlib counterpart).

## Review Feedback Addressed

- None yet (not submitted).

## Testing

- `deflate.slow_match_offset_round_trip` (new, `test/test_deflate.cc`): one 70000-byte input of random, text, periodic and zero runs, compressed at levels 7, 8 and 9 (`Z_FILTERED`, memLevel 4) and decoded back. An instrumented build counted about 16000 calls with `match_offset > 0` in each of the knuth (levels 7, 8) and the roll (level 9) matcher on this input, offsets up to 223; the existing round-trip tests of `test_deflate.cc` use level 9 only, so they never run the knuth matcher. The test passes with and without the change (`gtest.txt`: `no`): forming a pointer outside its object without dereferencing it is not reported by AddressSanitizer or UndefinedBehaviorSanitizer. It guards that the rewritten candidate addresses read the same bytes (a wrong address gives a wrong match and a stream that does not decode to the input).
- Reproduction in the project's regression suite: `longest-match-offset-base` (by the letter of the standard: an instrumented copy of `match_tpl.h` counts the out-of-object base pointers without the patch and finds none with it; the compressed output of every differential-test input is identical with and without the patch).

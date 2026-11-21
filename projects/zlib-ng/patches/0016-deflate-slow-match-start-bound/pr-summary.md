# Reject matches in deflate_slow() that do not start before strstart

## Problem

After `Z_FULL_FLUSH` with all input consumed (or `deflateReset`), `strstart` restarts at 0 and `head` is cleared but `prev` keeps positions of the earlier input; levels 2-6 leave the `prev` slots of positions they do not insert, and `deflateParams` to level 7 or 8 does not rebuild the chains. The offset search of `longest_match_slow_knuth_c` reads such slots, and its chain walk does not test `cur_match >= strstart` after each step, so it accepts a stale position ahead of `strstart`. `deflate_slow` then tallies a wrapped distance: `d_code` reads far outside `dist_code` (ISO C17 §6.5.6p8) and the output decodes to wrong data.

## Fix

Files: `deflate_slow.c`.

After `longest_match`, `deflate_slow` treats a match whose start is not before `strstart` (`s->match_start >= s->strstart`) as no match, as it already treats a match of at most `match_discard` bytes; `deflate_medium`'s `find_best_match` rejects the same case. A match accepted from a chain that holds only earlier positions starts before `strstart`, so nothing else changes.

The series is one commit with the library change and two GoogleTest cases.

## Related Upstream References

- Not yet submitted upstream. The code is zlib-ng's own (no madler/zlib counterpart).
- An earlier draft of this series cleared `prev` in `CLEAR_HASH` instead (a `memset` of `w_size` entries wherever `head` is cleared). That removes the stale entries at their source, but it costs a 64 KiB clear per reset, flush and parameter change at windowBits 15, and whether every path that leaves a forward entry in `prev` is covered was not established. The local test in `deflate_slow` is the form proved here; the tests below fail without it and pass with it.

## Review Feedback Addressed

- None yet (not submitted).

## Testing

- `deflate.changes_level_after_full_flush` and `deflate.changes_level_after_reset` (new, `test/test_deflate_params.cc`): one raw stream at level 2-6 on a first input, then `Z_FULL_FLUSH` (or `deflate` and `deflateReset`), part of a second input at that level, `deflateParams` to level 7 or 8, and the rest with `Z_FINISH`; the stream must decode to the input (inputs generated from fixed seeds, as in the regression case). Without the change both fail under AddressSanitizer (`SEGV` on a wild read in `zng_tr_tally_dist`, `deflate_p.h`, called from `deflate_slow`); with it both pass. Observed with `tests/patch-gtest.sh`.
- Reproduction in the project's regression suite: `deflate-slow-match-start` (also a round-trip mismatch without a sanitizer).

# Reject matches in deflate_slow() that do not start before strstart

Status: tests and upstream-style commit message pending

## Problem

After `Z_FULL_FLUSH` with all input consumed (or `deflateReset`), `strstart` restarts at 0 and `head` is cleared but `prev` keeps positions of the earlier input; levels 2-6 leave the `prev` slots of positions they do not insert, and `deflateParams` to level 7 or 8 does not rebuild the chains. The offset search of `longest_match_slow_knuth_c` reads such slots, and its chain walk does not test `cur_match >= strstart` after each step, so it accepts a stale position ahead of `strstart`. `deflate_slow` then tallies a wrapped distance: `d_code` reads far outside `dist_code` (ISO C17 §6.5.6p8) and the output decodes to wrong data.

## Fix

Files: `deflate_slow.c`.

After `longest_match`, `deflate_slow` treats a match whose start is not before `strstart` (`s->match_start >= s->strstart`) as no match, as it already treats a match of at most `match_discard` bytes; `deflate_medium`'s `find_best_match` rejects the same case. A match accepted from a chain that holds only earlier positions starts before `strstart`, so nothing else changes.

## Related Upstream References

- Not yet submitted upstream.

## Review Feedback Addressed

- None yet.

## Testing

- Reproduction in the project's regression suite: `deflate-slow-match-start`.
- Confirmed on real C: yes (AddressSanitizer, `deflate_p.h:101`; a round-trip mismatch without a sanitizer).
- No GoogleTest case in this series yet.

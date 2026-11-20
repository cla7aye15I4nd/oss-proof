# Bound the insert count of deflate_medium() to STD_MAX_MATCH

Status: tests and upstream-style commit message pending

## Problem

`max_insert_count` is `max_lazy_match`, which `deflateTune` stores as given. For `max_lazy = INT_MIN`, `max_len = 2 * max_insert_count` wraps to 0 and a match at distance 1 leaves one position to insert: `insert_knuth_stepped` divides by `inserts - 1 = 0` (ISO C17 §6.5.5p5; `SIGFPE` on x86_64).

## Fix

Files: `deflate_medium_tpl.h`.

`deflate_medium` bounds its insert count: `max_insert_count = MIN(MAX(2, s->max_insert_count), STD_MAX_MATCH)`. For a count above 258 every match (at most 258 bytes) was already inserted position by position, by `insert_knuth_batch` or by `insert_knuth_stepped` stepping by one, so the output is unchanged except where the C divided by zero.

## Related Upstream References

- Not yet submitted upstream.

## Review Feedback Addressed

- None yet.

## Testing

- Reproduction in the project's regression suite: `deflate-medium-insert-count`.
- Confirmed on real C: yes (UndefinedBehaviorSanitizer division by zero, `insert_string_p.h:186`).
- No GoogleTest case in this series yet.

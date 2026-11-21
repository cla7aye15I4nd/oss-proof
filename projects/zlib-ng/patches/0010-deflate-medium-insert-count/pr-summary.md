# Bound the insert count of deflate_medium() to STD_MAX_MATCH

## Problem

`max_insert_count` is `max_lazy_match`, which `deflateTune` stores as given. For `max_lazy = INT_MIN`, `max_len = 2 * max_insert_count` in `insert_match` wraps to 0, and a match at distance 1 reaches `insert_knuth_stepped` with one position to insert: it divides by `inserts - 1 = 0` (ISO C17 §6.5.5p5; `SIGFPE` on x86_64).

## Fix

Files: `deflate_medium_tpl.h`.

`deflate_medium` bounds its insert count: `max_insert_count = MIN(MAX(2, s->max_insert_count), STD_MAX_MATCH)`. For a count above 258 every match (at most 258 bytes) was already inserted position by position, by `insert_knuth_batch` or by `insert_knuth_stepped` stepping by one, so the output is unchanged except where the C divided by zero.

`deflate_fast` is not changed: no defect is known there (an earlier draft of this series also clamped its `max_inserts`; that is hardening only and is not part of this fix).

The series is one commit with the library change and one GoogleTest case.

## Related Upstream References

- Not yet submitted upstream. https://github.com/zlib-ng/zlib-ng/pull/2509 (merged before the pinned commit) introduced the lower bound `MAX(2, s->max_insert_count)`; the upper bound has no upstream counterpart.

## Review Feedback Addressed

- None yet (not submitted).

## Testing

- `deflate.tune_insert_count` (new, `test/test_deflate_tune.cc`): 4096 bytes of `a` at levels 3 to 6 (`deflate_medium` and `deflate_medium_fizzle`) after `deflateTune` with `max_lazy` in {`INT32_MIN`, -1, 0, 1, 258, 259, 100000}; each stream must decode to the input. Without the change UndefinedBehaviorSanitizer reports a division by zero (`insert_string_p.h`, `insert_knuth_stepped_static`); with it all cases pass. Observed with `tests/patch-gtest.sh`.
- Reproduction in the project's regression suite: `deflate-medium-insert-count`.

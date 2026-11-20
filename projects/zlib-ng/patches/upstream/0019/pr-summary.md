# PR 0019: Clear `prev[]` in `CLEAR_HASH()` to prevent stale forward matches

- **Proposed PR Title**: `Clear prev[] in CLEAR_HASH() to prevent stale forward matches`
- **Target Base**: `zlib-ng/zlib-ng` `develop` (`5f1f4899`)
- **Upstream PR**: Ready to submit (upgraded from `deflate_slow.c` symptom band-aid to root-cause `CLEAR_HASH(s)`)
- **Commits**: 1 (`upstream.patch`)
- **Files**: `deflate.c`, `test/test_deflate_params.cc`

## Problem & Root Cause

`longest_match_slow()` reads `prev[]` slots for interior bytes inside matches (which is why `alloc_deflate()` initializes `prev` and `insert_skip()` clears skipped `prev` slots). However, levels 2–6 (`deflate_fast` / `deflate_medium`) leave interior `prev` slots unpopulated. When `Z_FULL_FLUSH`, `deflateReset()`, or `deflateSetDictionary()` calls `CLEAR_HASH(s)` and resets `strstart` back to `0`, previously clearing *only* `s->head` left stale pre-reset positions `>= strstart` inside `s->prev`.

Subsequently switching to `deflate_slow` (levels 7–9 via `deflateParams()`) without rebuilding chains follows a stale `prev[]` link with `cur_match >= strstart`, causing a wrapped backward distance passed to `zng_tr_tally_dist()` (`dist_code` out-of-bounds read under ASan and corrupt compressed output without a sanitizer).

## Fix Summary

Clear `s->prev` alongside `s->head` inside `CLEAR_HASH(s)` in `deflate.c`:

```c
#define CLEAR_HASH(s) do { \
    memset((unsigned char *)s->head, 0, HASH_SIZE * sizeof(*s->head)); \
    memset((unsigned char *)s->prev, 0, (s)->w_size * sizeof(*(s)->prev)); \
  } while (0)
```

This fixes `Z_FULL_FLUSH`, `deflateReset()`, `deflateReset2()`, and `deflateSetDictionary()` at the source with zero hot-path overhead inside `deflate_slow()`. Add `deflate.changes_level_after_full_flush` (seed 362) and `deflate.changes_level_after_reset` (seed 303) in `test/test_deflate_params.cc`.

## Overlaps & Dependencies

- **Internal (`deflate.c`)**: completely disjoint from `0006`, `0018`, and `deflate-reset-block-open`. Note that `deflate.c`'s sibling proof patch `0019-deflate-slow-match-start-bound.patch` patched `deflate_slow.c`, whereas clearing `s->prev` in `CLEAR_HASH(s)` eliminates the root cause for all matchers with no inner-loop check.

## Verification

- Stress-checked on native AVX2 ASan+UBSan with `ZLIB_DEBUG` `Assert(match_len < STD_MIN_MATCH || s->match_start < s->strstart)` enabled across 2,000 random seeds × 2 modes (`Z_FULL_FLUSH`, `deflateReset`) and 1,000 targeted generator seeds × 2 modes with zero assertion or sanitizer failures.
- `build-compat-san` & `build-native-san`:
  - Before fix (`5f1f4899`): both `deflate.changes_level_after_full_flush` and `deflate.changes_level_after_reset` fail (`AddressSanitizer: global-buffer-overflow` in `dist_code` / round-trip mismatch).
  - After fix: both pass (`[  PASSED  ] 2 tests.`).

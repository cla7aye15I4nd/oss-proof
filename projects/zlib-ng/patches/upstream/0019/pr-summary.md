# Clear prev[] in CLEAR_HASH() to prevent stale forward matches

## Problem

`longest_match_slow()` reads `prev[]` entries for interior positions inside matches (which is why `alloc_deflate()` zero-initializes `prev` and `insert_skip()` clears skipped `prev` slots). However, levels 2–6 (`deflate_fast` / `deflate_medium`) leave interior `prev` slots unpopulated. When `Z_FULL_FLUSH`, `deflateReset()`, or `deflateSetDictionary()` calls `CLEAR_HASH(s)` and resets `strstart` back to `0`, clearing only `s->head` leaves stale pre-reset positions `>= strstart` inside `s->prev`.

If the caller subsequently switches to `deflate_slow` (levels 7–9 via `deflateParams()`), `longest_match_slow()` can follow a stale `prev[]` slot ahead of `strstart`, causing `deflate_slow()` to pass a wrapped backward distance to `zng_tr_tally_dist()` (out-of-bounds read on `dist_code` under AddressSanitizer and corrupted output without a sanitizer).

## Fix

Zero `s->prev` alongside `s->head` inside `CLEAR_HASH(s)` in `deflate.c`:

```c
#define CLEAR_HASH(s) do { \
    memset((unsigned char *)s->head, 0, HASH_SIZE * sizeof(*s->head)); \
    memset((unsigned char *)s->prev, 0, (s)->w_size * sizeof(*(s)->prev)); \
  } while (0)
```

This eliminates stale `prev[]` links across `Z_FULL_FLUSH`, `deflateReset()`, `deflateReset2()`, and `deflateSetDictionary()` at the source with zero hot-path overhead in `deflate_slow()`.

Add `deflate.changes_level_after_full_flush` and `deflate.changes_level_after_reset` in `test/test_deflate_params.cc`.

## Testing

- Clang (`ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, ASan + UBSan) and Clang (`ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`, ASan + UBSan):
  - Before fix: both `deflate.changes_level_after_full_flush` and `deflate.changes_level_after_reset` abort with AddressSanitizer `global-buffer-overflow` in `dist_code` (and produce round-trip mismatches without sanitizers).
  - After fix: both tests pass in both builds.
- Stress-tested on native AVX2 ASan + UBSan with `ZLIB_DEBUG` enabled across 2,000 random seeds × 2 modes (`Z_FULL_FLUSH` and `deflateReset`) plus 1,000 targeted seeds × 2 modes with zero assertion or sanitizer failures.

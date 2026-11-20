# Bound max_insert_count in deflate_medium and deflate_fast

## Problem

`deflateTune()` stores caller-supplied `max_lazy` (`int32_t`) directly in `s->max_insert_count`. Both `deflate_medium_tpl.h` and `deflate_fast.c` only clamp the lower bound (`MAX(2, s->max_insert_count)`), whereas `insert_knuth_stepped_static()` expects an insert count in `[2, STD_MAX_MATCH]`. Passing `max_lazy = INT32_MIN` wraps `2 * max_insert_count` to `0` in 32-bit unsigned arithmetic, leaving a single position to insert on a distance-1 match and triggering integer division by zero (`inserts - 1 == 0`) in `insert_string_p.h` (ISO C17 §6.5.5p5 / `SIGFPE`).

## Fix

Clamp the insert count in unsigned arithmetic to `[2U, STD_MAX_MATCH]` in both `deflate_medium_tpl.h` and `deflate_fast.c`:

- `MIN(MAX(2U, s->max_insert_count), STD_MAX_MATCH)`

Add `deflate.tune_stepped_insert_count` in `test/test_deflate_tune.cc` testing compression levels `2`, `4`, and `6` across `max_lazy` values `{INT32_MIN, 0, 1, 258, 100000}`.

## Testing

- Clang (`ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, ASan + UBSan) and Clang (`ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`, ASan + UBSan):
  - Before fix: `deflate.tune_stepped_insert_count` aborts with UBSan integer division by zero in `insert_string_p.h`.
  - After fix: passes in both builds.

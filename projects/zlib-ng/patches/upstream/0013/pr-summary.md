# PR 0013: Bound `max_insert_count` in `deflate_medium` and `deflate_fast`

- **Proposed PR Title**: `Bound max_insert_count in deflate_medium and deflate_fast`
- **Target Base**: `zlib-ng/zlib-ng` `develop` (`5f1f4899`)
- **Upstream PR**: Ready to submit
- **Commits**: 1 (`upstream.patch`)
- **Files**: `deflate_fast.c`, `deflate_medium_tpl.h`, `test/test_deflate_tune.cc`

## Problem & Root Cause

`deflateTune()` stores caller-supplied `max_lazy_match` (`int32_t`) directly in `s->max_insert_count`. Both `deflate_medium_tpl.h` and `deflate_fast.c` only clamp the lower bound (`MAX(2, s->max_insert_count)`), assuming `max_insert_count <= STD_MAX_MATCH` (`258`). Passing `max_lazy = INT32_MIN` (which `MAX(2, ...)` compares in signed `int32_t` or wraps with large values like `0x80000000` / large unsigned counts):
- wraps `2 * max_insert_count` or passes `count > 258` into `insert_knuth_stepped_static()`;
- causes integer division by zero (`inserts - 1 == 0`) inside `insert_string_p.h` (`SIGFPE` / UBSan) on `deflate_medium` repetitive input.

## Fix Summary

Clamp both lower and upper bounds to `[2, STD_MAX_MATCH]` (`unsigned` comparison) in both `deflate_medium_tpl.h` and `deflate_fast.c`:

- `MIN(MAX(2U, s->max_insert_count), STD_MAX_MATCH)`

Add `deflate.tune_stepped_insert_count` in `test/test_deflate_tune.cc` exercising `level in {2, 4, 6}` across `max_lazy in {INT32_MIN, 0, 1, 258, 100000}` with `PREFIX(uncompress)` (`z_uintmax_t`).

## Overlaps & Dependencies

- Independent (`deflate_fast.c`, `deflate_medium_tpl.h`, and `test/test_deflate_tune.cc` are untouched by all other series).

## Verification

- `build-compat-san` & `build-native-san`:
  - Before fix (`5f1f4899`): `deflate.tune_stepped_insert_count` fails under UBSan (`division by zero` at `insert_string_p.h`).
  - After fix: passes on both (`[  PASSED  ] 1 test.`).

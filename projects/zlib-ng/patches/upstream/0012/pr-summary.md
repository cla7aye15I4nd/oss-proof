# PR 0012: Keep `longest_match` candidate bases within the deflate window

- **Proposed PR Title**: `Keep longest_match candidate bases within the deflate window`
- **Target Base**: `zlib-ng/zlib-ng` `develop` (`5f1f4899`)
- **Upstream PR**: Ready to submit
- **Commits**: 1 (`upstream.patch`)
- **Files**: `match_tpl.h`, `test/test_deflate.cc`

## Problem & Root Cause

In `match_tpl.h` (`LONGEST_MATCH_SLOW`), the offset-search loop shifts `mbase_start` and `mbase_end` below the start of `window`:

```c
mbase_start -= match_offset;
mbase_end -= match_offset;
```

Even though `cur_match > limit = limit_base + match_offset` ensures every dereference `mbase_start + cur_match` lands back inside `window`, forming `window - match_offset` itself constructs an out-of-bounds pointer before the allocation (ISO C17 §6.5.6p8).

## Fix Summary

Keep `mbase_start` fixed at `window` (and `mbase_end = mbase_start + offset`), and apply `match_offset` at the index expression via a template macro:

```c
#ifdef LONGEST_MATCH_SLOW
#  define MATCH_POS(m) ((m) - match_offset)
#else
#  define MATCH_POS(m) (m)
#endif
```

For non-slow matchers (`LONGEST_MATCH_SLOW` undefined), `MATCH_POS(cur_match)` expands directly to `cur_match` with zero extra instructions or unused `match_offset` references. Add `deflate.slow_match_offset_round_trip` in `test/test_deflate.cc`.

## Draft Cleanup

- Fixed compile failure when `#ifndef LONGEST_MATCH_SLOW` by parameterizing `MATCH_POS(m)` instead of referencing `match_offset` unconditionally.
- Moved the regression test from `test/test_deflate_tune.cc` to `test/test_deflate.cc` to eliminate merge conflicts with `0013`.
- Used `PREFIX(uncompress)` with `z_uintmax_t` so the test compiles cleanly under both `ZLIB_COMPAT=ON` and `ZLIB_COMPAT=OFF`.

## Overlaps & Dependencies

- Independent (`match_tpl.h` and `test/test_deflate.cc` are untouched by all other series).

## Verification

- `build-compat-san` & `build-native-san`:
  - `deflate.slow_match_offset_round_trip` passes on both builds (`[  PASSED  ] 1 test.`).
  - Forming an out-of-object base pointer without dereferencing is ISO C17 §6.5.6p8 UB that Clang runtime sanitizers do not flag, so verification combines source-level C17 inspection with round-trip regression testing.

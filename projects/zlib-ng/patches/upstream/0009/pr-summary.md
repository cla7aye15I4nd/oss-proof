# Tracker 0009: `inflateSetDictionary()` with `NULL` dictionary (Covered Upstream by PR #2516)

- **Local Proof Patch**: `0009-inflatesetdictionary-null.patch`
- **Upstream PR**: https://github.com/zlib-ng/zlib-ng/pull/2516 (`Test inflate api errors` by `Dead2`, open)
- **Action**: **Do not submit a duplicate PR.** Keep this 0-commit tracker until `#2516` lands and the upstream pin moves past it.

## Context

`inflateSetDictionary(strm, NULL, 0)` on a raw inflate stream previously bypassed the NULL-dictionary check and evaluated `NULL + 0`, `NULL - 0`, and `memcpy(..., NULL, 0)` (ISO C17 §6.5.6p8, §7.24.1p2), returning `Z_OK` instead of `Z_STREAM_ERROR`. Open upstream PR `#2516` already addresses this path and adds `inflate` API error tests.

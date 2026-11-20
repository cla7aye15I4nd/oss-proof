# Keep longest_match candidate bases within the deflate window

## Problem

In `match_tpl.h` (`LONGEST_MATCH_SLOW`), the offset-search loop shifts `mbase_start` and `mbase_end` backwards by `match_offset`:

```c
mbase_start -= match_offset;
mbase_end -= match_offset;
```

Although `cur_match > limit = limit_base + match_offset` guarantees every dereference `mbase_start + cur_match` lands back inside `window`, forming `window - match_offset` itself produces an out-of-bounds pointer before the allocated object when `match_offset` exceeds the alignment padding before `window` (ISO C17 §6.5.6p8).

## Fix

Keep `mbase_start` anchored at `window` (and `mbase_end = mbase_start + offset`), applying `match_offset` at the index expression through a template macro:

```c
#ifdef LONGEST_MATCH_SLOW
#  define MATCH_POS(m) ((m) - match_offset)
#else
#  define MATCH_POS(m) (m)
#endif
```

For non-slow matchers (`LONGEST_MATCH_SLOW` undefined), `MATCH_POS(cur_match)` expands directly to `cur_match` with no extra arithmetic. Add `deflate.slow_match_offset_round_trip` in `test/test_deflate.cc`.

## Testing

- Clang (`ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, ASan + UBSan + C pointer-pair) and Clang (`ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`, ASan + UBSan): `deflate.slow_match_offset_round_trip` passes in both builds (forming an out-of-object pointer without dereferencing is not reported by C runtime sanitizers; verified by ISO C17 §6.5.6p8 source inspection and round-trip testing).

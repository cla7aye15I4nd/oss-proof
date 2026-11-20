# Tracker 0010: `inflate_fast()` with `>= 8` primed bits (Covered Upstream by PR #2526)

- **Local Proof Patch**: `0010-inflate-fast-primed-bits.patch`
- **Upstream PR**: https://github.com/zlib-ng/zlib-ng/pull/2526 (`Keep primed inflate streams off the fast path` by `arfa-21`, open)
- **Action**: **Do not submit a duplicate PR.** Keep this 0-commit tracker until `#2526` lands and the upstream pin moves past it.

## Context

When `inflatePrime()` leaves `>= 8` bits in `state->bits`, `inflate_fast()` decrements `in -= (state->bits >> 3)` on exit past the start of the caller's input buffer (`next_in` moves before buffer start, ISO C17 §6.5.6p8, while `avail_in` grows and `total_in` wraps). Open upstream PR `#2526` already keeps primed streams off `inflate_fast()` and adds regression tests.

# Harden gzip extra copying when shared header state changes

## Problem

In `inflate()` (`EXTRA` state), copying the gzip `FEXTRA` payload computes:

```c
len = state->head->extra_len - state->length;
if (len < state->head->extra_max) {
    memcpy(state->head->extra + len, next,
           len + copy > state->head->extra_max ?
           state->head->extra_max - len : copy);
}
```

If two streams share one `gz_header` via `inflateCopy()` after the fixed 10-byte gzip header and the second stream parses a smaller `XLEN`, `state->head->extra_len < state->length` causes `uint32_t` underflow in `len` and wraparound in `len + copy`. Reaching an actual out-of-bounds write requires an impractical `extra_max` above about `2^32 - 65535`, so this is defense-in-depth hardening.

## Fix

In `inflate.c` (`EXTRA` state):

- Require `state->length <= state->head->extra_len` before subtracting.
- Compare `copy > state->head->extra_max - len` instead of `len + copy > state->head->extra_max`.

Add `inflate.shared_gzip_header_extra_bounds` in `test/test_inflate_copy.cc` using `inflateCopy()` after the fixed 10-byte gzip header with `uint8_t extra[16]` and `header.extra_max = UINT32_MAX` (once lengths disagree, no bytes are written to `extra`).

## Related Upstream References

- Updates open PR: https://github.com/zlib-ng/zlib-ng/pull/2528
- Note: https://github.com/zlib-ng/zlib-ng/pull/2404 also modifies `test/test_inflate_copy.cc`.

## Review Feedback Addressed

- Squashed into a single commit with a clear commit message stating this is hardening only and noting the `extra_max > ~2^32 - 65535` condition.
- Replaced the opt-in 4 GiB test with an always-on `inflateCopy()` test using `uint8_t extra[16]` and `header.extra_max = UINT32_MAX` (matching inline review feedback).
- Removed standalone C reproducer files, verbose comments, and any out-of-contract `inflateGetHeader()` usage after `inflate()` has started.

## Testing

- Clang (`ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, ASan + UBSan) and Clang (`ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`, ASan + UBSan):
  - Before fix: `inflate.shared_gzip_header_extra_bounds` crashes under AddressSanitizer.
  - After fix: passes in both builds (and verified separately with a 4 GiB `extra_max = 0xfffffff0U` allocation under ASan).

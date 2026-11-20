# Mask the gzip extra length in deflateBound()

Status: tests and upstream-style commit message pending

## Problem

`2 + extra_len` is computed in 32-bit `unsigned` and wraps for `extra_len >= 0xfffffffe`, so the bound is below what one `deflate(Z_FINISH)` writes, against the promise of `zlib.h`. Not undefined behaviour.

## Fix

Files: `deflate.c`.

`deflateBound` adds `2 + (extra_len & 0xffff)` for a user gzip header with an extra field.

## Related Upstream References

- Open zlib-ng PR https://github.com/zlib-ng/zlib-ng/pull/2523 carries the same fix written without the `(z_size_t)` cast.
- Related madler/zlib PR: https://github.com/madler/zlib/pull/1360 (open).

## Review Feedback Addressed

- None yet.

## Testing

- Reproduction in the project's regression suite: `deflatebound-gzip-extra-length`.
- Confirmed on real C: yes (`deflate` does not return `Z_STREAM_END`).
- No GoogleTest case in this series yet.

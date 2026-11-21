# Advance next_in in inflateSync() only when input was consumed

## Problem

`inflateSync` may be called with no input (`next_in == NULL`, `avail_in == 0`) when at least 8 bits are held, for example after `inflatePrime`. It then searches only the held bits, `syncsearch` consumes nothing, and `strm->next_in += 0` is `NULL + 0` (ISO C17 §6.5.6p8).

## Fix

Files: `inflate.c`.

`inflateSync` advances `next_in` only when `syncsearch` consumed bytes (`if (len) strm->next_in += len;`). `avail_in` and `total_in` are updated as before; with `len == 0` neither changes, so the result is the same.

The series is one commit with the library change and one GoogleTest case.

## Related Upstream References

- Not yet submitted upstream.
- https://github.com/zlib-ng/zlib-ng/pull/2510 (merged before the pinned commit) ported other `inflateSync` fixes; madler/zlib `develop` still has `strm->next_in += len`.

## Review Feedback Addressed

- None yet (not submitted).

## Testing

- `inflate.sync_primed_bits_without_input` (new, `test/test_inflate_sync.cc`): `inflateSync` on a raw stream with primed bits and no input, once without a sync pattern (`Z_DATA_ERROR`) and once with the whole `00 00 ff ff` pattern in the primed bits (`Z_OK`); `next_in` stays `NULL`, `avail_in` and `total_in` stay 0. It passes with and without the change (`gtest.txt`: `no`): adding 0 to a null pointer is not reported by AddressSanitizer or UndefinedBehaviorSanitizer (clang 21 checked on a minimal C program). The test guards the path and its results.
- Reproduction in the project's regression suite: `inflatesync-null-next-in` (by the letter of the standard on a traced run).

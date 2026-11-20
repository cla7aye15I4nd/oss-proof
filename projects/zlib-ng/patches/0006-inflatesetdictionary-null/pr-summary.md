# Reject a NULL dictionary in inflateSetDictionary()

Status: tests and upstream-style commit message pending

## Problem

`inflateSetDictionary(strm, NULL, 0)` on a raw stream computes `NULL + 0`, `NULL - 0` and calls `memcpy` from `NULL` (ISO C17 §6.5.6p8, §7.24.1p2), and returns `Z_OK`.

## Fix

Files: `inflate.c`.

`inflateSetDictionary` returns `Z_STREAM_ERROR` for a `NULL` dictionary, as `zlib.h` documents, before any other step.

## Related Upstream References

- Covered by open zlib-ng PR https://github.com/zlib-ng/zlib-ng/pull/2516 (another contributor), which adds the same `NULL` check; no separate PR is planned.

## Review Feedback Addressed

- None yet.

## Testing

- Reproduction in the project's regression suite: `inflatesetdictionary-null`.
- Confirmed on real C: yes (UndefinedBehaviorSanitizer: null pointer passed as `memcpy`'s source, `inflate.c:361`, with GCC and clang on glibc; the return value differs: `Z_OK` vs `Z_STREAM_ERROR`); `NULL + 0` and `NULL - 0` by the letter of the standard.
- No GoogleTest case in this series yet.

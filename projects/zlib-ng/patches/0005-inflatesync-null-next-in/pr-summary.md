# Advance next_in in inflateSync() only when input was consumed

Status: tests and upstream-style commit message pending

## Problem

With `next_in == NULL`, `avail_in == 0` and at least 8 primed bits, `strm->next_in += 0` is `NULL + 0` (ISO C17 §6.5.6p8).

## Fix

Files: `inflate.c`.

`inflateSync` advances `next_in` only when `syncsearch` consumed bytes.

## Related Upstream References

- Not yet submitted upstream.

## Review Feedback Addressed

- None yet.

## Testing

- Reproduction in the project's regression suite: `inflatesync-null-next-in`.
- Confirmed on real C: by the letter of the standard on a traced run (no sanitizer reports `NULL + 0` in C).
- No GoogleTest case in this series yet.

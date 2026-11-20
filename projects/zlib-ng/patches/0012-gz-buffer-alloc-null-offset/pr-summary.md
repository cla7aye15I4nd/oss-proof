# Test the allocation in gz_buffer_alloc() before offsetting it

Status: tests and upstream-style commit message pending

## Problem

When the allocation failed, `state->buffers + in_size` was `NULL` plus a nonzero offset (ISO C17 §6.5.6p8).

## Fix

Files: `gzlib.c`.

`gz_buffer_alloc` tests the allocation (`state->in == NULL`) before it computes `state->out = state->buffers + in_size`; the second half of the old test (`out_size && state->out == NULL`) is dropped, as it is false whenever the allocation succeeded.

## Related Upstream References

- Not yet submitted upstream.

## Review Feedback Addressed

- None yet.

## Testing

- Reproduction in the project's regression suite: `gzbuffer-alloc-null-offset`.
- Confirmed on real C: yes (clang's UndefinedBehaviorSanitizer; GCC's does not report `NULL` plus an offset).
- No GoogleTest case in this series yet.

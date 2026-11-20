# Move leftover input to the buffer start before gzvprintf() formats

Status: tests and upstream-style commit message pending

## Problem

A `gz_comp` whose `write()` fails returns with `next_in` moved forward and input left. `gzvprintf` (after `gzclearerr`) then set `avail_in = size` from that `next_in`, so `next_in + avail_in` passed `in + size` and moved on with each failed round: the formatted text overwrote compressed data not yet written in the output buffer, then `vsnprintf` and `next[size - 1] = 0` wrote past the buffer block (ISO C17 §7.22.3, §6.5.6p8). Upstream zlib fixed the same code in its `develop` branch in 2026 (`gz_vacate`, which moves the leftover input to the start of the buffer).

## Fix

Files: `gzwrite.c`.

Before formatting, `gzvprintf` moves input left in the buffer to its start: when `avail_in != 0` and `next_in != state->in`, `memmove(state->in, strm->next_in, strm->avail_in)` and `next_in = state->in`. Afterwards `next_in + avail_in <= in + size` holds again whenever `gzvprintf` formats, so the `size` bytes it counts from `next_in` lie in the first half of the buffer, as the code's comment assumes, and the `memmove(state->in, state->in + state->size, left)` after a successful `gz_comp` moves the right bytes. When there is no leftover input, or it already starts at `in`, nothing changes. The other writers (`gz_write`, `gzputc`, `gz_zero`) only add input up to `in + size` and are unchanged.

## Related Upstream References

- Not yet submitted upstream. madler/zlib fixed the same code on its `develop` branch (`gz_vacate`).

## Review Feedback Addressed

- None yet.

## Testing

- Reproduction in the project's regression suite: `gzprintf-failed-write-drift`.
- Confirmed on real C: yes, through documented calls only (AddressSanitizer heap buffer overflow in `gzvprintf`; the stream damaged when the program stops before that call).
- No GoogleTest case in this series yet.

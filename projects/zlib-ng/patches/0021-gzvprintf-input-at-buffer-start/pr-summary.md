# Move leftover input to the buffer start before gzvprintf() formats

## Problem

`gzvprintf()` (`gzwrite.c`) formats at `next_in + avail_in` and, when the input reaches `state->size`, compresses `state->size` bytes from `next_in` and moves the rest from `state->in + state->size` to the start. It relies on `next_in + avail_in <= state->in + state->size` ("the input buffer is double-sized just for this function"). A `gz_comp()` whose `write()` fails returns with `next_in` moved forward (`deflate()` consumed part of the input) and input left. After `gzclearerr()`, the next `gzprintf()` counted `state->size` bytes from that `next_in`, so `next_in + avail_in` passed `in + size` and moved further with each failed round: the formatted text overwrote compressed data not yet written from the output buffer (a damaged gzip stream), and a round later `vsnprintf()` and `next[state->size - 1] = 0` wrote past the end of the buffer block (heap buffer overflow, ISO C17 §6.5.6p8). The failures are ordinary ones: a non-blocking descriptor that is full (`EAGAIN`).

## Fix

Before formatting, `gzvprintf()` moves input left in the buffer to its start: when `avail_in != 0` and `next_in != state->in`, `memmove(state->in, strm->next_in, strm->avail_in)` and `next_in = state->in`. Afterwards `next_in + avail_in <= in + size` holds whenever `gzvprintf()` formats, so the `size` bytes it counts lie in the first half of the buffer and the `memmove()` after a successful `gz_comp()` moves the right bytes. When there is no leftover input, or it already starts at `state->in`, nothing changes. The other writers (`gz_write()`, `gzputc()`, `gz_zero()`) only add input up to `in + size` and are unchanged.

madler/zlib does the same move in `gz_vacate()`, added with its support for non-blocking devices (`81cc0be`, in zlib 1.3.1.2; its pointer tests revised by `e3dc0a8` and `6be4bcda`). `gz_vacate()` also writes the input out first when it reaches into the second half, and reports a stall through `state->again`, which zlib-ng does not have. That code is not cherry-picked: it is part of the non-blocking rework, which zlib-ng has not taken, and the write it adds changes when `gzprintf()` writes, beyond this defect.

Add `gzip.printf_after_failed_writes` in `test/test_gzio.cc` (Linux only): a `"wb0"` writer with a 262144-byte buffer on a non-blocking pipe of 1 MiB whose room is set before each call (filled with whole pages and read back), so that each `write()` either completes or fails with `EAGAIN` without writing anything; `gzprintf()` rounds, some of whose writes fail, with `gzclearerr()` after each; then the pipe is drained, the file closed, and the gzip stream read back must inflate completely. It is skipped when the pipe cannot be set to 1 MiB.

## Related Upstream References

- madler/zlib `81cc0be` ("Support non-blocking devices in the gz* routines.", in zlib 1.3.1.2): `gz_vacate()`, described above.
- Note: https://github.com/zlib-ng/zlib-ng/pull/2517 (open) adds a `NULL` `format` check to `gzvprintf()`, unrelated.
- Not yet submitted to zlib-ng.

## Review Feedback Addressed

- None yet (not submitted).

## Testing

- Clang, `ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, `-O0`, AddressSanitizer + UndefinedBehaviorSanitizer, on Linux:
  - Before the fix: aborts with AddressSanitizer heap-buffer-overflow, a write by `vsnprintf()` called from `gzvprintf()` past the buffer block.
  - After the fix: passes; the stream inflates completely.
- Clang, `ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`, same sanitizers: passes.

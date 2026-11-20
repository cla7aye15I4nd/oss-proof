# Do not leave next_in pointing at the caller's buffer in gz_write()

Status: tests and upstream-style commit message pending

## Problem

One stale pointer: the direct path points `strm.next_in` at the caller's buffer and left it there, with `avail_in` nonzero after a failed `write`. After `gzclearerr`, a small write (`gz_write`, `gzputc`, `gzprintf`) computed `(next_in + avail_in) - state->in` across objects (ISO C17 §6.5.6p9) and copied past the end of `in`; `gzclose` (`gz_comp(state, Z_FINISH)`), `gzflush` and `gzsetparams` wrote or compressed `avail_in` bytes of the caller's buffer after `gzwrite` had returned (use after free when the caller freed it). Both findings of a failed `gzwrite` are fixed by this one patch.

## Fix

Files: `gzwrite.c`.

On the direct path of `gz_write` (a write of at least the buffer size, compressed or transparent), when `gz_comp` fails, `strm.avail_in` is set to 0 and `strm.next_in` to `state->in` before `gz_write` returns 0; after the direct path succeeds, `strm.next_in` is set to `state->in` (`avail_in` is already 0 there: the direct `write` cleared it, and `deflate` with room left in the output consumed all input). On every path without a failure the stream then holds what it held before except a `next_in` that no code reads while `avail_in` is 0.

## Related Upstream References

- Open zlib-ng PR https://github.com/zlib-ng/zlib-ng/pull/2527 contains these lines and more (madler/zlib `df84af25` and `6be4bcda`).

## Review Feedback Addressed

- None yet.

## Testing

- Reproductions in the project's regression suite: `gzwrite-clearerr-stale-input`, `gzclose-after-failed-write`.
- Confirmed on real C: yes (pointer-pair check / heap-buffer-overflow; heap-use-after-free).
- No GoogleTest case in this series yet.

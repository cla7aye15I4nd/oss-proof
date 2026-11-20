# Take each batch of zeros off skip before writing it in gz_zero()

Status: tests and upstream-style commit message pending

## Problem

`gz_zero` added a batch to `x.pos` and took it off `skip` only after the write succeeded. A failed write left the batch counted in both: `x.pos + skip` passed the position `gzseek` had returned (and `GZ_OFF_MAX`, which patch 0002 relies on). `gztell` then computed `x.pos + skip` with signed overflow (ISO C17 §6.5p5) after `gzseek(file, INT64_MAX, SEEK_SET)` and one failed write; with a smaller seek, `gzclearerr` and the write again wrote the batch twice, so the file and `gztell` were longer than the seek asked for.

## Fix

Files: `gzwrite.c`.

`gz_zero` takes each batch of zeros off `skip` when it adds the batch to `x.pos`, before `gz_comp` writes it, instead of after a successful write. When the write fails, the batch stays in the input buffer (`avail_in`), and the next `gz_zero` (after `gzclearerr`) or `gz_comp` writes it first, so the file gets exactly the zeros the seek asked for. On every path without a failure nothing changes.

## Related Upstream References

- Not yet submitted upstream. madler/zlib `51c7cd2c` changes the same function in a different order.

## Review Feedback Addressed

- None yet.

## Testing

- Reproduction in the project's regression suite: `gzwrite-zero-retry`.
- Confirmed on real C: yes, through documented calls only (UndefinedBehaviorSanitizer, `gzlib.c:496`; the repeated zeros: 14099 bytes written for a seek to 10000 and 3 bytes).
- No GoogleTest case in this series yet.

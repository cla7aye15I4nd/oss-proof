# Patches

The verified source is zlib 1.4 (upstream commit `99623ef7`) with the seven patches of this
directory applied in name order. Every theorem is about that patched source.

Each patch fixes an issue of zlib without whose fix a safety statement cannot be proved, or a
promise of `zlib.h` does not hold. Each is as small as the fix allows. A patch that was submitted
upstream is the submitted fix. [Findings](https://www.dataisland.org/zlib-f/en/findings.html)
lists the issues in one table, with the calls that reach each issue and the evidence.

## 0001-inflate-copy-pointer-equality.patch

`inflateCopy` compares a pointer into the static fixed-code table with a pointer into the state's
own code array using `>=` and `<=`, which C defines only for pointers into one object. The patch
tests the same condition with pointer equality. Without it the safety of `inflateCopy` cannot be
proved for every stream.

Upstream: the patch is the commit of [PR #1369](https://github.com/madler/zlib/pull/1369), which
the maintainer answered with "Applied". zlib 1.4 does not contain it.

## 0002-gzseek-negative-position-overflow.patch

An initial `gzungetc` sets `state->x.pos` to -1. `gzseek64` then overflows signed arithmetic: the
`SEEK_CUR` range check evaluates `GZ_OFF_MAX - pos` with a negative `pos`, and a `SEEK_SET`
target near `GZ_OFF_MAX` overflows in `pos - state->x.pos`. The patch evaluates the range check
only for a positive `pos` and refuses a seek whose displacement does not fit. Without it the
safety of `gzseek64` and `gzseek` cannot be proved.

Upstream: the patch is the `gzlib.c` part of
[PR #1361](https://github.com/madler/zlib/pull/1361), which is open.

## 0003-gzread-partial-copy-read-error.patch

In transparent (`COPY`) mode, when `read` supplies some bytes and then fails, `gz_load` leaves
the partial count in `x.have` and returns -1, and `gz_fetch` returns before its assignment of
`x.next`. The readers then take the partial bytes through a stale `x.next`, which can be outside
the output buffer. The patch sets `state->x.next = state->out` before `gz_load`. Without it the
safety of the gz reading calls cannot be proved.

Upstream: the patch is the change of [PR #1363](https://github.com/madler/zlib/pull/1363), which
is open.

## 0004-gz-position-overflow.patch

The gz readers and writers add to the signed position `state->x.pos` without a bound, so a read
or write at a position near `GZ_OFF_MAX` overflows it. The patch keeps the position within
`z_off64_t`. Reading: `gz_fetch` fills the output buffer only with bytes whose position is
representable (at least one, to find the end of the input), and `gz_read` and `gzgets` deliver no
byte past `GZ_OFF_MAX`; data beyond it gives `Z_DATA_ERROR` "position overflow". Writing:
`gz_write`, the fast path of `gzputc` and `gzprintf` refuse a write that would carry the position
past `GZ_OFF_MAX`, with the same error. Without the patch the safety of the gz readers and
writers cannot be proved.

The patch also bounds the transparent branch of `gz_look`. The `gzgetc()` macro of `zlib.h` does
`pos++` on any buffered byte with no check, so every reading call must return with
`x.pos + x.have <= GZ_OFF_MAX`. The transparent branch of `gz_look` buffers input too, so it
buffers only the room that is left and records the same error beyond it.

Upstream: local patch, not submitted.

## 0005-gz-next-zero-advance.patch

`gzseek64` and `gz_skip_have` do `state->x.next += n` also when `n` is zero. The field may then
never have been written (`gz_reset` does not set it), or may point into a caller buffer that was
freed after a direct `gzread`; arithmetic on either is undefined in C. The patch advances
`x.next` only when `n` is not zero. No result or state changes. The model faults on arithmetic
with a dangling pointer, so without the patch the gz reading calls cannot be proved safe. The
model does not see the never-written case: a pointer field in fresh memory is `NULL` there, and
`NULL + 0` passes. That case rests on the reading of the C and on the probe run.

Upstream: local patch, not submitted.

## 0006-deflatebound-fixed-conservative.patch

With `windowBits` 15, `memLevel` 8 and strategy `Z_FIXED`, `deflateBound` returns the tight
default bound, which counts on a stored block as the fallback of every block. A block that
crosses a window slide has none, and `deflate_fast` (levels 1 to 3) takes 3-byte matches at any
distance, which cost 25 bits with fixed codes. The output then exceeds the bound, and one
`deflate(Z_FINISH)` call with that room returns `Z_OK`, against the promise of `zlib.h`. The
patch makes `deflateBound_z` return a conservative bound also when the strategy is `Z_FIXED`
(`fixedlen` for levels 1 to 9, `storelen` for level 0, as for the other parameter sets), which
allows 9 bits per byte. No other strategy and no other parameter set changes. It fixes a broken
promise, not a memory error: no safety goal depends on the value of the bound.

Upstream: local patch, not submitted.

## 0007-gzoffset-negative-lseek.patch

`gzoffset64` takes `LSEEK(fd, 0, SEEK_CUR)`, refuses only -1, and when reading subtracts the
buffered input `state->strm.avail_in`. On Linux, `lseek` on a file with unsigned offsets
(`/proc/<pid>/mem`, `/dev/mem`) returns any 64-bit offset, negative ones included, and POSIX
allows negative offsets for some devices. A descriptor at a large negative offset then makes the
subtraction overflow `z_off64_t` (reproduction under
`tests/regression/gzoffset-negative-lseek/`). The patch returns -1 for every negative result of
`lseek`, as for a failure: a negative value is not a file offset. Without it the safety of
`gzoffset64` and `gzoffset` cannot be proved on every outside world.

Upstream: local patch, not submitted.

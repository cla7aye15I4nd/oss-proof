# gz: position overflow after a transparent look near `GZ_OFF_MAX`

This page says why this project's local [patch 0004](../../patches/README.md) also bounds the
transparent COPY branch of `gz_look`. It is about the patch, not about a further defect of upstream
zlib. Patch 0004 is the fix of [gzread-pos-overflow](gzread-pos-overflow/README.md). A fix that
bounds only `gz_fetch`, `gz_read` and `gzgets` leaves one path on which a reader can still overflow
the position. Patch 0004 closes that path.

Status: the overflow without the bound is confirmed in the model and by reading the C. It is not
reproduced under a sanitizer: the history needs about 2^63 decoded bytes. With patch 0004,
`gz_look`'s COPY branch buffers only `gz_room(state, avail_in)` bytes and records `Z_DATA_ERROR`
"position overflow" when the input goes past that. The patch is local and has not been submitted
upstream.

## What goes wrong without the bound

Patch 0004 keeps the position `state->x.pos` within `z_off64_t`. `gz_fetch` loads only what fits
before `GZ_OFF_MAX` (`gz_room`), and `gz_read` and `gzgets` drop buffered output once `x.pos` is
at `GZ_OFF_MAX`. The reader invariant needs more at each return: `x.pos + x.have <= GZ_OFF_MAX`,
because the `gzgetc()` macro of zlib.h does `(g)->pos++` on any buffered byte.

Suppose `gz_look`'s transparent COPY branch is not bounded. It copies all pending input to the
output buffer and sets `x.have = strm->avail_in`, up to `size` bytes, at any `x.pos`. The drop in
`gz_read` runs only on the next trip of its loop. So `gz_read` can return with
`x.pos + x.have > GZ_OFF_MAX`. The same holds through `gz_skip` (`gz_skip_have` takes only
`min(have, skip)`) and through `gzdirect` (it calls `gz_look` and returns).

`gz_look` takes the COPY branch after the start only in one history:
`tests/verification/regressions/gz-copy-direct.c` shows it in the real C. A gzip member is
followed by data that is not gzip; `gz_decomp` treats it as trailing garbage (`junk == 1`) and
sets `eof`; `gzclearerr` clears `eof`; the next read goes to `gz_look` with `direct == 0`,
`junk == 1`, and copies the following input transparently. If the member decoded to nearly
`GZ_OFF_MAX` bytes, `x.pos` is near `GZ_OFF_MAX` there.

## Call sequence

Without the bound in `gz_look`:

```c
/* a gzip member that decodes to GZ_OFF_MAX - 3 bytes, then non-gzip bytes */
gzread(f, ...);            /* read the member to its end: x.pos = GZ_OFF_MAX - 3 */
gzread(f, buf, 1);         /* trailing garbage: eof set, how = LOOK, junk = 1 */
gzclearerr(f);             /* eof cleared */
gzread(f, buf, 3);         /* gz_look COPY: have = 8; copies 3; x.pos = GZ_OFF_MAX, have = 5 */
gzgetc(f);                 /* macro: (g)->pos++ overflows */
```

With patch 0004 the fourth call buffers three bytes, returns 3 with `x.have = 0` and records
`Z_DATA_ERROR`; the `gzgetc` returns -1.

## Evidence

- Model, without the bound: from a constructed reader at `x.pos = GZ_OFF_MAX - 3` with
  `how = LOOK`, `direct = 0`, `junk = 1`, an 8-byte input buffer and eight bytes `'A'` left in the
  file, Lean's kernel evaluated `gzread(file, buf, 3)` to return 3 with `x.pos = GZ_OFF_MAX` and
  `x.have = 5`. The start satisfied the position clauses of the reader invariant; the end did not.
  A following `gzgetc` faulted with `Fault.ub` on `x.pos + 1`; its buffered path is the same as
  the macro's. The state is constructed, not reached by a public history.
- Model, with patch 0004: three theorems check the runs from the same state. `start_clauses`:
  the start satisfies the position clauses. `gzread_within_room`: `gzread` returns 3 with
  `x.have = 0` and `Z_DATA_ERROR`, and the position clauses hold. `gzgetc_after_refused`: the
  following `gzgetc` returns -1 with no fault.
- C: the reading of `gz_look`, `gz_fetch` and `gz_read` without the bound gives the same trace as
  the model run without the bound.
- No sanitizer run: the history needs about 2^63 decoded bytes.

## Scope and confidence

Confidence is high that the C without the bound in `gz_look` allows the state, and that the
history above reaches it if a gzip member that long can be read. Scope: readers built with such a
patch, at a position within `size` bytes of `GZ_OFF_MAX`, after a gzip member with trailing data
and `gzclearerr`. Without patch 0004 the same history overflows already in `gz_read`
([gzread-pos-overflow](gzread-pos-overflow/README.md)).

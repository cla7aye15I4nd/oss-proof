# gz: position overflow after a transparent look near `GZ_OFF_MAX`

Status: confirmed in the model and by reading the C. Not reproduced under a sanitizer: the history
needs about 2^63 decoded bytes. It was a gap in the first version of the local
[patch 0004](../../patches/README.md), the fix of [gzread-pos-overflow](gzread-pos-overflow/README.md).
Patch 0004 now covers it: `gz_look`'s COPY branch buffers only `gz_room(state, avail_in)` bytes
and records `Z_DATA_ERROR` "position overflow" when the input goes past that. The patch is local
and pending upstream submission (extension approved by the owner on 2026-11-13).

## What went wrong

Patch 0004 keeps the position `state->x.pos` within `z_off64_t`. `gz_fetch` loads only what fits
before `GZ_OFF_MAX` (`gz_room`), and `gz_read` and `gzgets` drop buffered output once `x.pos` is
at `GZ_OFF_MAX`. The reader invariant needs more at each return: `x.pos + x.have <= GZ_OFF_MAX`,
because the `gzgetc()` macro of zlib.h does `(g)->pos++` on any buffered byte.

In the first version of the patch, `gz_look`'s transparent COPY branch was not bounded. It copied
all pending input to the output buffer and set `x.have = strm->avail_in`, up to `size` bytes, at
any `x.pos`. The drop in `gz_read` runs only on the next trip of its loop. So `gz_read` could
return with `x.pos + x.have > GZ_OFF_MAX`. The same held through `gz_skip` (`gz_skip_have` takes
only `min(have, skip)`) and through `gzdirect` (it calls `gz_look` and returns).

`gz_look` takes the COPY branch after the start only in one history:
`tests/verification/regressions/gz-copy-direct.c` shows it in the real C. A gzip member is
followed by data that is not gzip; `gz_decomp` treats it as trailing garbage (`junk == 1`) and
sets `eof`; `gzclearerr` clears `eof`; the next read goes to `gz_look` with `direct == 0`,
`junk == 1`, and copies the following input transparently. If the member decoded to nearly
`GZ_OFF_MAX` bytes, `x.pos` is near `GZ_OFF_MAX` there.

## History

With the first version of patch 0004:

```
/* a gzip member that decodes to GZ_OFF_MAX - 3 bytes, then non-gzip bytes */
gzread(f, ...);            /* read the member to its end: x.pos = GZ_OFF_MAX - 3 */
gzread(f, buf, 1);         /* trailing garbage: eof set, how = LOOK, junk = 1 */
gzclearerr(f);             /* eof cleared */
gzread(f, buf, 3);         /* gz_look COPY: have = 8; copies 3; x.pos = GZ_OFF_MAX, have = 5 */
gzgetc(f);                 /* macro: (g)->pos++ overflows */
```

With the current patch the fourth call buffers three bytes, returns 3 with `x.have = 0` and
records `Z_DATA_ERROR`; the `gzgetc` returns -1.

## Evidence

- Model, before the extension: from a constructed reader at `x.pos = GZ_OFF_MAX - 3` with
  `how = LOOK`, `direct = 0`, `junk = 1`, an 8-byte input buffer and eight bytes `'A'` left in the
  file, the kernel evaluated `gzread(file, buf, 3)` to return 3 with `x.pos = GZ_OFF_MAX` and
  `x.have = 5`. The start satisfied the position clauses of the reader invariant; the end did not.
  A following `gzgetc` faulted with `Fault.ub` on `x.pos + 1`; its buffered path is the same as
  the macro's. The state is constructed, not reached by a public history.
- Model, now: `ZlibF/Proof/gz.position-copy-overflow-regression.lean`, restated in
  `tests/verification/regressions/gz-position-copy-overflow.lean`, checks the fixed runs from the
  same state: `gzread` returns 3 with `x.have = 0` and `Z_DATA_ERROR`, the position clauses hold,
  and the following `gzgetc` returns -1 with no fault. The file's header records the earlier run.
- C: the reading of `gz_look`, `gz_fetch` and `gz_read` with the first version of patch 0004 gives
  the same trace as the earlier model run.
- No sanitizer run: the history needs about 2^63 decoded bytes.

## Scope and confidence

Confidence is high that the C with the first version of patch 0004 allowed the state, and that
the history above reaches it if a gzip member that long can be read. Scope: readers with that
version, at a position within `size` bytes of `GZ_OFF_MAX`, after a gzip member with trailing data
and `gzclearerr`. Without patch 0004 the same history overflows already in `gz_read` (F-1).

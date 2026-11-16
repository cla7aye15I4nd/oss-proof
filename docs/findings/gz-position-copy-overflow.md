# gz: `gz_look` can buffer bytes whose position is past `GZ_OFF_MAX`

In zlib's `gzread.c`, the transparent COPY branch of `gz_look` hands all pending input to the
output buffer, whatever the position `state->x.pos` is. After a gzip member with trailing data and
a `gzclearerr`, this happens in the middle of a file. If the position is then near `GZ_OFF_MAX`,
a read returns with buffered bytes whose position cannot be represented, and the `gzgetc()` macro
overflows `x.pos`. This is one more path of the position overflow in
[gzread-pos-overflow](gzread-pos-overflow/README.md), not a separate defect of zlib. It is the
reason the fix of that finding, the local [patch 0004](../../patches/README.md), bounds this
branch too: bounding `gz_fetch`, `gz_read` and `gzgets` alone does not close it.

Status: confirmed by reading the C. It is not reproduced under a sanitizer: the history needs
about 2^63 decoded bytes. The C that was read is upstream `develop` at commit
`757f0527154291bcf6bfbd6396ecde6bedd2db95`; `gzread.c` is byte-identical in zlib 1.4 (commit
`99623ef7097352da7993ba614161fd6a311e046e`), the revision this project verifies. With patch 0004,
the COPY branch buffers only `gz_room(state, avail_in)` bytes and records `Z_DATA_ERROR`
"position overflow" when the input goes past that. The patch has not been submitted upstream.

## What goes wrong

The `gzgetc()` macro of zlib.h does `(g)->pos++` on any buffered byte, in the caller's code and
with no check. So the position stays representable only if every reading call returns with
`x.pos + x.have <= GZ_OFF_MAX`.

`gz_look`'s transparent COPY branch copies all pending input to the output buffer and sets
`x.have = strm->avail_in`, up to `size` bytes, at any `x.pos`. Unpatched zlib has no bound on the
position at all. A fix that only bounds what `gz_fetch` loads, and makes `gz_read` and `gzgets`
drop buffered output once `x.pos` is at `GZ_OFF_MAX`, does not reach this branch, and the drop in
`gz_read` runs only on the next trip of its loop. So `gz_read` can return with
`x.pos + x.have > GZ_OFF_MAX`. The same holds through `gz_skip` (`gz_skip_have` takes only
`min(have, skip)`) and through `gzdirect` (it calls `gz_look` and returns).

The reading of the C is that `gz_look` takes the COPY branch after the start of a file only in
one history. A gzip member is followed by data that is not gzip; `gz_decomp` treats it as
trailing garbage (`junk == 1`) and sets `eof`; `gzclearerr` clears `eof`; the next read goes to
`gz_look` with `direct == 0`, `junk == 1`, and copies the following input transparently.
`tests/verification/regressions/gz-copy-direct.c` reaches this branch in the real C, at a small
position. If the member decoded to nearly `GZ_OFF_MAX` bytes, `x.pos` is near `GZ_OFF_MAX` there.

## Call sequence

In unpatched zlib, and with any fix that does not bound `gz_look`:

```c
/* a gzip member that decodes to GZ_OFF_MAX - 3 bytes, then non-gzip bytes */
gzread(f, ...);            /* read the member to its end: x.pos = GZ_OFF_MAX - 3 */
gzread(f, buf, 1);         /* trailing garbage: eof set, how = LOOK, junk = 1 */
gzclearerr(f);             /* eof cleared */
gzread(f, buf, 3);         /* gz_look COPY: have = 8; copies 3; x.pos = GZ_OFF_MAX, have = 5 */
gzgetc(f);                 /* macro: (g)->pos++ overflows */
```

The comments assume an 8-byte input buffer with eight bytes left in the file. With patch 0004 the
fourth call buffers three bytes, returns 3 with `x.have = 0` and records `Z_DATA_ERROR`; the
`gzgetc` returns -1.

## Evidence

- C: the reading of `gz_look`, `gz_fetch` and `gz_read` gives the trace above. No run of the real
  C shows it: the history needs about 2^63 decoded bytes.
- Model, with patch 0004: three theorems check the run from a constructed reader at
  `x.pos = GZ_OFF_MAX - 3` with `how = LOOK`, `direct = 0`, `junk = 1`, an 8-byte input buffer and
  eight bytes `'A'` left in the file. `start_clauses`: the start satisfies the position clauses
  of the reader invariant. `gzread_within_room`: `gzread(file, buf, 3)` returns 3 with
  `x.pos = GZ_OFF_MAX`, `x.have = 0` and `Z_DATA_ERROR`, and the position clauses hold.
  `gzgetc_after_refused`: the following `gzgetc` returns -1 with no fault. The state is
  constructed, not reached by a public history.
- Model, without the bound in `gz_look`: the same call was evaluated on a translation of
  `gzread.c` that bounded `gz_fetch`, `gz_read` and `gzgets` only. It returned 3 with
  `x.pos = GZ_OFF_MAX` and `x.have = 5`, which breaks the position clauses, and a following
  `gzgetc` faulted with `Fault.ub` on `x.pos + 1`; the buffered path of the `gzgetc` function is
  the same as the macro's. That translation is not retained, and no theorem records this run.

## Scope and confidence

Confidence is high that the C allows the state, and that the history above reaches it if a gzip
member that long can be read. Scope: a reader at a position within `size` bytes of `GZ_OFF_MAX`,
after a gzip member with trailing data and `gzclearerr`. In unpatched zlib no reading path bounds
the position ([gzread-pos-overflow](gzread-pos-overflow/README.md)); this page adds only that a
fix must bound `gz_look` as well.

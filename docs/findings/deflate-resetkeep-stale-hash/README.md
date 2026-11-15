# `deflateResetKeep`: stale hash entries can produce a wrong match

After a direct `deflateResetKeep` in the middle of a stream, the next stream can contain a match
whose third byte is wrong, so it decodes to data different from the input. This is a data error,
not a memory error, and no sanitizer reports it. `deflateResetKeep` is listed in `zlib.h` as not
part of the zlib API.

## Status

- Reproduced on the pinned source (`757f0527154291bcf6bfbd6396ecde6bedd2db95`, upstream
  `develop`) on arm64 macOS, with no sanitizer.
- Whether it is a zlib bug is not yet checked with upstream: zlib.h does not document the
  intended use of `deflateResetKeep`.
- Not reported upstream. No patch: the proofs exclude a direct `deflateResetKeep`
  ([deviations](../../deviations.md), row "Direct `deflateResetKeep`").

## Call sequence

```c
deflateInit2(&s, level, Z_DEFLATED, -wb, mem, Z_DEFAULT_STRATEGY);   /* raw deflate */
/* input A */
deflate(&s, Z_NO_FLUSH);            /* leaves lookahead in the window */
deflateResetKeep(&s);               /* keeps the window and the hash, drops the lookahead */
/* input B */
deflate(&s, Z_FINISH);              /* the second stream */
```

The second stream may refer to the kept window `window[0 .. strstart)`. Decoded with those bytes
as the preset dictionary, it should give B. In some histories it does not.

Why: `deflateResetKeep` leaves `strstart` and sets `lookahead` to 0. The hash still holds the
positions `strstart - 2` and `strstart - 1`, which were inserted with keys of three bytes that
reached into the dropped lookahead. The next `deflate` call writes new input from `strstart` on.
`longest_match` does not compare the third byte of a candidate (it relies on equal hash keys), so
a stale candidate can be accepted with a wrong third byte.

The complete program is [`repro.c`](repro.c). It tries random parameters and inputs, seed by seed,
and stops after three histories whose decoding differs from B. It includes `deflate.h` to read
`strstart` and the kept window.

## Run

From the repository root, with the `zlib/` submodule checked out:

```sh
cc -I zlib docs/findings/deflate-resetkeep-stale-hash/repro.c \
   zlib/{adler32,crc32,deflate,inflate,inftrees,inffast,trees,zutil}.c -o stale-hash
./stale-hash
```

Output of a run on arm64 macOS for this page (exit status 1):

```
MISMATCH seed 13 level 8 wb 15 mem 3 alpha 5 na 508 nb 1292 rc 1 got 1292 first diff 680
MISMATCH seed 35 level 6 wb 12 mem 6 alpha 4 na 2204 nb 1041 rc 1 got 1041 first diff 989
MISMATCH seed 40 level 8 wb 11 mem 9 alpha 4 na 913 nb 1754 rc 1 got 1754 first diff 437
tried 41 bad 3
```

Each `MISMATCH` line is one history: `inflate` returns `Z_STREAM_END` (`rc 1`) with the right
length, and the byte at `first diff` differs from the input. Three of the first 41 completed
histories differ.

## Sanitizer verdict

None. There is no out-of-bounds access and no undefined arithmetic in these histories; the error
is in the data. No `report.txt` is kept.

## Scope and severity

- **Who reaches it.** A program that calls `deflateResetKeep` directly after a `deflate` call that
  left lookahead, and then compresses more data with the same stream.
- **Effect.** The compressed stream decodes to data different from the input. No memory error. No
  error code is returned by `deflate` or by `inflate`.
- **Severity.** For such a program: silent data corruption. For a program that stays inside the
  documented API: none, since `deflateReset` clears the hash after `deflateResetKeep`.

With `deflateCopy` added to the history, the same stale entries lead to a memory error:
[deflate-copy-pending-prev](../deflate-copy-pending-prev/README.md).

## What `zlib.h` says

`deflateResetKeep` is declared under the comment "undocumented functions (not part of the zlib
API)" (`zlib.h:2043`, declaration at line 2051). Its use is not described.

## Fix

None is applied here. An experiment recorded in `repro.c`: with `CLEAR_HASH(s)` added to
`deflateResetKeep` after `s->lookahead = 0;`, none of 200000 histories differs. That experiment was
not rerun for this page.

## Relation to the proofs

The hash-chain clause of the deflate invariant `DInv` does not hold after a direct
`deflateResetKeep`. The deflate stream domain of the safety goals therefore has no such call, and
no theorem covers this history.

In this history, without `deflateCopy`, no memory error is known. The reading of the C is that
`longest_match` reads only bytes inside the window, whatever the hash keys are. That reading is
**to confirm**, and no proof of this project will confirm it while the call stays outside the
proved domain.

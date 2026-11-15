# `deflateCopy` after `deflateResetKeep`: `longest_match` reads outside the window

After a direct `deflateResetKeep`, a stream made by `deflateCopy` can hold two uninitialised
entries of the hash chain table `prev`. A later `deflate` on the copy follows one of them, and
`longest_match` reads outside the window. The sequence needs `deflateResetKeep`, which `zlib.h`
lists as not part of the zlib API, so this is not a bug of the documented API.

This page gives the status, the reproduction and the relation to the proofs. The mechanism, the
affected releases, the impact and the possible fixes are in the
[report draft](../deflate-copy-pending-prev-report.md), which is written for the zlib maintainers
and has not been sent.

## Status

- A memory error: a read of an uninitialised table entry, then a heap read outside the window.
- Reported by AddressSanitizer and by valgrind on the pinned source
  (`757f0527154291bcf6bfbd6396ecde6bedd2db95`, upstream `develop`) on x86_64 Linux (GCC 14);
  the same AddressSanitizer report on arm64 macOS. The patches of this repository do not touch
  the deflate sources.
- Outside the documented API: it needs a direct call of `deflateResetKeep`.
- Not reported upstream. No patch: the proofs exclude the call
  ([deviations](../../deviations.md), row "Direct `deflateResetKeep`").

## Call sequence

```c
deflateInit2(&a, 6, Z_DEFLATED, 9, 8, Z_DEFAULT_STRATEGY);   /* windowBits 9: a 1024-byte window buffer */
/* 600 bytes of input */
deflate(&a, Z_NO_FLUSH);
deflateResetKeep(&a);               /* keeps the window and the hash, drops the lookahead */
deflate(&a, Z_BLOCK);               /* no input: insert becomes 2 */
deflateCopy(&c, &a);                /* copies prev only below strstart - insert */
deflateParams(&c, 6, Z_RLE);
deflate(&c, Z_SYNC_FLUSH);          /* no input: deflate_rle sets insert to 0 */
deflateParams(&c, 6, Z_DEFAULT_STRATEGY);
/* input that starts with the three window bytes at strstart - 2 */
deflate(&c, Z_FINISH);              /* longest_match follows the uninitialised prev entry */
```

Every buffer is valid and separate, and every call is to an exported function. The complete
program is [`repro.c`](repro.c); the same driver is
[`copy.c`](../../../tests/regression/deflate-copy-pending-prev/copy.c) in the regression directory.
It includes `deflate.h` only to read `strstart` and three window bytes and to print state. It
installs an allocator that fills fresh memory with the 16-bit value 1030, which puts the candidate
position just past the 1024-byte window and makes the report deterministic. With the argument
`plain` it uses the default allocator.

## Run

From the repository root, with the `zlib/` submodule checked out:

```sh
ZLIB_SRC=$PWD/zlib bash tests/regression/deflate-copy-pending-prev/run.sh
```

The script builds zlib with `-fsanitize=address,undefined -g -O1` and runs `copy.c`;
AddressSanitizer must report the read in `longest_match`. When valgrind is installed, it also
builds without sanitizers and runs `copy plain` under memcheck, which must report the use of the
uninitialised entry. The script exits with status 0 when the checks hold. The line it prints for
the first check is:

```
ok: deflateCopy after deflateResetKeep, then Z_RLE: longest_match reads past the window
```

## Sanitizer verdict

From [`report.txt`](../../../tests/regression/deflate-copy-pending-prev/report.txt), x86_64 Linux:

```
==PID==ERROR: AddressSanitizer: heap-buffer-overflow on address 0x519000000e89 at pc 0x0000004033f1 bp 0x7ffe4828dba0 sp 0x7ffe4828db98
READ of size 1 at 0x519000000e89 thread T0
    #0 0x4033f0 in longest_match deflate.c:1511
    #1 0x4095b4 in deflate_slow deflate.c:2029
    #2 0x41ef85 in deflate deflate.c:1239
0x519000000e89 is located 7 bytes after 1026-byte region [0x519000000a80,0x519000000e82)
```

The region is the window of the copy, allocated in `deflateCopy` (`deflate.c:1361`). With the
default allocator, valgrind in the same file:

```
==PID== Conditional jump or move depends on uninitialised value(s)
==PID==    at 0x40176B: longest_match (deflate.c:1555)
==PID==  Uninitialised value was created by a heap allocation
==PID==    by 0x404C6F: deflateCopy (deflate.c:1362)
```

A run on arm64 macOS for this page gave the same AddressSanitizer report at `deflate.c:1511`;
valgrind was not available there.

## Scope and severity

- **Who reaches it.** A program that calls `deflateResetKeep` directly in the middle of a stream,
  then `deflateCopy`, then changes the strategy on the copy to `Z_RLE` (or `Z_HUFFMAN_ONLY`) and
  back. Data alone cannot trigger it: an attacker who controls only the bytes being compressed
  does not choose these calls.
- **Effect.** A read of uninitialised memory, then a read of up to 258 bytes at an offset of up to
  65535 from the window start. No write was observed. The compressed output may depend on the
  bytes read.
- **Releases.** The report appears on zlib 1.4 and on the pinned `develop`, and not on 1.3.1 or
  1.3.2 (AddressSanitizer, arm64 macOS, the same driver). The report draft names the two upstream
  commits that are both needed.
- **Severity.** Moderate for a program that uses `deflateResetKeep` this way; none for a program
  that stays inside the documented API.

## What `zlib.h` says

`deflateResetKeep` is declared under the comment "undocumented functions (not part of the zlib
API)" (`zlib.h:2043`, declaration at line 2051). `deflateCopy`, `deflateParams` and `deflate` are
documented, and zlib.h does not mention their use after `deflateResetKeep`.

## Fix

None is applied here, and none was sent upstream. The report draft lists three possible fixes.
One was tried on this reproduction only: with `deflateCopy` changed to copy all `w_size` entries
of `prev`, there is no report and `deflate` returns `Z_STREAM_END`.

## Relation to the proofs

The deflate safety goals exclude a direct `deflateResetKeep` from the call histories they cover.
This finding is the reason the exclusion cannot be removed: with the call, `deflate` can read
outside the window.

Without the call, the partial copy of `prev` is sound, and that is a theorem. In the numbering of
the report draft's mechanism:

- Without step 2 (`deflateResetKeep`) no chain head waits for insertion: every nonzero `head`
  entry is below `strstart - insert`. This is `DInv.heads_inserted` and, at level 0 with one
  pending slide, `DInv.slid_heads_inserted` (`ZlibF/Proof/deflate.c.universal-heads.lean`), for
  every state that satisfies the deflate invariant `DInv`. `DInv` holds after every history of the
  deflate stream domain (`reachable_inv`, under the hypotheses of
  `Goal.deflate_sequence_safety`). With two or more pending slides (level 0) the invariant says
  nothing about the tables, and `deflateParams` clears them before a nonzero level runs.
- Without step 4 (`deflateCopy`) the two entries hold the values written when the positions were
  inserted.
- Without step 5 (the `Z_RLE` flush) `fill_window` inserts the two positions, and so rewrites
  their entries, before any `longest_match`.

The real-C checker of the project agrees with the first statement on 4.6 million sampled states.
That is evidence, not proof.

A positional hash-chain invariant that admits `deflateResetKeep` is false after step 5. The
related data error without the copy is
[deflate-resetkeep-stale-hash](../deflate-resetkeep-stale-hash/README.md).

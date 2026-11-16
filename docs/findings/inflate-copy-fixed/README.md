# `inflateCopy` compares pointers into unrelated objects

`inflateCopy` on a stream that has decoded a fixed-code block, and no dynamic block after it,
compares a pointer into a static
table with a pointer into the heap-allocated inflate state, using `>=` and `<=`. C defines these
operators only for pointers into the same object. This page lets a zlib maintainer reproduce the
report and judge it without reading anything else.

## Status

- Undefined behaviour by the C standard (C11 6.5.8p5: relational comparison of pointers into
  different objects). Inside the documented use of `inflateCopy`.
- Reported by AddressSanitizer's pointer-pair check on unmodified upstream `develop` at commit
  `757f0527154291bcf6bfbd6396ecde6bedd2db95`, on x86_64 Linux and on arm64
  macOS.
- No wrong result was observed: without the pointer-pair check the same program returns `Z_OK`
  from `inflateCopy`.
- Fix submitted upstream as [PR #1369](https://github.com/madler/zlib/pull/1369). The maintainer
  answered "Applied" on 2026-11-06. The upstream `develop` head read on 2026-11-14 (`99623ef7`)
  does not contain it. The verified source applies the submitted commit as
  [patch 0001](../../../patches/README.md).

## Call sequence

```c
z_stream strm, copy;
unsigned char out[1];
memset(&strm, 0, sizeof strm);
memset(&copy, 0, sizeof copy);
inflateInit(&strm);                 /* default: zlib wrapper, 32K window */
strm.next_in = encoded;             /* a zlib stream whose only block is a fixed block */
strm.avail_in = sizeof encoded;
strm.next_out = out;
strm.avail_out = 1;                 /* room for one byte */
inflate(&strm, Z_NO_FLUSH);         /* Z_OK inside the fixed block: state->lencode is the static lenfix */
inflateCopy(&copy, &strm);          /* inflate.c:1383: state->lencode >= state->codes */
```

`encoded` is 23 bytes: a zlib header and one final fixed block that decodes to 2048 bytes `A`. The
complete program is [`repro.c`](repro.c). No buffer is too small, and no two buffers overlap.

The statement, in the unpatched `inflate.c` (lines 1383 and 1384):

```c
if (state->lencode >= state->codes &&
    state->lencode <= state->codes + ENOUGH - 1) {
```

`state->codes` is an array inside the inflate state, which `inflateInit` allocates. From the
start of a fixed block on, `state->lencode` points to `lenfix`, a static table.

## Run

From the repository root, with the `zlib/` submodule checked out:

```sh
python3 docs/findings/inflate-copy-fixed/reproduce.py
```

The script compiles `repro.c` with the six decoder sources of the unmodified `zlib/`, using
`-O1 -g -fsanitize=address,pointer-compare,pointer-subtract -fno-omit-frame-pointer`, and runs it
with `ASAN_OPTIONS=detect_invalid_pointer_pairs=2:detect_leaks=0`. `CC` selects the compiler (the
default is `clang`). The script fails unless the run exits with an error and prints the
pointer-pair report that names `inflateCopy` and `lenfix`; a compile error does not count. On
success its last line is:

```
CONFIRMED: default-init fixed-block inflateCopy compares unrelated objects
```

## Sanitizer verdict

From [`report.txt`](report.txt), x86_64 Linux:

```
inflate=0 produced=1 fixed_block=1
==PID==ERROR: AddressSanitizer: invalid-pointer-pair: 0x5a0a568b10a0 0x78f4037e0668
    #0 0x5a0a568ab70f in inflateCopy zlib/inflate.c:1383
0x5a0a568b10a0 is located 0 bytes inside of global variable 'lenfix' defined in 'zlib/inffixed.h:10:19' (0x5a0a568b10a0) of size 2048
0x78f4037e0668 is located 1384 bytes inside of 7176-byte region [0x78f4037e0100,0x78f4037e1d08)
```

These are five lines of the report; the 7176-byte region is the inflate state allocated by
`inflateInit2_` (`inflate.c:206`). A run on arm64 macOS (Apple clang) printed the
same verdict at the same line.

## Scope and severity

- **Who reaches it.** Any `inflateCopy` of a stream whose `lencode` is the static table: the
  default `inflateInit` or any `inflateInit2`, and any input that contains a fixed block.
  `inflate` points `lencode` at the static table when it meets a fixed block (`inflate_fixed`,
  called at `inflate.c:736`). The pointer stays there until a dynamic block replaces it
  (`inflate.c:820`) or the stream is reset (`inflateResetKeep`, `inflate.c:118`); a stored block
  does not change it. So the copy can come inside the fixed block, after it, or after the stream
  has ended. The retained reproduction copies inside the block. With its output buffer enlarged
  to 4096 bytes, `inflate` returns `Z_STREAM_END` and `inflateCopy` gets the same report at the
  same line (a run on arm64 macOS with Apple clang; that variant is not retained).
- **Effect.** None was observed. On a platform with a flat address space the comparison is an
  address comparison, it is false for the static table, and the copy keeps the pointer to the
  static table, which is correct. The same holds for `distcode`. The risk is only that a compiler
  may assume the comparison is between pointers into one object.
- **Severity.** Low: strictly undefined, no memory error, no wrong output, not controlled by the
  compressed data beyond its use of a fixed block.

## What `zlib.h` says

`inflateCopy` "Sets the destination stream as a complete copy of the source stream"
(`zlib.h:974`). It puts no condition on where in the stream the source has stopped, so the call
sequence above is a documented use.

## Fix

[PR #1369](https://github.com/madler/zlib/pull/1369), commit
`300fea14353d2e2ca61210aca7c48861ded5788c`: test whether the table is the state's own with pointer
equality, `state->lencode == state->codes`, in place of the two relational comparisons. Whenever `lencode` points into the state's own array it points to its start: `inflate.c` assigns
it from `state->next` right after `state->next = state->codes` (lines 118, 820 and 898). So the
equality test selects the same cases.
`copy->lencode` is then set to `copy->codes`, and `distcode` keeps its offset.

[Patch 0001](../../../patches/README.md) is exactly that
commit.

## Relation to the proofs

The Lean translation follows the patched source. In the pointer model, ordering two pointers into
different objects is a fault, so the unpatched statement could not be proved safe. The reproduction
on this page builds the unpatched source on purpose. A differential test builds the patched source
and compares successful `inflateCopy` calls of the real C with the translation; that comparison is
evidence of fidelity, not proof.

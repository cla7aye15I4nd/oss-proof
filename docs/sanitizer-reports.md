# Sanitizer reports

This page lists every retained reproduction in which a sanitizer reports undefined behaviour or a
memory error in the real C. There are eleven directories. Five show caller mistakes that the
safety theorems exclude by a named premise, one shows a call sequence that needs an undocumented
function, and five show defects of zlib itself, which the verified source patches. Each directory
has a runner, the C driver and the raw sanitizer output in `report.txt`.

## How to read a section

Each section gives the call sequence as C, the sanitizer's verdict lines copied from `report.txt`,
and one of two things:

- for a caller mistake, the **excluding premise**: the assumption of a safety goal that the
  layout violates, as a link to its row in [deviations](deviations.md);
- for a zlib defect, a link to its page in [findings](findings.md) and the patch that fixes it.

The safety goals named here are those of `ZlibF/Spec/Safety/`: one goal per function, such as
`Goal.inflate_safety` and `Goal.deflate_safety`, and one goal per call sequence, such as
`Goal.inflate_sequence_safety`, `Goal.deflate_sequence_safety` and `Goal.gz_sequence_safety`. A
premise of a function's goal is also a premise of the same call inside the sequence goal. All of
these goals are proved; the level of each is in [progress](progress.md#scope).

Platform and source of the reports:

| Reports | Host | Source built |
| --- | --- | --- |
| The four caller-mistake directories other than `gzprintf-error-string` | x86_64 Linux; the same verdicts on arm64 macOS, with one difference noted under `prime.c` | The pinned source with patch 0001. Their line numbers are those of the pinned source: patch 0001 changes only `inflate.c` near line 1383. |
| `gzprintf-error-string` | arm64 macOS (Apple clang) only | The pinned source with patches 0001 to 0005. Its line numbers are those of that patched source and differ from the pinned source. |
| `deflate-copy-pending-prev` | x86_64 Linux (GCC 14); the same AddressSanitizer report on arm64 macOS | The pinned source; no patch touches the deflate files. |
| `inflate-copy-fixed`, `gzseek-pushback-overflow`, `gzread-transparent-stale-next` | x86_64 Linux (GCC 15.2); the same verdicts on arm64 macOS (Apple clang 21) | The pinned source without any patch. Line numbers are those of the pinned source. |
| `gzread-pos-overflow`, `gzwrite-pos-overflow` | x86_64 Linux (kernel 7.0, GCC 15.2). The write report also reproduces on arm64 macOS; the read report did not reproduce in a run there ([its page](findings/gzread-pos-overflow/README.md) says what was observed). | The pinned source with the patches except 0004, as each `run.sh` builds it. The retained run of `gzwrite-pos-overflow` with the real `/dev/null` used patches 0001 to 0003. The `gzread.c` lines are one above those of the pinned source; the `gzwrite.c` lines are those of the pinned source. |

A sanitizer report is evidence about one run of the real C. It is not a proof.

## Caller mistakes outside the proved domain

A program that calls zlib has to build these layouts and call orders on purpose: it points a
header buffer into its own input or output, edits the header record while zlib uses it, calls a
function after the point zlib.h allows, passes `NULL` for a length cell, or passes the string that
`gzerror` returned to `gzprintf` on the same handle. They are not inputs an attacker controls. No
compressed byte stream reaches any of them.

None of these was reported upstream, and none is recorded as a zlib bug. The `gzprintf` case is
recorded as a documentation gap.

### `inflate-gzip-extra`: the gzip extra buffer during `inflate`

[Directory](../tests/regression/inflate-gzip-extra/README.md),
[report](../tests/regression/inflate-gzip-extra/report.txt). zlib.h is silent about both layouts.

`overlap.c`: the extra buffer overlaps the input that holds the extra field.

```c
inflateInit2(&strm, 31);            /* gzip */
head.extra = in + 14;               /* the extra field is at in + 12 .. in + 20 */
head.extra_max = 8;
inflateGetHeader(&strm, &head);
strm.next_in = in;
inflate(&strm, Z_FINISH);           /* inflate.c:626: zmemcpy(head->extra + len, next, ...) */
```

```
==PID==ERROR: AddressSanitizer: memcpy-param-overlap: memory ranges [0x7269582f018e,0x7269582f0196) and [0x7269582f018c, 0x7269582f0194) overlap
    #2 0x64e96ca550f5 in inflate inflate.c:626
```

`shrink.c`: the caller lowers `extra_len` while `inflate` is inside the extra field.

```c
head.extra = malloc(0xffffffffu);
head.extra_max = 0xffffffffu;
inflateGetHeader(&strm, &head);
inflate(&strm, Z_NO_FLUSH);         /* 12 header bytes: stops inside the 4-byte extra field */
head.extra_len = 0;                 /* the caller changes the record */
inflate(&strm, Z_NO_FLUSH);         /* inflate.c:626: writes at offset 2^32 - 4 */
```

```
==PID==ERROR: AddressSanitizer: heap-buffer-overflow on address 0x7b0f3f1ff7ff at pc 0x7f0f43328d2d bp 0x7ffd603f0d00 sp 0x7ffd603f04a8
WRITE of size 4 at 0x7b0f3f1ff7ff thread T0
    #2 0x64da3988bf46 in inflate inflate.c:626
```

Excluding premise: [deviations, row "Inflate gzip extra field"](deviations.md#stream-calls-inflate-and-deflate)
(`InflateHeaderProgress`). While `inflate` reads a gzip header, the extra buffer is separate from
the unread input, and in the extra field `extra_len` is not below the count still to read. It is
a premise of `Goal.inflate_safety` and of every `inflate` call of `Goal.inflate_sequence_safety`.

### `deflate-gzip-name-output`: the gzip name inside a buffer `deflate` writes

[Directory](../tests/regression/deflate-gzip-name-output/README.md),
[report](../tests/regression/deflate-gzip-name-output/report.txt). zlib.h is silent about both
layouts.

`output.c`: the name is the caller's output buffer.

```c
deflateInit2(&s, 6, Z_DEFLATED, 31, 1, Z_DEFAULT_STRATEGY);   /* gzip, memLevel 1 */
head.name = buf;                    /* 1024 bytes, NUL at index 505 */
deflateSetHeader(&s, &head);
s.next_out = buf;
s.avail_out = 1024;
deflate(&s, Z_NO_FLUSH);            /* deflate.c:1177: the flush overwrites the NUL */
```

```
==PID==ERROR: AddressSanitizer: heap-buffer-overflow on address 0x793cff3e0480 at pc 0x5dd4f2b5609c bp 0x7ffefba39f50 sp 0x7ffefba39f40
READ of size 1 at 0x793cff3e0480 thread T0
    #0 0x5dd4f2b5609b in deflate deflate.c:1177
```

`pending.c`: the name lies in the stream's own `pending_buf` (reached through the internal
state). The verdict is the same kind, at the same line:

```
==PID==ERROR: AddressSanitizer: heap-buffer-overflow on address 0x6daba5be0500 at pc 0x644e87c872ea bp 0x7ffe6e6b3ff0 sp 0x7ffe6e6b3fe0
READ of size 1 at 0x6daba5be0500 thread T0
    #0 0x644e87c872e9 in deflate deflate.c:1177
```

Excluding premise: [deviations, row "Deflate gzip header regions"](deviations.md#stream-calls-inflate-and-deflate)
(`DeflateHeaderApart`). While `deflate` writes an attached gzip header, the input range, the
output range, the extra field, the name and the comment are pairwise separate, and the last three
lie outside the storage the stream owns. It is a premise of `Goal.deflate_safety` and of every
`deflate` call of `Goal.deflate_sequence_safety`.

### `deflate-history-domain`: late calls and edits of the header record

[Directory](../tests/regression/deflate-history-domain/README.md),
[report](../tests/regression/deflate-history-domain/report.txt). Four cases.

`prime.c`: `deflatePrime` after `deflate` has started. zlib.h excludes it: `deflatePrime` "must
be used before the first deflate() call" (`zlib.h:825`).

```c
deflateInit2(&z, 1, Z_DEFLATED, -15, 1, Z_DEFAULT_STRATEGY);  /* raw, memLevel 1 */
deflate(&z, Z_NO_FLUSH);            /* 300 input bytes: symbols are recorded */
for (k = 0; k < 200; k++)
    deflatePrime(&z, 16, 0xffff);   /* pending grows over the symbol buffer */
deflate(&z, Z_FINISH);              /* trees.c:930: d_code(dist) */
```

```
trees.c:930:20: runtime error: index 767 out of bounds for type 'uch [512]'
trees.c:930:20: runtime error: load of address 0x614810c3571f with insufficient space for an object of type 'const uch'
```

On arm64 macOS the first line is the same; UndefinedBehaviorSanitizer then reports a signed
left-shift overflow at `trees.c:937` in place of the second line, because the byte read out of
bounds differs.

`header.c 1`: `deflateSetHeader(strm, NULL)` after `deflate` has started. zlib.h excludes it:
`deflateSetHeader` may be called after init or reset and "before the first call of deflate()"
(`zlib.h:840`).

```c
deflateInit2(&z, 6, Z_DEFLATED, 31, 1, Z_DEFAULT_STRATEGY);   /* gzip, memLevel 1 */
g.extra = extra;                    /* 2000 bytes */
g.extra_len = 2000;
deflateSetHeader(&z, &g);
z.avail_out = 10;
deflate(&z, Z_NO_FLUSH);            /* stops inside the extra field, 500 bytes written */
deflateSetHeader(&z, Z_NULL);
deflate(&z, Z_FINISH);              /* deflate.c:1137: s->gzhead->extra */
```

```
deflate.c:1137:22: runtime error: member access within null pointer of type 'struct gz_header'
==PID==ERROR: AddressSanitizer: SEGV on unknown address 0x000000000018 (pc 0x62e83b3ddde4 bp 0x7ffe5b49aca0 sp 0x7ffe5b49aa40 T0)
```

Excluding premise for both: [deviations, row "Other stream arguments"](deviations.md#stream-calls-inflate-and-deflate)
(`DeflateNotStarted`). `deflatePrime` and `deflateSetHeader` are called only before the first
`deflate` call has started the stream. It is a premise of `Goal.deflatePrime_safety` and
`Goal.deflateSetHeader_safety`, and of the same calls in `Goal.deflate_sequence_safety`.

`header.c 2`: the same start; then the caller shortens the extra field. zlib.h is silent on edits
while the header is written.

```c
g.extra_len = 10;                   /* below the 500 bytes already written */
deflate(&z, Z_FINISH);              /* deflate.c:1142: zmemcpy from the extra buffer */
```

```
==PID==ERROR: AddressSanitizer: heap-buffer-overflow on address 0x7c21e51e0850 at pc 0x7e51e6f2901f bp 0x7ffed5b3e4c0 sp 0x7ffed5b3dc68
READ of size 512 at 0x7c21e51e0850 thread T0
    #2 0x57575de3d176 in deflate deflate.c:1142
```

`clear.c`: a 1500-byte extra field and a 3-byte name; the caller clears `extra` part-way.

```c
head.extra = extra;
head.extra_len = 1500;
head.name = (Bytef *)name;          /* "abc" */
deflateSetHeader(&s, &head);
s.avail_out = 100;
deflate(&s, Z_FINISH);              /* stops inside the extra field */
head.extra = Z_NULL;                /* the caller changes the record */
deflate(&s, Z_FINISH);              /* deflate.c:1177: reads name[gzindex], past the name */
```

```
==PID==ERROR: AddressSanitizer: heap-buffer-overflow on address 0x722a2ebe0204 at pc 0x64bb6cd58142 bp 0x7fff28a19670 sp 0x7fff28a19660
READ of size 1 at 0x722a2ebe0204 thread T0
    #0 0x64bb6cd58141 in deflate deflate.c:1177
0x722a2ebe0204 is located 496 bytes after 4-byte region [0x722a2ebe0010,0x722a2ebe0014)
```

Excluding premise for both: [deviations, row "Deflate gzip header progress"](deviations.md#stream-calls-inflate-and-deflate)
(`DeflateHeaderProgress`). At each `deflate` call that writes an attached gzip header, a field
still covers the part already written, and a field is not set to `NULL` part-way. It is a premise
of `Goal.deflate_safety` and of every `deflate` call of `Goal.deflate_sequence_safety`.

### `compress-allocation`: a `NULL` length cell

[Directory](../tests/regression/compress-allocation/README.md), `ubwitness.c`,
[report](../tests/regression/compress-allocation/report.txt). zlib.h describes `destLen` as the
size of the destination buffer on entry; it does not mention `NULL`. `report.txt` holds only this
witness step of `run.sh`; the rest of that runner is a comparison with the Lean translation and
has no sanitizer report.

```c
compress2(dst, NULL, src, 1, 6);    /* compress.c:70: z_size_t got = *destLen; */
compress(dst, NULL, src, 1);        /* the same statement */
```

```
compress.c:70:20: runtime error: load of null pointer of type 'uLongf'
```

Excluding premise: [deviations, row "Whole-buffer compression"](deviations.md#whole-buffer-utilities-and-checksums)
(`CompressArguments`; the clause `capacity ≠ none` of `CompressorSafety`). `compress` and
`compress2` take a non-`NULL` length cell. It is a premise of `Goal.compress_safety` and
`Goal.compress2_safety`. The `_z` forms test the cell for `NULL` and their goals admit it.

### `gzprintf-error-string`: the handle's own error string as a `%s` argument

[Directory](../tests/regression/gzprintf-error-string/README.md), `errstr.c`,
[report](../tests/regression/gzprintf-error-string/report.txt). A documentation gap, not a zlib
bug: zlib.h says that later `gzerror` calls may invalidate the string and that closing the file
makes it unavailable (`zlib.h:1793`); it does not mention `gzprintf`.

```c
/* p[1]: the write end of a full, non-blocking pipe */
gzFile f = gzdopen(p[1], "wT");
gzwrite(f, big, 100000);            /* stalls with EAGAIN: err = Z_ERRNO, a message is allocated */
const char *m = gzerror(f, &e);     /* the handle's own message */
gzprintf(f, "%s", m);               /* gzvprintf frees the message, then vsnprintf reads it */
```

```
==PID==ERROR: AddressSanitizer: heap-use-after-free on address 0x604000000390 at pc 0x000102dc6ed0 bp 0x00016d8715f0 sp 0x00016d870d80
READ of size 2 at 0x604000000390 thread T0
    #2 0x0001025a9e50 in gzvprintf gzwrite.c:491
freed by thread T0 here:
    #1 0x0001025a7fc8 in gz_error gzlib.c:568
    #2 0x0001025a9b1c in gzvprintf gzwrite.c:448
```

In the pinned source without patches the three statements are at `gzwrite.c:485` (the
`vsnprintf` call), `gzlib.c:563` (the `free`) and `gzwrite.c:442` (the `gz_error` call).

Excluding premise: [deviations, row "Gz printf strings"](deviations.md#gzip-file-interface)
(`GzArguments`). The format of `gzprintf` and `gzvprintf` and every `%s` argument lie outside the
blocks the handle owns. It is a premise of every `gzprintf` and `gzvprintf` call of
`Goal.gz_sequence_safety`.

## A call sequence that needs an undocumented function

### `deflate-copy-pending-prev`: `deflateCopy` after `deflateResetKeep`

[Directory](../tests/regression/deflate-copy-pending-prev/README.md), `copy.c`,
[report](../tests/regression/deflate-copy-pending-prev/report.txt). This is not a caller layout:
every buffer is valid and separate, and every call is to an exported function. The sequence uses
`deflateResetKeep`, which zlib.h declares under "undocumented functions (not part of the zlib
API)". The full account is the [finding](findings/deflate-copy-pending-prev/README.md); a
[report draft](findings/deflate-copy-pending-prev-report.md) exists and has not been sent.

```c
deflateInit2(&a, 6, Z_DEFLATED, 9, 8, Z_DEFAULT_STRATEGY);
deflate(&a, Z_NO_FLUSH);
deflateResetKeep(&a);
deflate(&a, Z_BLOCK);
deflateCopy(&c, &a);
deflateParams(&c, 6, Z_RLE);
deflate(&c, Z_SYNC_FLUSH);          /* no input */
deflateParams(&c, 6, Z_DEFAULT_STRATEGY);
deflate(&c, Z_FINISH);              /* input that starts with the bytes at strstart - 2 */
```

```
==PID==ERROR: AddressSanitizer: heap-buffer-overflow on address 0x519000000e89 at pc 0x0000004033f1 bp 0x7ffe4828dba0 sp 0x7ffe4828db98
READ of size 1 at 0x519000000e89 thread T0
    #0 0x4033f0 in longest_match deflate.c:1511
```

With the default allocator, valgrind reports a conditional jump on an uninitialised value at
`deflate.c:1555`, created by the `prev` allocation of `deflateCopy`.

Excluding premise: [deviations, row "Direct `deflateResetKeep`"](deviations.md#stream-calls-inflate-and-deflate).
A deflate call history has no direct `deflateResetKeep` call. This limits the streams that
`Goal.deflate_safety`, `Goal.deflateCopy_safety` and the other deflate goals speak about, and the
histories of `Goal.deflate_sequence_safety`.

## Library defects

These five are defects of zlib inside the documented use. Each has a page under
[findings](findings.md) with the call sequence, the run command, the verdict, the severity and the
fix. The runners build the source without the fix on purpose; the gz runners also build it with
the fix and check that the report is gone.

| Directory | Verdict | Finding | Fix in the verified source |
| --- | --- | --- | --- |
| [inflate-copy-fixed](findings/inflate-copy-fixed/README.md) ([report](findings/inflate-copy-fixed/report.txt)) | AddressSanitizer `invalid-pointer-pair`, `inflate.c:1383`, between the static `lenfix` and the inflate state | [`inflateCopy` compares unrelated pointers](findings/inflate-copy-fixed/README.md) | Patch 0001, upstream PR #1369 |
| [gzseek-pushback-overflow](../tests/regression/gzseek-pushback-overflow/README.md) ([report](../tests/regression/gzseek-pushback-overflow/report.txt)) | UndefinedBehaviorSanitizer: signed integer overflow, `gzlib.c:395`, `403`, `424` | [`gzseek` after an initial `gzungetc`](findings/gzseek-pushback-overflow/README.md) | Patch 0002, upstream PR #1361 |
| [gzread-transparent-stale-next](../tests/regression/gzread-transparent-stale-next/README.md) ([report](../tests/regression/gzread-transparent-stale-next/report.txt)) | AddressSanitizer `heap-buffer-overflow` READ of size 1, `gzread.c:369`, 0 bytes after the 32-byte output buffer | [`gzread` copies from a stale `x.next`](findings/gzread-transparent-stale-next/README.md) | Patch 0003, upstream PR #1363 |
| [gzread-pos-overflow](../tests/regression/gzread-pos-overflow/README.md) ([report](../tests/regression/gzread-pos-overflow/report.txt)) | UndefinedBehaviorSanitizer: signed integer overflow in `gz_read` (`x.pos += n`), in the `gzgetc()` macro and in the `gzgetc` function | [gz position overflow, reading](findings/gzread-pos-overflow/README.md) | Patch 0004, local |
| [gzwrite-pos-overflow](../tests/regression/gzwrite-pos-overflow/README.md) ([report](../tests/regression/gzwrite-pos-overflow/report.txt)) | UndefinedBehaviorSanitizer: signed integer overflow, `gzwrite.c:230` (`gz_write`) and `gzwrite.c:352` (`gzputc`) | [gz position overflow, writing](findings/gzwrite-pos-overflow/README.md) | Patch 0004, local |

Upstream state of each fix is in [patches](../patches/README.md).

## Clean runs, kept as evidence that a layout is defined

These runs use the same sanitizers and report nothing. They show that a layout is defined C, so
the proofs cover it.

- [inflate-shared-block](../tests/regression/inflate-shared-block/README.md): the input and
  output ranges lie in one heap block, in both orders. This is inside the premise `StreamBuffers`,
  which asks that the two ranges are separate, not that they lie in different blocks.
- [inflate-gzip-flags-prime](../tests/regression/inflate-gzip-flags-prime/README.md):
  `inflatePrime` on a gzip stream in `FLAGS` makes the flags word 65544. This is defined,
  though zlib.h says `inflatePrime` "should be used with raw inflate" (`zlib.h:1021`).

## Not listed

- [deflate-slide](../tests/regression/deflate-slide/README.md): UndefinedBehaviorSanitizer reports
  a signed overflow in an artificial internal state that no call sequence is shown to reach. It
  tests the translation's overflow fault, not a caller layout.
- Differential regressions whose sanitizer builds stay silent: `inflate-copy`,
  `inflate-deferred-distance`, `inflate-prime`, `trees-depth-read`, `crc-byte-views`.
- The data error in [deflate-resetkeep-stale-hash](findings/deflate-resetkeep-stale-hash/README.md),
  which no sanitizer reports.
- The zero advance of `x.next` that the local patch 0005 removes
  ([unset](findings/gz-reset-next-uninitialised/README.md),
  [dangling](findings/gz-next-dangling-after-direct-read/README.md)): undefined by the letter of C,
  shown with a probe; no sanitizer reports it.
- The position overflow after a transparent look, a gap of the first version of patch 0004
  ([finding](findings/gz-position-copy-overflow.md)): confirmed in the model and by reading the C,
  not reproduced under a sanitizer.
- [inflate-configured-window](../tests/regression/inflate-configured-window/README.md): a native run
  of the C on one input, with no sanitizer and no report.

## Adding a reproduction

A new sanitizer reproduction goes under `tests/regression/<name>/` with `run.sh`, `report.txt`
and a section on this page. `report.txt` holds the raw output, with process ids replaced and paths
made relative to the repository or the zlib root.

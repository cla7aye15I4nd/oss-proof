# Specification review records (historical)

This page keeps the six closed records of the section "Specification review" of [progress](../progress.md), as it stood
after the required goals were accepted on `bde170e9`. The text is unchanged apart from relative links. It is a historical
record: states such as "open" and "checked", hours, counts and dates describe the time each
entry was written. They are not current status. Current status and remaining work are only in
[progress](../progress.md).

### Specification review

#### Gzip seek mode

Corrected. `GzSeek` used to let a successful seek return a handle in the other mode, so
the abstract `gz_seek_read` goal was false. The relation now keeps the mode. The goal has a
[locally checked proof](../../ZlibF/Proof/Api/GzSeekRead.lean), and the former counterexample is a
[regression](../../tests/verification/regressions/gz-seek-mode.lean). Registration and CI on a
named commit remain. This was a model issue, not a zlib issue.

#### Inflate initialization cleanup

Corrected. For an invalid window parameter the `inflateInit2_` goal required a structurally
unchanged state table, but allocation followed by free lengthens that table. That branch now
compares every object table entry by entry (`SameObjectsUpToTableShape`); no C operation
observes the table length. The goal has a
[locally checked proof](../../ZlibF/Proof/public-inflate-init2.lean), and the former counterexample
is a [regression](../../tests/verification/regressions/inflate-init2-table-shape.lean).
Registration and CI on a named commit remain. This was a contract issue, not a zlib issue.

#### Decompression utility cleanup

Corrected. `UncompressCounted` and `UncompressSingle` compared the final heap with
`SameObjects`, which requires equal object tables, including their physical length.
`uncompress2_z` allocates a local `z_stream` and a local 8-byte block before its argument
checks and frees both on every path; a freed entry stays in the table as an empty entry. Even
the null-argument refusal therefore made the four decompression goals false. They now compare
tables entry by entry (`SameObjectsUpToTableShape`, moved to `Spec/Public/Memory.lean`), as
the `inflateInit2_` contract does. The counterexample is a
[regression](../../tests/verification/regressions/uncompress-table-shape.lean). This was a contract
issue, not a zlib issue. `CompressorContract` had the same pattern (`compress2_z` also frees a
local `z_stream`).

The same four contracts also lacked the heap representation condition `Uniq` (one object per
block identity below `nextBlk`), which [the trusted base](../trusted-base.md) requires of every
initial heap and which every public stream history already assumes (`InitDomain`,
`StreamReachable`). It is now a premise. It does not narrow the C domain: every C state has such
a representation.

Corrected for the compressors too. `CompressorContract` and `CompressorSafety` had both defects.
The local `z_stream` of `compress2_z` is freed on every path after the argument checks, so its
empty entry made the goals false even when `deflateInit` refuses the level before allocating
(level 10 on the public caller witness:
[regression](../../tests/verification/regressions/compress-table-shape.lean)). They now use
`SameObjectsUpToTableShape`. They also lacked `Uniq`, which the `deflateInit` contract and the
`deflate` stream history (`StreamReachable.deflateInit`) assume; it is now a premise. Statement test
of `CompressorSafety`: `tests/goals/compress-safety` (ASan, UBSan, leak count, allocation
failures, invalid levels; no clause violated in 9000 runs).

Review the corrected shared `Uncompress2` relation independently. The deferred-distance and
exact-free corrections have independent counterexamples and checked regression proofs;
implementation refinement remains open. Its former empty-output clause on memory failure and
extension clause on buffer error have been removed using the existing paired counterexample.
Complete the older abstract gz and dictionary models before using them as complete operational
refinements; the concrete public targets do not assume their callee contracts.

#### Gzip open path length

Corrected on 2026-11-13. `gz_open` copies the caller path with `malloc(len + 1)` and
`snprintf(state->path, len + 1, "%s", path)`. Two halves:

- `snprintf` past `INT_MAX`: the model `snprintf` returns -1 there, as glibc does
  ([trusted base](../trusted-base.md), Formatting). No fault, no statement change.
- `malloc` above `PTRDIFF_MAX`: the runtime allocator now refuses a request of `2^63` bytes or
  more, as glibc 2.43 does ([trusted base](../trusted-base.md), Allocation size). A path of
  `2^63 − 1` bytes then makes `gzopen` return NULL without an oracle failure and without calling
  `open`. The old second clause of `OpenContract` admitted that path and demanded an invalid
  mode, an oracle failure or a failed `open`, so it was false of the corrected model. The
  checked counterexample is the
  [regression](../../tests/verification/regressions/gzopen-path-ptrdiff.lean)
  (`old_open_clause_false`). `Goal.gz_initialisation_domain` was false for the same path: it
  promised a handle under `NoAllocationFailure h`.

Correction, in its own commit. `OpenContract` (`Goal.gzopen`, `Goal.gzopen64`), second clause:
old premises `Fresh h → Uniq h → LibraryGlobals h → FileSystem fs → CString h path name →
CString h mode flags`; new premises add `ZlibF.PlatformMemory.ByteObjectsFit h` after
`FileSystem fs`. `Goal.gz_initialisation_domain`, first clause: old premises `... FileSystem fs →
NoAllocationFailure h → CString h path name → ...`; new premises add `ByteObjectsFit h` after
`NoAllocationFailure h`. With it, the path and its NUL lie in one object below `2^63` bytes, so
the copy is never refused for its size and `len + 1` does not wrap. The witness clause and
`Goal.gzdopen` (a 19-byte path) are unchanged. None of the three goals was proved or registered.
The premise is the accepted platform scope ([deviations](../deviations.md), row "Platform
byte-object scope").

#### Gzip library findings with local fixes

Library reports of 2026-11-12, kept here until the owner decides whether F-1 and W7 move to
`README.md` as confirmed findings. Each has a local patch, approved by the owner on 2026-11-12 and
not yet submitted upstream ([patches](../../patches/README.md)).

- F-1, [gzread position overflow](../findings/gzread-pos-overflow/README.md): after a transparent
  `gzseek` to `INT64_MAX` on Linux `/dev/zero`, `gzread` overflows the signed `x.pos`. Confirmed
  by UBSan on x86_64 Linux. Patch 0004.
- W7, [gzwrite position overflow](../findings/gzwrite-pos-overflow/README.md): a transparent writer
  on `/dev/null` that seeks to `INT64_MAX - 10` overflows `x.pos` in `gzwrite` (and in `gzputc` at
  `INT64_MAX`). Confirmed by UBSan on x86_64 Linux with the real device. Patch 0004.
- [gz look COPY past the limit](../findings/gz-position-copy-overflow.md): `gz_look`'s COPY branch
  buffered all pending input without the room bound, so a reader after a gzip member, trailing
  data and `gzclearerr` near `GZ_OFF_MAX` returned with `x.pos + x.have` past it. Confirmed in the
  model (`gz.position-copy-overflow-regression`) and by reading the C; not reproducible in practice
  (about 2^63 decoded bytes). Patch 0004, extended on 2026-11-13. Statement changes with it:
  `GzLookSpec`'s COPY disjunct is now `how = COPY ∧ avail_in = 0 ∧ (x.have ≠ 0 ∨ x.pos =
  GZ_OFF_MAX) ∧ x.pos + x.have ≤ GZ_OFF_MAX` (was `how = COPY ∧ x.have ≠ 0`); `BodyPost` of
  `gz_fetch` lets the loop continue in COPY with `avail_in = 0`, and its measure ranks COPY 0.
- R-3, [x.next never written](../findings/gz-reset-next-uninitialised/README.md): `gzseek` and
  `gzdirect` right after `gzopen` advance the never-written `x.next` by zero. Undefined by the
  letter of C; no sanitizer report. Patch 0005.
- R-4, [x.next dangling after a direct read](../findings/gz-next-dangling-after-direct-read/README.md):
  after a large `gzread` into a buffer the caller then frees, `gzseek` and `gzdirect` advance
  `x.next` by zero inside the freed buffer. Undefined by the letter of C; no sanitizer report.
  Patch 0005.

The translations of `gzread.c`, `gzwrite.c` and `gzlib.c` follow both patches. Only 0005 has a
differential row (a direct read into a freed buffer, then `gzdirect` and `gzseek`); 0004 needs a
device, which the file model cannot express. `tests/audit/theorems.txt` still lists
`seekTail_dangling_ub` and `gzseek64_dangling_next_ub`, which no longer exist; their removal is for
a human.

#### Gzip offset and rewind on the OS-call oracle

Corrected in `caad9db4` under the owner's delegation; the evidence is recorded here. The OS-call
oracle lets an `lseek` return any value in `[0, 2^63 - 1]` without moving the descriptor (M3), as
Linux does on some devices. Three registered goals state the descriptor position after `lseek`:

- `Goal.gzoffset64` and `Goal.gzoffset` (`OffsetContract`, `Spec/Public/GzControl.lean`). Old: for
  every reachable handle in `GzValid` and every world with `FileSystem fs`, the call returns, keeps
  the heap, changes the world only in `errno` (`{ fs' with errno := fs.errno } = fs`), and returns
  the descriptor position less the buffered input of a reader (-1 for a bad descriptor). New: the
  same under the added premise `RegularOs fs`, and the world changes only in `errno` and the call
  counter (`{ fs' with errno := fs.errno, nos := fs.nos } = fs`).
- `Goal.gzrewind`. Old: for every reachable handle in `GzValid`, the call returns -1 with the heap
  kept, or 0 with the reset state and the descriptor at the saved start; a writer or a serious
  error gives -1 with the world kept. New: the same under the added premise `RegularOs fs`.

Reason. Every oracle call advances the call counter `nos`, so the old world clause of the offset
contract is false for every handle (by the definition of `fsLseek`). An oracle `lseek` returns a
value unrelated to the descriptor, so the value clauses hold only when every later call is regular:
`RegularOs fs` (`Spec/Public/GzState.lean`). Checked counterexample: the
[regression](../../tests/verification/regressions/gz-offset-regular-world.lean). In a world admitted
by `FileSystem` whose `lseek` returns 77 without moving, `gzdopen(3, "r")` records the start 77;
`gzoffset64` and `gzoffset` then return 77 while the descriptor is at 0, and `gzrewind` returns 0
while the descriptor stays at 0. The old three statements are false, and so is the corrected offset
contract without `RegularOs`. This was a model change, not a zlib issue.

The three goals are now functional contracts of the regular-file instance. Their safety on every
world (every oracle) is part of `Goal.gz_sequence_safety` (`GzSafety.lean`), proved on the branch `skeleton/gz`. Its call
dispatch (`operation_safe` in `gz.skeleton.lean`) takes `gzoffset64`, `gzoffset` and `gzrewind` as
next calls through `gzoffset64_step`, `gzoffset_step` and `gzrewind_step`. Each is `GzCallSafe` for
every `fs`, with no `RegularOs` and no read budget: no fault, a result, the open descriptors kept,
`GzInv` kept, and only the handle's blocks changed. The three step lemmas are open on the skeleton,
and `gzrewind_step` relies on the local patch for R-3. Until they are checked, the safety of these
calls on a non-regular world is not proved. They cannot reuse the registered proofs as they stand,
since those now assume `RegularOs`.

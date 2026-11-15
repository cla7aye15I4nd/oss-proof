# zlib-f

Kernel-checked Lean 4 proofs that zlib is safe. The C source is translated statement by statement,
and the proofs show that every documented public function of the default x86_64 Linux build runs
with no undefined behaviour, no memory error and no leak, and terminates, over its call sequences.

**Proved.** All 63 required goals have a registered theorem of exactly their type, and the
acceptance suite is green on commit `bde170e9` (2026-11-15). The required goals are the safety
goals and the non-vacuity goals of the 86 documented functions of the target build: `inflate` and
`deflate` with their call sequences, the other stream functions, the checksums, `compress*` and
`uncompress*`, the gzip file interface, and the callback decoder `inflateBack`.

**Assumed.** The kernel checks each proof against its Lean statement. It does not check that the
runtime model, the hand translation, or the model of files and formatting match C: these are
reviewed and tested, and listed in the [trusted base](docs/trusted-base.md). Differential tests
are evidence of fidelity, not proof. Some theorems state a premise that `zlib.h` does not: caller
buffers that do not overlap, a read budget below 2^61 bytes for the termination of the gz reading
calls, fewer than 2^48 input bytes for one `inflateBack` call. [Deviations](docs/deviations.md)
lists every one. The verified source is the pinned `zlib/` plus the five [patches](patches/README.md).

**Open.** The 31 gz functions and the three `inflateBack` functions have no safety goal of their
own yet: each names its sequence goal (`Goal.gz_sequence_safety`,
`Goal.inflate_back_sequence_safety`), which is registered. The per-function goals are still to be
stated and registered.

**Not planned.** Functional correctness (the output of `inflate` equals the format, the output of
`deflate` decodes to its input), since 2026-11-11; a functional fact stays in scope only when a
planned safety proof depends on it, and what is already proved stays. Also not planned: other
build configurations, and the functions that `zlib.h` lists as undocumented.
[Scope](docs/progress.md#scope) gives every group with its reason. The
[status page](https://www.dataisland.org/zlib-f/status.html) shows each result as open, checked or
registered, from the proof records.

## Targets

Each public function has two goals, both in the Lean namespace `ZlibF.Spec.Public.Goal`. Its
**safety goal** says the call returns without undefined behaviour, writes only its frame and leaks
nothing. Its **functional goal**, in `ZlibF/Spec/Functional/`, says what the result is.
`tests/audit/public-api.json` names both for every function (`safety_goal`, `functional_goal`).
The safety goals are in `ZlibF/Spec/Safety/`; the gz and `inflateBack` goals of both kinds are
still in `ZlibF/Spec/Public/`. The acceptance audit requires the safety goals and the non-vacuity goals:
each must have a theorem of exactly its type in `tests/audit/theorems.txt`. The manifest's
`open_safety` list of exceptions is empty. A proved functional goal is audited in full; an
unproved one fails nothing. See [the split](docs/design/safety-functional-split.md).

## Documentation

**[Read the documentation website](https://www.dataisland.org/zlib-f/)** · [Website content sources](docs/README.md)

| Start here | What it answers |
| --- | --- |
| [Proof overview](https://www.dataisland.org/zlib-f/reference/docs/overview.html) | What is the claim, its assumptions and the proof framework? |
| [Results and status](https://www.dataisland.org/zlib-f/status.html) | What is established, what is planned and what is not? |
| [All-target proof graph](https://www.dataisland.org/zlib-f/reference/docs/progress.html#proof-progress-graph) | How do targets depend on each other, and which input ranges are covered? |
| [Evidence index](https://www.dataisland.org/zlib-f/reference/docs/progress.html) | Where are the exact statements, proofs and dependencies of every target? |
| [Specifications](https://www.dataisland.org/zlib-f/reference/docs/spec/README.html) | What safety, input, API, helper and format requirements must be proved? |
| [API](https://www.dataisland.org/zlib-f/reference/api.html) | What does each function require and guarantee? |
| [Data format](https://www.dataisland.org/zlib-f/reference/docs/spec/format/README.html) | What do DEFLATE, zlib and gzip bytes mean? |
| [Design](https://www.dataisland.org/zlib-f/reference/docs/design/README.html) | How do the translation and memory model work? |
| [Proofs](https://www.dataisland.org/zlib-f/reference/docs/proof/README.html) | How are the arguments composed? |
| [Checking](https://www.dataisland.org/zlib-f/reference/docs/checking/README.html) | What counts as checked and as accepted? |
| [Contributing](https://www.dataisland.org/zlib-f/reference/docs/checking/contributing.html) | Which commands do I run, in which order? |
| [Glossary](https://www.dataisland.org/zlib-f/reference/docs/glossary.html) | What do the terms mean? |

## Repository

- `zlib/`: pinned upstream source, never edited in place; fixes are in `patches/`.
- `ZlibF/Zlib/`: statement-by-statement C translation.
- `ZlibF/Spec/Safety/`: the required safety goals. `ZlibF/Spec/Functional/`: functional contracts,
  the format and API models. `ZlibF/Spec/Public/`: definitions both use.
- `ZlibF/Proof/` and `ZlibF/Math/`: implementation proofs and heap-free reasoning.
- `ZlibF/Runtime/`: memory, pointer, arithmetic and execution semantics.
- `tests/`: differential, mutation and proof-audit checks.

## Local checks

```bash
lake build ZlibF
scripts/check-sorry.sh
```

[Contributing](docs/checking/contributing.md) lists every step. See [checking](https://www.dataisland.org/zlib-f/reference/docs/checking/README.html) for each check's scope and final acceptance.
Differential tests are evidence of translation fidelity, not proof.
[Source findings](docs/findings.md) state their confidence and scope.

## Source finding: deflateCopy after deflateResetKeep

After a direct `deflateResetKeep` and a `deflate(Z_BLOCK)`, two chain heads wait for insertion;
`deflateCopy` does not copy their `prev` slots, and a `Z_RLE` or `Z_HUFFMAN_ONLY` flush on the copy
ends with `insert = 0`, so they are never re-inserted. A later default-strategy `deflate` then
follows an uninitialised `prev` slot, and `longest_match` reads outside the window. The
[retained reproduction](docs/findings/deflate-copy-pending-prev/README.md) diagnoses the pinned
unmodified C on x86_64 Linux: AddressSanitizer reports the read outside the window, and valgrind
the use of the uninitialised slot. Confidence is high for the diagnosed sequence. It reproduces on
zlib 1.4 and the pinned `develop`, not on 1.3.1 or 1.3.2 (the partial copy came with 1.3.2, the
dropped lookahead with 1.4). Scope: it needs `deflateResetKeep`, which zlib.h declares
undocumented and not part of the zlib API, so this is not a bug of the documented API; the proved
deflate stream domain excludes it ([deviations](docs/deviations.md)). A
[report draft](docs/findings/deflate-copy-pending-prev-report.md) is written; nothing was sent
upstream.

## Source finding: gz position overflow

`gzread` and `gzwrite` add the bytes they move to the signed 64-bit position `x.pos` without a
bound. On a transparent file whose position can reach 2^63 − 1 the addition overflows, which is
undefined behaviour. Reading: on a device whose `lseek` succeeds without moving (`/dev/zero` on
Linux), `gzseek(INT64_MAX, SEEK_SET)` is accepted and the next `gzread` overflows in `gz_read`,
`gzgetc` and the `gzgetc()` macro ([reproduction](docs/findings/gzread-pos-overflow/README.md)).
Writing: after a transparent writer seeks near 2^63 on `/dev/null`, `gzwrite` and `gzputc` overflow
([reproduction](docs/findings/gzwrite-pos-overflow/README.md)). UndefinedBehaviorSanitizer reports
both on x86_64 Linux with the pinned C. Confidence is high for the diagnosed sequences. Scope: a
device whose `lseek` succeeds without moving, or a transparent position near 2^63. The verified
source includes a local fix, [patch 0004](patches/README.md), approved by the owner and not yet
submitted upstream: the position stays within `z_off64_t`, and an overflowing call fails with
`Z_DATA_ERROR`.

A gap in that fix: `gz_look`'s transparent COPY branch buffers up to `size` bytes without the room
bound, so after a gzip member with trailing data, `gzclearerr` and a read near 2^63 − 1, a reader
returns with `x.pos + x.have` past `GZ_OFF_MAX`, and the `gzgetc()` macro then overflows `x.pos`
([finding](docs/findings/gz-position-copy-overflow.md)). Confirmed in the model and by reading the
C; not reproducible in practice (about 2^63 decoded bytes); not confirmed by a sanitizer.
Confidence is high for the patched source as written. Scope: patch 0004 readers within `size`
bytes of `GZ_OFF_MAX` after that history. Patch 0004 now bounds that branch too.

## Source fix

`inflateCopy` compares a static fixed table with a separately allocated state
table after a default-initialized stream pauses inside a fixed block.
The [retained reproduction](docs/findings/inflate-copy-fixed/README.md) diagnoses
the pinned unmodified C. The verified source now includes the exact fix from
[upstream PR #1369](https://github.com/madler/zlib/pull/1369) through
[the temporary patch](patches/README.md). The translation uses the same equality
check. Confidence is high for the diagnosed LP64 issue. The public copy proof is
registered: `Goal.inflateCopy` and `Goal.inflateCopy_safety`.

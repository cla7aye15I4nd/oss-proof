# zlib-f

Kernel-checked Lean 4 proofs that zlib is safe. The C source is translated to Lean statement by
statement. The proofs show that every documented public function of the default x86_64 Linux
build runs with no undefined behaviour, no memory error and no leak, and terminates, in every
sequence of calls, under the premises each theorem states.

**Proved.** Each of the 86 documented functions of the target build has a safety goal, and a
theorem whose type is exactly that goal: `inflate` and `deflate`, the other stream functions, the
checksums, `compress*` and `uncompress*`, the gzip file interface, and the callback decoder
`inflateBack`. So has `gzvprintf`, which `zlib.h` lists as undocumented and `gzprintf` goes
through. Further goals, each with a theorem of exactly its type, cover the call sequences of
`inflate`, `deflate`, `inflateBack` and the gz functions (sequence safety goals), the calls the
library must refuse, such as a `NULL` stream or handle (refusal goals), and the fact that the
premises can be met ([non-vacuity goals](docs/glossary.md#goals)).
[Coverage by function](docs/coverage.md) names the theorem of each function.

**Status.** One page records at which [level](docs/glossary.md#status) each result stands
(checked, registered or accepted), the commit of each run of the
[acceptance suite](docs/glossary.md#checking), the number of goals and the work that remains:
[progress, Scope](docs/progress.md#scope).

**Assumed.** The kernel checks each proof against its Lean statement. Six things are trusted and
not proved ([trusted base](docs/trusted-base.md)):

1. the Lean kernel, three standard axioms, and the audit programs;
2. the runtime model of memory, pointers, faults and loops;
3. the hand translation of the C;
4. the selected source: the pinned `zlib/` plus the [patches](patches/README.md);
5. the build configuration, and the model of allocation, files and formatting;
6. the statements: that each goal says what it should.

Differential tests are evidence that the translation matches the C, not proof. Some theorems
state a premise that `zlib.h` does not: caller buffers that do not overlap, the default
allocator, a read budget below 2^61 bytes for the termination of the gz reading calls, fewer
than 2^48 input bytes for one `inflateBack` call. [Deviations](docs/deviations.md) is the
checklist of these premises by function.

**Not required.** Functional correctness is not required for the safety results: that the output
of `inflate` equals the format, or that the output of `deflate` decodes to its input. One part of
it is planned work: the round trip of a default zlib stream through `deflate` and
then `inflate`. Its conditional form says: when both call sequences reach `Z_STREAM_END`, the
output equals the input. After it come completeness (both always finish with enough room) and the
unconditional form. Other build configurations, custom allocators and the functions that `zlib.h`
lists as undocumented are not planned. [Scope](docs/progress.md#scope) gives every group with its
reason, and how far the round trip is. Functional goals proved earlier are kept.

## Which theorem covers a function

| Question | Where |
| --- | --- |
| Which theorem proves that function X is safe, and on which domain? | [Coverage by function](docs/coverage.md) |
| What must my call satisfy to be covered? | [Deviations](docs/deviations.md), the checklist at the top |
| Is the result checked, registered or accepted, and on which commit? | [Scope](docs/progress.md#scope) |
| What do the words mean? | [Glossary](docs/glossary.md) |

## Kinds of goal

A goal is a Lean proposition named `Goal.…`; a goal is proved only by a theorem whose type is
exactly the goal. The manifest `tests/audit/public-api.json` names a safety goal and a functional
goal for every documented function. The safety goal is the function's own, named
`Goal.<function>_safety` (or `_safe`); for `compressBound` and `compressBound_z`, which are pure,
the functional goal stands for it.

| Kind | Says | Where | Required by the audit |
| --- | --- | --- | --- |
| Safety goal | The call returns without undefined behaviour, writes only the memory it is allowed to (its frame) and leaks nothing | `ZlibF/Spec/Safety/`; the sequence and refusal goals of gz and the sequence goal of `inflateBack` in `ZlibF/Spec/Public/` | Yes |
| Non-vacuity goal | The premises of the safety goals can be met: a concrete heap on which init or open succeeds | `ZlibF/Spec/Safety/Domains.lean`, `ZlibF/Spec/Public/` | Yes |
| Functional goal | What the result is: return values, output bytes | `ZlibF/Spec/Functional/` | No. A proved one is audited in full; an unproved one fails nothing |

[The split](docs/design/safety-functional-split.md) gives the rules.

## Documentation

**[Read the documentation website](https://www.dataisland.org/zlib-f/)** · [Website content sources](docs/README.md)

| Start here | What it answers |
| --- | --- |
| [Overview](https://www.dataisland.org/zlib-f/reference/docs/overview.html) | What is proved, what is assumed, and how is the proof built? |
| [Results and status](https://www.dataisland.org/zlib-f/status.html) | What is registered, what is planned and what is not? |
| [Coverage by function](https://www.dataisland.org/zlib-f/reference/docs/coverage.html) | Which theorem covers function X? |
| [Deviations](https://www.dataisland.org/zlib-f/reference/docs/deviations.html) | What must a call satisfy to be covered? |
| [Trusted base](https://www.dataisland.org/zlib-f/reference/docs/trusted-base.html) | What does the kernel not check? |
| [All-target proof graph](https://www.dataisland.org/zlib-f/reference/docs/progress.html#proof-progress-graph) | How do targets depend on each other, and which input ranges are covered? |
| [Evidence index](https://www.dataisland.org/zlib-f/reference/docs/progress.html) | Where are the exact statements, proofs and dependencies of every target? |
| [Specifications](https://www.dataisland.org/zlib-f/reference/docs/spec/README.html) | What do the safety goals, the API contracts and the formats say? |
| [API](https://www.dataisland.org/zlib-f/reference/api.html) | What does each function require and guarantee? |
| [Design](https://www.dataisland.org/zlib-f/reference/docs/design/README.html) | How do the translation and memory model work? |
| [Proofs](https://www.dataisland.org/zlib-f/reference/docs/proof/README.html) | How are the arguments composed? |
| [Checking](https://www.dataisland.org/zlib-f/reference/docs/checking/README.html) | What does each check establish? |
| [Contributing](https://www.dataisland.org/zlib-f/reference/docs/checking/contributing.html) | Which commands do I run, in which order? |
| [Glossary](https://www.dataisland.org/zlib-f/reference/docs/glossary.html) | What do the terms mean? |

## Repository

- `zlib/`: pinned upstream source, never edited in place; fixes are in `patches/`.
- `ZlibF/Zlib/`: statement-by-statement C translation.
- `ZlibF/Spec/Safety/`: the required safety goals. `ZlibF/Spec/Functional/`: functional contracts,
  the format and API models. `ZlibF/Spec/Public/`: definitions both use, and five required
  goals of the gz interface and of `inflateBack`: their sequence, refusal and non-vacuity goals.
- `ZlibF/Proof/` and `ZlibF/Math/`: implementation proofs and heap-free reasoning.
- `ZlibF/Runtime/`: memory, pointer, arithmetic and execution semantics.
- `tests/`: differential tests, the proof audit, and the proof mutants.

## Local checks

```bash
lake build ZlibF
scripts/check-sorry.sh
```

These two are the first steps of the fast gate, not all of it. The fast gate is the jobs `build`
and `no-sorry` of `.github/workflows/lean.yml`. It also builds the audit tools and the
differential drivers, searches the sources for forbidden constructs, runs
`tests/audit/PartialCheck.lean` on the built library, checks that the patches apply to the pinned
`zlib/`, and runs `scripts/check-strlit.py` and `scripts/check-spec-layers.py`. [Contributing](docs/checking/contributing.md) lists every step, and
[checking](docs/checking/README.md) says what each check establishes and how a result becomes
accepted. Proof mutants are additional evidence, run on request; they are not part of acceptance.

## Issues found in zlib

The work found the issues below in the pinned source. Each row gives the reproduction, the
confidence and the scope. The last two rows are broken promises about a size, not memory errors. [Findings](docs/findings.md) has the full text of each and the upstream
state; [patches](patches/README.md) describes each patch.

| Issue | In the documented API? | Evidence and confidence | Fix in the verified source |
| --- | --- | --- | --- |
| `inflateCopy` compares unrelated pointers with a relational operator, which is undefined behaviour, when a stream has stopped inside a fixed block | Yes | [Reproduction](docs/findings/inflate-copy-fixed/README.md) on the pinned C. High for the diagnosed sequence. | Patch 0001, the fix of upstream [PR #1369](https://github.com/madler/zlib/pull/1369) |
| `gzseek` after an initial `gzungetc`: `x.pos` is -1 and the range checks of `gzseek64` overflow signed arithmetic | Yes | [Reproduction](docs/findings/gzseek-pushback-overflow/README.md): UndefinedBehaviorSanitizer reports three sites. High. | Patch 0002, from upstream [PR #1361](https://github.com/madler/zlib/pull/1361), open |
| `gzread` after a partial read that fails, in transparent mode: `gz_fetch` returns before it sets `x.next`, and the readers copy from the old pointer, outside the buffer | Yes; it needs a read error after partial data | [Reproduction](docs/findings/gzread-transparent-stale-next/README.md): AddressSanitizer reports the read. High. | Patch 0003, upstream [PR #1363](https://github.com/madler/zlib/pull/1363), open |
| gz position overflow: `gzread`, `gzgetc`, the `gzgetc()` macro, `gzwrite` and `gzputc` add to the signed 64-bit position `x.pos` without a bound | Yes; on a device whose `lseek` succeeds without moving (`/dev/zero`, `/dev/null`), or a transparent position near 2^63 | Reproductions for [reading](docs/findings/gzread-pos-overflow/README.md) and [writing](docs/findings/gzwrite-pos-overflow/README.md): UndefinedBehaviorSanitizer on x86_64 Linux. High for the diagnosed sequences. | Patch 0004, local, approved by the owner, not submitted upstream: the position stays within `z_off64_t`, and an overflowing call fails with `Z_DATA_ERROR` |
| The same overflow through the transparent COPY branch of `gz_look`, in the first version of patch 0004: after a gzip member with trailing data, `gzclearerr` and a read near 2^63 − 1, `x.pos + x.have` passes `GZ_OFF_MAX` | Yes; within `size` bytes of `GZ_OFF_MAX` after that history | [Finding](docs/findings/gz-position-copy-overflow.md): confirmed in the model and by reading the C. Not confirmed by a sanitizer; the history needs about 2^63 decoded bytes. High for the patched source as written. | Patch 0004 bounds that branch too |
| Zero advance of an unset or dangling `x.next`: `gzseek64` and `gz_skip_have` do `x.next += 0` when the field was never written or points into a freed caller buffer | Yes; the two call sequences of the findings | Probe runs for the [unset](docs/findings/gz-reset-next-uninitialised/README.md) and the [dangling](docs/findings/gz-next-dangling-after-direct-read/README.md) case. Undefined by the letter of C. Weaker than the rows above: no sanitizer reports either case and no misbehaviour was observed. | Patch 0005, local, approved by the owner, not submitted upstream |
| `deflateCopy` after `deflateResetKeep`: two pending `prev` slots are not copied, a later `deflate` on the copy follows an uninitialised slot, and `longest_match` reads outside the window | No: it needs a direct call of `deflateResetKeep`, which `zlib.h` lists as undocumented | [Reproduction](docs/findings/deflate-copy-pending-prev/README.md) on the unmodified pin: AddressSanitizer reports the read, valgrind the uninitialised slot. High for the diagnosed sequence. It reproduces on zlib 1.4 and the pinned `develop`, not on 1.3.1 or 1.3.2. | None. The proved deflate domain excludes the call ([deviations](docs/deviations.md)). A [report draft](docs/findings/deflate-copy-pending-prev-report.md) exists; nothing was sent upstream. |
| `deflateBound` is too small with `Z_FIXED` at levels 1 to 3, `windowBits` 15 and `memLevel` 8: one `deflate(Z_FINISH)` call with that room returns `Z_OK`, against the promise of `zlib.h` | Yes. A broken promise, not a memory error; `compress`, `compress2` and `compressBound` use the default strategy and are not affected | [Reproduction](docs/findings/deflatebound-fixed-far-matches/README.md) on the pinned C, with and without sanitizers, which report nothing. High for the diagnosed parameters. A system zlib 1.2.12 fails at every level 1 to 9. Not reported upstream. Whether upstream knows it is not yet checked with upstream. | None. No safety goal depends on the value of the bound |
| `deflateBound` with a gzip extra field of length 2^32 − 2 or 2^32 − 1: `2 + extra_len` wraps at 32 bits, and the bound is about 64 KiB too small | Yes. A broken promise, not a memory error | [Reproduction](docs/findings/deflatebound-extra-len/README.md) on the pinned C. Known upstream. | None. No safety goal depends on the value of the bound |

The safety goals of `inflateCopy` and of the gz functions are stated for the patched source.

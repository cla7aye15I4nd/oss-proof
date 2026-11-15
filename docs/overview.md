# Understanding and proving zlib

Read one task, then expand the mechanism you need. Each illustrated chapter
explains what an operation does and the proof obligation that follows from it.
The header language menu switches between English and 简体中文 on the same page.

## The claim

**Proved.** Every documented public function of the default x86_64 Linux build of zlib is safe.
On every input that its premises admit, the translated call returns with no undefined behaviour
and no memory error, writes only what it may, leaks nothing, and terminates. This holds over call
sequences: for every history of an inflate stream, a deflate stream, a callback decoder and a
gzip file handle. The 63 required goals are registered, and the acceptance suite is green on
commit `bde170e9` (2026-11-15).

**Assumed.** The theorems are about a Lean translation that runs on a runtime model. That the
model and the translation match C is reviewed and tested, not proved: see
[trusted base](trusted-base.md). The premises each theorem puts on the caller are in
[deviations](deviations.md). Differential tests are evidence of fidelity, not proof. Compiler,
operating-system and hardware correctness are outside the proof.

**Open.** The gz functions and the three `inflateBack` functions have no safety goal of their own
yet. Each names its sequence goal, which is registered. The per-function goals are still to be
stated and registered.

**Not planned.** Functional correctness (the output of `inflate` equals the format, the output of
`deflate` decodes to its input), since 2026-11-11. A functional fact is in scope only when a
planned safety proof depends on it; what is already proved stays. Model-only statements, other
build configurations and the functions that `zlib.h` declares undocumented are not planned
either. [Scope](progress.md#scope) lists every group with its reason.

## Contents

- [The claim](#the-claim)
- [Reading path](#reading-path)
- [Shared proof rules](#shared-proof-rules)
  - [Scope](#scope)
  - [Argument](#argument)
  - [Evidence](#evidence)

## Reading path

<a id="1-follow-a-complete-task"></a>
<a id="1-what-zlib-does"></a>
<a id="11-one-library-three-related-formats"></a>
<a id="12-repetition-becomes-a-backward-reference"></a>
<a id="13-meaning-of-compressed-bytes"></a>
<a id="13-symbols-become-bits-and-blocks"></a>
<a id="14-where-these-jobs-live-in-the-library"></a>
<a id="2-how-applications-use-the-apis"></a>
<a id="2-understand-the-encoded-bytes"></a>
<a id="21-one-decoder-two-kinds-of-lifetime"></a>
<a id="22-the-ordinary-inflate-loop"></a>
<a id="23-copies-reuse-and-borrowed-metadata"></a>
<a id="24-compression-has-its-own-completion-protocol"></a>
<a id="3-pause-and-continue-the-same-task"></a>
<a id="33-meaning-of-compressed-bytes"></a>
<a id="4-add-format-headers-and-integrity-checks"></a>
<a id="41-construct-and-interpret-decoding-tables"></a>
<a id="42-join-the-slow-and-fast-paths"></a>
<a id="43-close-the-call-and-its-history"></a>
<a id="5-reuse-branch-and-control-a-task"></a>
<a id="51-window-and-hash-chain-invariants"></a>
<a id="52-trees-symbols-and-shared-output-storage"></a>
<a id="53-publish-blocks-and-compose-calls"></a>
<a id="6-choose-an-application-interface"></a>
<a id="61-construct-and-interpret-decoding-tables"></a>
<a id="62-join-the-slow-and-fast-paths"></a>
<a id="63-close-the-call-and-its-history"></a>
<a id="71-window-and-hash-chain-invariants"></a>
<a id="72-follow-the-actual-implementation"></a>
<a id="72-trees-symbols-and-shared-output-storage"></a>
<a id="73-publish-blocks-and-compose-calls"></a>
<a id="74-locate-the-exact-evidence"></a>
<a id="proving-the-zlib-implementation"></a>

| Chapter | Follow the example to understand… |
| --- | --- |
| [1. A complete task](guide/round-trip.md) | Original bytes → compressed bytes → recovered bytes; start, process and release. |
| [2. Repetition, codes and blocks](guide/encoding.md) | Overlapping history copies, Huffman codes and block choice. |
| [3. Streaming](guide/streaming.md) | Buffer exhaustion, retained bits/history and exact continuation. |
| [4. Formats and integrity checks](guide/wrappers.md) | A shared DEFLATE body, wrapper conditions and trailer validation. |
| [5. State operations](guide/state-operations.md) | Reset for another task, Copy for a checkpoint, dictionaries and flushes. |
| [6. Application interfaces](guide/interfaces.md) | Whole buffers, callbacks, gzip files and logical Seek. |

Follow a chapter's links when you need an exact contract or C-level argument.
[Specifications](spec/README.md) define required behavior;
[implementation arguments](proof/README.md) give the technical derivation by
C component. These references serve different questions from the guided examples.
Review records are grouped under Checking, outside this first reading path.

## Shared proof rules

<a id="1-what-must-be-proved"></a>
<a id="3-what-must-be-proved-and-why"></a>
<a id="7-how-the-arguments-become-checked-claims"></a>

### Scope

<a id="11-the-implementation-and-configurations"></a>
<a id="12-safety-of-calls-and-lifetimes"></a>
<a id="2-assumptions-and-model-boundaries"></a>
<a id="21-platform-assumptions"></a>
<a id="22-caller-and-external-world-obligations"></a>
<a id="23-what-the-kernel-trusts"></a>
<a id="25-configuration-and-calling-protocol-are-separate"></a>
<a id="31-the-implementation-and-configurations"></a>
<a id="32-safety-of-calls-and-lifetimes"></a>
<a id="4-assumptions-and-model-boundaries"></a>
<a id="41-platform-assumptions"></a>
<a id="42-caller-and-external-world-obligations"></a>
<a id="43-what-the-kernel-trusts"></a>
<a id="71-scope-and-assumptions"></a>

The target is the default x86_64 Linux build. A safety goal quantifies over every input,
parameter, allocation outcome and history that its premises admit. The ranges in
[input configurations](spec/input-configurations.md) describe coverage of intermediate work.
Examples select particular runs without narrowing public targets. The accepted
[platform premises](spec/platform.md) include each represented byte object
having fewer than `2^63` bytes; this does not bound total stream length.
[Safety](spec/safety.md) owns the exact UB, frame, termination and resource rules.
[Trusted base](trusted-base.md) and [deviations](deviations.md) own model limits.

### Argument

<a id="3-how-the-proof-is-built"></a>
<a id="31-translate-the-actual-c-execution"></a>
<a id="32-establish-an-invariant-by-initialization"></a>
<a id="33-preserve-it-through-calls"></a>
<a id="34-relate-executions-to-byte-meaning"></a>
<a id="4-the-inflate-argument"></a>
<a id="5-how-the-proof-is-built"></a>
<a id="5-the-deflate-argument"></a>
<a id="51-translate-the-actual-c-execution"></a>
<a id="52-establish-an-invariant-by-initialization"></a>
<a id="53-preserve-it-through-calls"></a>
<a id="54-relate-executions-to-byte-meaning"></a>
<a id="6-the-inflate-argument"></a>
<a id="7-the-deflate-argument"></a>
<a id="73-establish-preserve-and-compose"></a>

An invariant is a set of facts about a stream's state that must hold before each further
call: for example, that the decoder's saved history agrees with the bytes already recovered.
The subject is the pinned C plus registered patches, translated statement by
statement. Implementation readings in the chapters are **to confirm** by proof.
Initialization must establish the state and ownership invariant. Each actual
call derives its helper premises and preserves the required facts on the
returned heap; End accounts for released resources. A callee contract must be
proved about that callee. A top-level domain needs a concrete witness.

The [common method](proof/method.md) connects these steps by induction over
legal call histories. Where a safety proof needs a functional fact, it relates actual bytes to
the independent format meaning.
The chapters explain each mechanism's specific invariant at its example.

### Evidence

<a id="6-reading-a-formal-result"></a>
<a id="61-find-its-exact-statement"></a>
<a id="62-follow-its-proof-and-evidence"></a>
<a id="8-reading-a-formal-result"></a>
<a id="81-find-its-exact-statement"></a>
<a id="82-follow-its-proof-and-evidence"></a>

Inspect the exact statement, caller domain and returned state. A local branch
lemma or heap-free model theorem does not establish a whole public API.
Statements about the abstract API model speak about the model, not about the C;
concrete execution needs its own refinement argument. Finite differential runs validate examples, not
universal claims. [Checking](checking/README.md) defines acceptance on a named
commit. [Progress](progress.md) records the target graph, the current evidence and the remaining
work.

---

## Project status and remaining work

[Documentation](README.md) · [API](spec/api/README.md) · [Checking](checking/README.md)

The project is finished when the safety results are accepted, in this order: `inflate` is
safe on every input; `deflate` is safe on every input, both with their call sequences; then
every other public function, including the gzip file interface and `inflateBack`. The safety
of `compress` and `uncompress` follows as compositions. The acceptance suite is green on commit
`bde170e9` (2026-11-15) with all 63 required goals registered. What remains is listed under
"Open" in [the claim](#the-claim).

Each public function has a safety goal and a functional goal; `tests/audit/public-api.json`
names both. The safety goals are in `ZlibF/Spec/Safety/` and the functional goals in
`ZlibF/Spec/Functional/`; the gz and `inflateBack` goals of both kinds are still in
`ZlibF/Spec/Public/`. The acceptance audit
requires the safety goals and the non-vacuity goals; a proved functional goal is audited in full,
and an unproved one fails nothing. [The split](design/safety-functional-split.md) gives the rules
and [safety](spec/safety.md#where-the-goals-are) the layout.

Current status, counts and the ordered list of remaining work are only in
[progress](progress.md). Earlier narrative checkpoints are kept, unchanged, in the
[overview changelog](history/overview-changelog.md); they are historical.

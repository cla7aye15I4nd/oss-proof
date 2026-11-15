# Proving one function

This page explains how a proof about one C function is built in this project, and how a proof
that does not go through is diagnosed. It is a description of method. It states no result of its
own; the [map](README.md) lists the theorems, and the component pages give the arguments.

The required goals are safety goals: a call returns without undefined behaviour or a memory
error, it terminates, it changes only the memory it is entitled to change, and it leaks nothing.
[Safety](../spec/safety.md) defines these claims. A functional goal says in addition what the
call computes. Functional goals are not required for the safety results. The method is the same
for both kinds, and this page says where a step is functional only.

## Fix the question first

A proof starts from three things that are fixed before it begins.

- **The C.** The pinned `zlib/` source with the patches of `patches/README.md` applied.
- **The translation.** `zlib/X.c` becomes `ZlibF/Zlib/X.c.lean`, statement by statement: each
  branch, read, write and conversion of the C has its counterpart, in the same order. Unsigned
  arithmetic wraps. Signed overflow, an invalid shift and an invalid pointer operation raise a
  fault. A statement is not replaced by an equivalent-looking one to make a proof easier. Order
  matters also for reads: reading a field before another write is not the same as using a value
  cached earlier.
- **The goal.** A Lean proposition in `ZlibF/Spec/` that names the caller's obligations, the
  result for each return value, the memory the call may write, and its allocations.

A public goal has to cover what `zlib.h` permits. Any premise narrower than `zlib.h` is written
in the docstring of the goal and has a row in [deviations](../deviations.md). An internal
theorem, about a function that only the library calls, may assume more, for example a table of
a certain shape; then every caller proves that premise at every call.

## Build the argument

```mermaid
flowchart TD
    Source["C source and fixed goal"] --> Hazards["every access, arithmetic step, call, exit and loop"]
    Hazards --> Local["local invariants and conditions"]
    Local --> Math["heap-free lemmas in ZlibF/Math"]
    Math --> Execution["execution proof: no fault, frame, ownership"]
    Local --> Execution
    Execution --> Init["callers and initialisation supply the premises"]
    Init --> Acceptance["registry and acceptance suite"]
```

What has to be shown at each kind of statement:

| Statement | To show |
| --- | --- |
| Read or write through a pointer | The object is live, the pointer has the right kind, and the offset is inside the object |
| Pointer arithmetic | The result is inside the object or one past its end |
| Shift, signed operation | The operands are in the range where C defines the result |
| Loop | An invariant, and a measure that falls on every round and is below the loop fuel |
| Call | The premises of the callee's theorem hold in the current state |

Two points are easy to miss.

**Loop fuel.** Every loop of the translation runs at most `2^64` rounds, and running out is the
fault `outOfFuel`. So a termination argument has to do more than show that the loop is finite
in the mathematical sense: it has to bound the number of rounds below the fuel.

**No callee contracts as assumptions.** A call is handled with a theorem that was proved about
the translated callee. A hypothesis of the form "the callee meets its specification" is not
allowed.

Arithmetic and combinatorial lemmas that need no heap are in `ZlibF/Math/`. A memory proof
applies them to the cells that the C reads and writes. A theorem about canonical codes, for
instance, serves the decoder only after a second theorem shows that `inflate_table` wrote those
entries into the heap.

## Diagnose a stuck proof

A proof that does not go through has one of four causes. None of them is assumed in advance.

| Cause | What the evidence looks like | What is done |
| --- | --- | --- |
| Proof technique | Statement and translation agree, and a lemma or an invariant clause is missing | The lemma is proved at the lowest layer that can state it. A stronger invariant is established at initialisation and kept by every operation |
| Wrong goal | A permitted execution contradicts the stated result | The counterexample is written down and kept as a regression under `tests/verification/regressions/`. The goal is corrected in a commit of its own |
| Translation bug | The translation differs from the C, for example in evaluation order or a conversion | The translation is corrected, and a differential test that catches the difference is added |
| zlib bug | The C itself faults on a permitted input | The input is built, the real C is run under a sanitizer, and the finding is recorded with its reproduction |

Narrowing the caller's domain solves none of these. A confirmed zlib bug can justify a minimal
patch that matches a fix submitted upstream. A limit of the model is not a zlib bug.

## One representation invariant

Each stateful component has one representation invariant: a property of the state that
initialisation establishes and every operation keeps. So it holds after every permitted series
of calls. A theorem that only *assumes* the invariant is not a sequence result; the sequence
theorem also proves that the invariant is reached.

| Component | Invariant | Module | Explained in |
| --- | --- | --- | --- |
| `inflate` | `InflateInv` | `ZlibF/Proof/inflate.c.invariant.lean` | [stream decoding](inflate.md#the-invariant) |
| `deflate` | `DInv`, with `HeaderInv` and `CallFacts` between calls | `ZlibF/Proof/deflate.c.universal-invariant.lean` | [stream compression](deflate.md#the-invariant) |
| gzip files | `GzInv` | `ZlibF/Proof/gz.inv-model.lean` | [gzip files](gzip.md) |
| callback decoder | `BackValid` between calls, `PInv` inside the dispatch loop | `ZlibF/Spec/Public/Back.lean`, `ZlibF/Proof/infback.c.safety-inv.lean` | [callback decoder](callbacks.md) |

The sequence goals state the invariant through a smaller public predicate, `StreamInvariant`
(`ZlibF/Spec/Public/Sequences.lean`). The proof invariants imply it.

Other modules use a small set of interface lemmas of an invariant and do not unfold its
definition. A change to the invariant then rebuilds its interface and not every module that
uses it.

An invariant that is too weak shows up as a counterexample, not as a hard proof. One example:
an earlier `deflate` invariant allowed the state `EXTRA_STATE` with a `NULL` `gz_header`
pointer, and a `deflate(Z_BLOCK)` run from such a state faulted. The repair was a new clause,
`HeaderInv.record`, which says the pointer is not `NULL` in the four header states that read
it, together with a proof that every reachable state has it (`reachable_inv_of`,
`ZlibF/Proof/deflate.c.universal-sequence-safety.lean`). That theorem takes one hypothesis,
`SequenceFacts`: three facts about one `deflate` call from a state with the invariant. The call
returns and keeps `DInv` and the owned blocks; it keeps `HeaderInv`; it keeps `CallFacts`.
The three facts are themselves proved: `sequence_facts`
(`ZlibF/Proof/public-deflate-copy.lean`) has no hypothesis, and `deflate_copy_public` in that
file applies `reachable_inv_of` to it. So the hypothesis is discharged, not assumed.

Functional only: bounds do not say which bytes are decoded. A functional proof adds a relation
between the state and the format, for the same executions, and shows how each step changes it.

## Initialisation, frame and ownership

**Initialisation** establishes the invariant on success and accounts for every allocation
failure. The default allocator does not zero memory, so the proof shows the write that
initialises each field that is read later. For pointer fields the model is weaker than C: a
pointer field in fresh memory reads as `NULL` without a fault. So a proof does not show that
a pointer field is written before it is read: that is **to confirm** by source review; see
[safety](../spec/safety.md#uninitialised-memory) and the [trusted base](../trusted-base.md).

**Uninitialised integers** have an arbitrary value, and a theorem holds for every such value.
`slide_hash`, for example, reads every slot of `prev`, written or not; a chain walk reaches
only slots that were written ([stream compression](deflate.md#hashing-chains-that-can-be-followed)).
The model gives each never-written cell one value for a whole run, so two reads of it agree. C
does not promise that. Whether any proof depends on such an agreement has not been checked
systematically; the row "One garbage value per cell" of [model limits](../model-limits.md)
records this limit.

**The frame** of a call is the memory it may change: the stream record, the blocks the stream
owns, and the caller ranges given to this call. Everything else is unchanged. Error returns have
their own effects: some write nothing, others have updated the state or produced output before
they return. A negative return code does not by itself mean an unchanged heap.

**Ownership** (`Owns`) tracks the live blocks that belong to a stream. An allocation adds a
block, and a free removes it exactly once. A copy creates new blocks and points the interior
pointers at them. A failed initialisation or copy frees every block it had obtained and leaves
earlier ownership as it was. Freedom from leaks follows from these steps over a whole history,
failure paths included.

```mermaid
flowchart LR
    Before["caller state, live blocks"] --> Init["init"]
    Init -->|success| Inv["invariant holds; stream owns its blocks"]
    Init -->|"failure: blocks freed"| Before
    Inv --> Call["API call"]
    Call -->|keeps| Inv
    Inv --> End["end"]
    End --> Released["live blocks as before init"]
```

## Non-vacuity and composition

An invariant that no state satisfies would make every "if the invariant holds" theorem true and
worthless. The initialisation theorem rules this out: it shows that the invariant is reached,
for the whole permitted parameter range. A top-level goal also has a non-vacuity theorem, which
exhibits a concrete heap and call that meet all its premises.

Calls are composed by induction over the permitted histories. Initialisation gives the
invariant. Each call gives the next invariant, its frame and its ownership step. Reset,
dictionaries, priming, recovery, copying and partly filled buffers are cases of that induction
wherever the API permits them.

## Check each proof interface

Before two proved parts are joined, the relation that the first establishes and the relation
that the second requires are compared, on the same heap and the same registers. Two theorems
with matching names are not thereby connected.

For a stream engine there are six such interfaces.

1. Initialisation establishes the invariant.
2. The entry of a call derives the local relation of the dispatch loop from it.
3. Each mode keeps that relation or establishes the exact relation of its exit.
4. Each round of the dispatch loop lowers a bounded rank.
5. Every exit restores the public accounting, the frame and the ownership relation. Direct
   returns and the common exit path each need this.
6. Every other permitted operation keeps the invariant.

Table construction has two different obligations. Index bounds and valid leaf shapes make a
lookup safe. Agreement with the canonical code makes a lookup mean the right symbol. A proof
that the writes land in the table gives neither.

## Structural facts used by several proofs

The component pages refer to these facts by number.

| ID | Fact | Used by | Explained in |
| --- | --- | --- | --- |
| F1 | The writes of table construction stay inside the table space, and a finished table has an entry at every index a reader can form | `inflate_table`, `inflate`, `inflate_fast` | [decode tables](inftrees.md#every-index-is-covered) |
| F2 | The counting offsets sort the coded symbols into distinct `work` slots, all written | `inflate_table` | [decode tables](inftrees.md#sorting-f2) |
| F3 | A match copy that reaches into the window has tested its distance against `whave` | `inflate`, `inflate_fast` | [fast decoding](inffast.md#match-copies-f3-and-f4) |
| F4 | In a window that is not full, `wnext = whave` | `updatewindow` | [stream decoding](inflate.md#window-shape-w), W.5 |
| F5 | A hash-chain walk reaches only inserted positions, through `prev` slots that were written | `longest_match` | [stream compression](deflate.md#inside-one-deflate-call) |
| F6 | The comparisons of a match, up to offset 258, are inside the window | `longest_match`, `deflate_rle` | [stream compression](deflate.md#inside-one-deflate-call) |
| F7 | The active heap, the stored nodes and the tree indices stay inside their arrays | `build_tree`, `pqdownheap` | [trees](trees.md#building-a-tree-f7) |
| F8 | The length repair finds a nonempty shorter class, and the count of the longest class does not go below zero | `gen_bitlen` | [trees](trees.md#limiting-the-code-lengths-f8) |
| F9 | Pending output never overwrites an unread symbol, and a whole block fits the shared buffer | the block writers | [trees](trees.md#the-overlay-lemma-f9) |

F3 and F4 do different work. F3 keeps a window read of a match inside the block. F4 lets
`updatewindow` keep `whave ≤ wsize`. The match copies do not need F4 for their bounds; it also
tells that the bytes they read were written, which is a reading that no safety theorem states.

## From checked to accepted

A proof of a public function is recorded with: the C function, the goal, its premises, the
invariant clauses used, the frame, the ownership changes, the callee theorems, the loop measures
and the mathematical lemmas.

Each newly proved public function gets proof mutants: the translation is changed in one place,
for example a dropped check, a changed return value, a wrong field or an index off by one, and
the proof of that function must then fail. A mutant that only breaks a lemma elsewhere does not
count.

The three levels, checked, registered and accepted, are defined in the
[glossary](../glossary.md#status). A small proof or a green build is not acceptance. See
[checking](../checking/README.md) and [verification policy](../anti-cheating.md).

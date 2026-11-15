# Glossary

This page defines the terms the other pages use, each once, in one or two sentences. The terms
are grouped: goals, status levels, the model, premises, the gzip file world, and checking. The
rules behind the status levels are in [checking](checking/README.md); the level of each result is
in [progress, Scope](progress.md#scope).

## Goals

**Goal.** A Lean proposition in `ZlibF/Spec/` about one C function or one call sequence. Its name
starts with `Goal.`. A goal is proved only by a theorem whose type is exactly the goal. **Target**
means the same thing.

**Safety goal.** A goal that says a call returns without a fault (no undefined behaviour, no
memory error, termination), writes only the memory it is allowed to (its frame), and leaks
nothing. Most are named `Goal.<function>_safety`.

**Functional goal.** A goal that says what the result of a call is: return values, output bytes,
the relation to the data format. Functional goals are not required for the safety results; the
ones already proved stay registered.

**Sequence goal.** A goal about every sequence of calls on one stream or handle, such as
`Goal.inflate_sequence_safety`. It says that the invariant holds after every history and that one
more call is safe.

**History.** The calls made so far on one stream or handle, starting at its init or open call,
with the caller's edits between calls. A sequence goal quantifies over every history, defined as
an inductive predicate (`StreamReachable`, `GzHistory`, `BackSafeReachable`). No earlier call's
specification is assumed.

**Reachable.** A stream is reachable when some history produces it: a successful init, then any
number of calls and caller edits. `StreamReachable` is the Lean predicate; a one-function safety
goal of a stream function holds on every reachable stream.

**Refusal.** A call that the C rejects with an error value, such as a call on a `NULL` or
inconsistent stream. The refusal goals (`Goal.inflate_refusal`, `Goal.deflate_refusal`,
`Goal.gz_refusal`) state the value and that the call changes nothing else; the one exception is a
refused copy, which clears the destination's state pointer.

**Non-vacuity goal.** A goal that shows the premises of other goals can be met: a concrete heap on
which init or open succeeds and gives a reachable stream or handle. Without it a sequence goal
could hold only because no history exists.

**Witness.** The concrete heap, and for gz the concrete file system, that a non-vacuity goal
exhibits, for example `witnessHeap` in `ZlibF/Spec/Public/Domains.lean`.

**Documented function.** A function that `zlib.h` declares before its comment "undocumented
functions (not part of the zlib API)". The ten functions after that comment are undocumented, and
a goal of their own is not required. One of them, `gzvprintf`, is still a call of the gz sequence
goal, because `gzprintf` goes through it.

**Required goal.** A goal the acceptance audit insists on: the safety goal of every documented
function of the target build, the listed sequence and refusal goals, and the non-vacuity goals.
`scripts/verification.py` computes the set from the manifest.

**Manifest.** The file `tests/audit/public-api.json`. For every exported function it names the
translated definition, the manual entry, the functional goal and the safety goal, and it lists
the undocumented functions and the non-vacuity goals.

**Registry.** One of three hand-edited lists under `tests/audit/`: `goals.txt` (every goal),
`theorems.txt` (the theorems that make up the result) and `proved-goals.txt` (the goals that have
a listed theorem of exactly their type).

**Counts.** 86 documented functions of the target build. 63 required goals: 52 one-function safety
goals, four sequence safety goals, three refusal goals and four non-vacuity goals; the 31 gz
functions share one sequence goal and the three `inflateBack` functions another. 239 goals in
`goals.txt`, of which 193 have a registered theorem; these include functional goals and internal
goals that are not required. The status page counts all 239.

**Model-only statement.** A theorem about the abstract API model in `ZlibF/Spec/Functional/`, not
about the translated C. It says nothing about the implementation until a separate theorem relates
the two.

## Status

**Checked.** The theorem is on the integration branch `dev` and the fast gate is green on that
commit: Lean's kernel has checked the proof. Every registered theorem is also checked. The status
page shows "checked" for a theorem that is checked and not registered.

**Registered.** The theorem is listed in `tests/audit/theorems.txt`, and its goal in
`tests/audit/proved-goals.txt`. The acceptance audit then requires the theorem's type to be
exactly the goal.

**Accepted.** The theorem is registered and the acceptance suite is green on a named commit. Only
an accepted result is reported as final, and always with that commit.

**Open.** A goal with no registered theorem of its type.

**Not planned.** A goal the project does not work on. It is never called proved.

## Model

**Fault.** The model's result for a run that does not return normally. Every undefined behaviour
the C can reach raises `Fault.ub`; a loop that uses up its fuel raises `Fault.outOfFuel`. A safety
theorem shows that no run raises either. One goal splits the two: the gz sequence goal proves that
no run raises `Fault.ub` in any world, and that the six reading calls return under a read budget.

**Fuel.** The bound on the iterations of one translated loop: `2^64` (`ZlibF/Runtime/Monad.lean`).
A theorem that concludes a normal return proves that the bound is never reached, which is the
project's meaning of termination.

**Heap.** The runtime model of memory in `ZlibF/Runtime/`: one table per kind of object (byte
arrays, word arrays, `z_stream` records, gzip headers, the three state records), the static
tables, and the allocator's bookkeeping.

**Block.** One allocation in the heap, named by a number. A block is **live** when some table holds
an object under its number. A freed number is never used again.

**Pointer.** `NULL`, or a reference to an object with an offset. The model has no value for an
uninitialised pointer: a pointer field in fresh memory reads as `NULL`, so a proof shows that a
pointer field was written before it is read ([trusted base](trusted-base.md), item 2).

**Well-formed heap.** Three conditions that most goals state about the heap a call starts on:
`Fresh` (no live block at or above the next block number), `Uniq` (a block number holds an object
of at most one table) and `LibraryGlobals` (the static tables are those of the selected build).
They describe the model's bookkeeping; a C caller cannot break them
([model limits](model-limits.md)).

**`ByteObjectsFit`.** Every byte array in the heap has fewer than `2^63` bytes, the LP64 limit
`PTRDIFF_MAX` on the size of one object. It does not bound total memory or the length of a stream.

**Allocation oracle.** The field `allocOk` of the heap: a function from the allocation attempt
number to success or failure. Goals quantify over every oracle, so they cover every pattern of
allocation failure.

**Garbage function.** The field `garbage` of the heap: it gives the value of each integer cell of
freshly allocated memory. Goals quantify over every garbage function, so they hold for every
content of uninitialised integers.

**Frame.** The set of blocks and byte ranges a call may write. "Writes only its frame" means that
every other live block is the same after the call (`Frame`, `BufferFrame`).

**Ledger.** The exact account of allocation in a goal's conclusion: which blocks the call created
and which it freed (`LiveChange`). "No leak" means that every block still live after the call was
live before it or is owned by the stream or handle.

**Owned.** A block is owned by a stream or handle when its state points to it: the state record,
the window, the hash tables, the pending buffer (`StreamOwned`, `GzOwned`).

**Representation invariant.** A property of a stream's state that every call preserves, for
example `DGood` for a deflate stream, `Good` for an inflate stream and `GzInv` for a gz handle.
The init or open function establishes it.

**Trusted base.** What a proof depends on and the kernel does not check. It has six items: the
Lean kernel with the audit programs; the runtime model; the hand translation; the selected source;
the build configuration with the model of the outside world; and the statements themselves. See
[trusted base](trusted-base.md).

**Pin.** The commit of upstream zlib that the `zlib/` submodule points to. The verified source is
the pin plus the files of `patches/`, applied in name order.

## Premises

**Precondition, premise.** What a theorem assumes about its inputs.

**Deviation.** A precondition narrower than `zlib.h` allows. It is written in the docstring of the
definition that states it and listed in [deviations](deviations.md).

**Separation precondition.** Caller memory regions do not overlap each other or the storage the
stream owns. A theorem states it as a hypothesis.

**`DefaultOrNull`.** The stream's `zalloc` and `zfree` are each `Z_NULL` or the library's default
function. A stream with a custom allocator is outside every goal.

**`StreamBuffers`.** The hypothesis on `next_in`, `avail_in`, `next_out` and `avail_out`. Each
range is NULL or readable (the output range writable), neither lies in the stream's own storage,
and the two ranges are separate. Every `inflate`, `deflate` and `deflateParams` call of a safety
goal assumes it.

## The gzip file world

**World.** The model's state of the operating system for the gz functions (`Fs` in
`ZlibF/Zlib/gzfs.lean`): files, open descriptors, `errno`, and two oracles, one for the OS calls
and one for `vsnprintf`. The gz safety
goal holds for every well-formed world.

**OS-call oracle.** Fields of the world that decide, for each `open`, `read`, `write`, `lseek` and
`close` call, whether it behaves as a regular file, fails with a chosen `errno`, or returns a
chosen result inside the POSIX contract of the call.

**Read budget.** The number of bytes a descriptor can still deliver (`readBudget`). The
termination of the six gz reading calls is proved for a budget below `2^61` bytes (`ReadsFinite`).

**Leaf.** A theorem about one function, or one group of calls, from which a sequence theorem is
assembled. `GzReadLeaves` in `ZlibF/Proof/gz.sequence-safety.lean` bundles the leaves of the gz
reading calls.

## Checking

**Differential test.** A run of the real C and of the Lean translation on the same input, compared.
It is evidence of fidelity, not proof.

**Proof mutant.** A deliberately wrong translation, such as a dropped check. A sound proof must
fail on it.

**Fast gate.** The jobs `build` and `no-sorry`. They run on every push and pull request.

**Acceptance suite.** Axiom gate, exact goal match, self tests, proof mutants and differential
tests. It runs nightly on `main` and on request.

**Axiom gate.** The part of the audit that walks every declaration a registered theorem depends
on and rejects any axiom other than `propext`, `Classical.choice` and `Quot.sound`.

**Exact goal match.** The part of the audit that requires the type of a registered theorem to be
exactly the goal it is listed for. A theorem with an extra premise does not count.

**Kernel replay.** The audit re-checks the compiled proofs in a fresh environment with Lean's
kernel, so that a result of an earlier build is not taken on trust.

**Coverage colour.** The colour of a node in the target graph of [progress](progress.md): gray,
blue, yellow or green, for how much of the input range a target's theorem covers
([input configurations](spec/input-configurations.md)). It is not a status level.

**Milestone.** `inflate` proved, `deflate` proved, a sequence goal proved, or about twenty newly
checked targets.

# Glossary

This page defines the terms the other pages use, each once, in one or two sentences. The terms
are grouped: goals, the two states of a result, the model, premises, the gzip file world, and
evidence. The state of each result is in [progress](progress.md).

## Goals

**Goal.** A Lean proposition about one C function or one call sequence. Its name
starts with `Goal.`. A goal is proved only by a theorem whose type is exactly the goal. **Target**
means the same thing.

**Safety goal.** A goal that says a call returns without a fault (no undefined behaviour, no
memory error, termination), writes only the memory it is allowed to (its frame), and leaks
nothing. Most are named `Goal.<function>_safety`.

**Functional goal.** A goal that says what the result of a call is: return values, output bytes,
the relation to the data format. The safety results do not depend on a functional goal that is
not done.

**Sequence goal.** A goal about every sequence of calls on one stream or handle, such as
`Goal.inflate_sequence_safety`. It says that the invariant holds after every history and that one
more call is safe.

**History.** The calls made so far on one stream or handle, starting at its init or open call,
with the caller's edits between calls. A sequence goal quantifies over every history, defined as
an inductive predicate (`StreamReachable`, `GzHistory`, `BackSafeReachable`).

**Reachable.** A stream is reachable when some history produces it: a successful init, then any
number of calls and caller edits. `StreamReachable` is the Lean predicate; a one-function safety
goal of a stream function holds on every reachable stream.

**Refusal.** A call that the C rejects with an error value, such as a call on a `NULL` or
inconsistent stream. A refusal clause states the value returned and what the call may change.
The safety goal of a function has one, beside its clause for a valid call, for every documented
inflate and deflate stream function except the four init functions, for `inflateCopy` and
`deflateCopy`, for the gzip file functions
that take a handle, and for `inflateBack` and `inflateBackEnd`; three refusal goals
(`Goal.inflate_refusal`, `Goal.deflate_refusal`, `Goal.gz_refusal`) state the refusals of several
functions at once. Which streams count as refused, and the values and changes, are in
[deviations](deviations.md#note-2-refused-streams).

**Non-vacuity goal.** A goal that shows the premises of other goals can be met: a concrete heap on
which init or open succeeds and gives a reachable stream or handle. Without it a sequence goal
could hold only because no history exists.

**Witness.** The concrete heap, and for gz the concrete file system, that a non-vacuity goal
exhibits, for example `witnessHeap`.

**Documented function.** A function that `zlib.h` declares before its comment "undocumented
functions (not part of the zlib API)". The ten functions after that comment are undocumented, and
a goal of their own is not planned. The exception is `gzvprintf`: `gzprintf` goes through it, so
it has the safety goal `Goal.gzvprintf_safety` and it is a call of the gz sequence goal.

**Kinds of safety goal.** The target build has 86 documented functions. The safety results
consist of goals of four kinds: one-function safety goals, sequence safety goals, refusal goals
and non-vacuity goals. There is one one-function safety goal for each documented function and one
for `gzvprintf`; for `compressBound` and `compressBound_z`, which are pure, the functional goal
stands for the safety goal.

**Model-only statement.** A theorem about the abstract API model, not
about the translated C. It says nothing about the implementation until a separate theorem relates
the two.

## Status

A result, a goal or a function has one of two states.

**Done.** A Lean theorem whose statement is exactly the goal exists and passes every check of the
project. [What a done result rests on](checking/README.md) says what the checks are.

**Not done.** No such theorem exists. A goal of which only a part has a theorem is not done; a
page may say in plain words which part has one.

**Not planned.** Said in addition to "not done" of a goal the project does not work on.

## Model

**Fault.** The model's result for a run that does not return normally. Every undefined behaviour
the C can reach raises `Fault.ub`; a loop that uses up its fuel raises `Fault.outOfFuel`. A safety
theorem shows that no run raises either. The gz goals split the two: the gz sequence goal, and the
goals of the six reading calls, prove that no run raises `Fault.ub` in any world, and that the six
reading calls return under a read budget.

**Fuel.** The bound on the iterations of one translated loop: `2^64`.
A theorem that concludes a normal return proves that the bound is never reached, which is the
project's meaning of termination.

**Heap.** The runtime model of memory: one table per kind of object (byte
arrays, word arrays, `z_stream` records, gzip headers, the three state records), the static
tables, and the allocator's bookkeeping.

**Block.** One allocation in the heap, named by a number. A block is **live** when some table holds
an object under its number. A freed number is never used again.

**Pointer.** `NULL`, or a reference to an object with an offset. The model has no value for an
uninitialised pointer: a pointer field in fresh memory reads as `NULL`, so a missing write does
not show. That a pointer field is written before it is read is not a theorem; it is **to
confirm** by source review ([trusted base](trusted-base.md), item 2).

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

**Result cell.** The variable that a pointer argument names and the C stores a result through,
such as `*destLen` or `*dictLength`. For eight public functions the translation takes the cell as
a value and not as memory, so their goals say nothing about the cell's memory: the four
`compress*` functions, the two `GetDictionary` functions, `deflatePending` and `deflateUsed`
([deviations](deviations.md#stream-calls-inflate-and-deflate), rows "Result cells" and
"Whole-buffer compression").

**Library heap.** The phrase the API entries use for the well-formed heap defined above
([contracts](spec/api/contracts.md#reading-a-proof-goals-paragraph)).

**Representation invariant.** A property of a stream's state that every call preserves, for
example `DGood` for a deflate stream, `Good` for an inflate stream and `GzInv` for a gz handle.
The init or open function establishes it.

**Trusted base.** What a proof depends on and the kernel does not check. It has six items: the
Lean kernel with the programs that check axioms and statements; the runtime model; the hand translation; the selected source;
the build configuration with the model of the outside world; and the statements themselves. See
[trusted base](trusted-base.md).

**Pin.** The commit of upstream zlib that the proofs are about. The verified source is the pin
plus the [patches](../patches/README.md), applied in name order.

**Normalisation.** One of four ways in which a translation may differ from a literal
statement-by-statement copy of the C, each with the same behaviour as the C.
[Translation](design/translation.md) lists them with an example of each. The translations also
contain at least six further forms that the four do not cover
([trusted base](trusted-base.md), item 3). A difference that changes what the C computes is a
translation bug.

## Premises

**Precondition, premise.** What a theorem assumes about its inputs.

**Deviation.** A precondition narrower than `zlib.h` allows. It is written in the docstring of the
definition that states it and listed in [deviations](deviations.md).

**Separation precondition.** Caller memory regions do not overlap each other or the storage the
stream owns. A theorem states it as a hypothesis.

**Caller edit.** What the caller does to a stream between two calls of a history: it changes
`next_in`, `avail_in`, `next_out` or `avail_out` of the `z_stream`, or memory the stream does not
own. `Rebuffer` is the Lean predicate; the gz form is `GzCallerFrame`. A history in which the
caller changes anything else of the stream is outside the sequence goals
([deviations](deviations.md#stream-calls-inflate-and-deflate), row "Caller edits between calls").

**Focused contract.** An entry of the API manual whose Pre describes ordinary correct use and is
on purpose narrower than what the function accepts
([contracts](spec/api/contracts.md#entry-structure)).

**`DefaultOrNull`.** The stream's `zalloc` and `zfree` are each `Z_NULL` or the library's default
function. A stream with a custom allocator is outside every goal.

**`StreamBuffers`.** The hypothesis on `next_in`, `avail_in`, `next_out` and `avail_out`. Each
range is NULL or readable (the output range writable), neither lies in the stream's own storage,
and the two ranges are separate. Every `inflate`, `deflate` and `deflateParams` call of a safety
goal assumes it.

## The gzip file world

**World.** The model's state of the operating system for the gz functions (`Fs`): files, open descriptors, `errno`, and two oracles, one for the OS calls
and one for `vsnprintf`. The gz safety
goal holds for every well-formed world.

**OS-call oracle.** Fields of the world that decide, for each `open`, `read`, `write`, `lseek` and
`close` call, whether it behaves as a regular file, fails with a chosen `errno`, or returns a
chosen result inside the POSIX contract of the call.

**Read budget.** The number of bytes a descriptor can still deliver (`readBudget`). The
termination of the six gz reading calls is proved for a budget below `2^61` bytes (`ReadsFinite`).

## Checking

**Differential test.** A run of the real C and of the Lean translation on the same input, compared.
It is evidence of fidelity, not proof.

**Sanitizer reproduction.** A small C program that makes the real zlib show an issue when it is
built with AddressSanitizer or UndefinedBehaviorSanitizer. It is evidence about one run of the
real C, not proof.

**Proof mutant.** A deliberately wrong translation, such as a dropped check. Mutated translations
were checked to break the proofs: a proof that still passed on one would not depend on the
translation. This is additional evidence, not part of what "done" means.

**Allowed axioms.** `propext`, `Classical.choice` and `Quot.sound`, the three standard axioms of
Lean. A done result depends on no other axiom.

**Exact statement.** The type of the theorem behind a done result is exactly the goal. A theorem
with an extra premise does not count.

**Kernel replay.** The compiled proofs are checked again by Lean's kernel in a fresh environment,
so that the result of an earlier build is not taken on trust.

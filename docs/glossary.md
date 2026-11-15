# Glossary

Each term is defined once, in the order a reader needs it. The rules behind the status words are
in [checking](checking/README.md); the current status is in [progress](progress.md#scope).

## Goals

**Goal.** A Lean proposition in `ZlibF/Spec/` about one C function or one call sequence. Its name
starts with `Goal.`. A goal is proved only by a theorem whose type is exactly the goal. **Target**
means the same thing.

**Safety goal.** A goal that says a call returns without a fault (no undefined behaviour, no
memory error, termination), writes only its frame, and leaks nothing. Most are named
`Goal.<function>_safety`.

**Functional goal.** A goal that says what the result of a call is: return values, output bytes,
the relation to the data format. Functional goals are not planned since 2026-11-11; the proved
ones stay registered.

**Sequence goal.** A goal about every sequence of calls on one stream or handle, such as
`Goal.inflate_sequence_safety`. It says that the invariant holds after every history and that one
more call is safe.

**History.** The calls made so far on one stream or handle, starting at its init or open call,
with the caller's edits between calls. A sequence goal quantifies over every history, defined as
an inductive predicate (`StreamReachable`, `GzHistory`, `BackSafeReachable`). No earlier call's
specification is assumed.

**Refusal.** A call that the C rejects with an error value, such as a call on a `NULL` or
inconsistent stream. The refusal goals (`Goal.inflate_refusal`, `Goal.deflate_refusal`,
`Goal.gz_refusal`) state the value and that the call changes nothing else; the one exception is a
refused copy, which clears the destination's state pointer.

**Non-vacuity goal.** A goal that shows the premises of other goals can be met: a concrete heap on
which init or open succeeds and gives a reachable stream or handle. Without it a sequence goal
could hold only because no history exists.

**Required goal.** A goal the acceptance audit insists on: the safety goal of every documented
function of the target build, and the non-vacuity goals. `tests/audit/public-api.json` fixes the
set.

## Status

**Checked.** The theorem is on `dev` and the fast gate is green on that commit. Lean's kernel has
checked the proof. `AGENTS.md` words this level with `main`; in practice day-to-day work is
merged to `dev`, and `main` receives `dev` at a milestone.

**Registered.** The theorem is listed in `tests/audit/theorems.txt`, and its goal in
`tests/audit/proved-goals.txt`.

**Accepted.** The theorem is registered and the acceptance suite is green on a named commit. Only
an accepted result is reported as final.

**Open.** A goal with no registered theorem of its type.

**Not planned.** A goal the project does not work on. It is never called proved.

## Model

**Fault.** The model's result for a run that does not return normally. Every undefined behaviour
the C can reach raises `Fault.ub`; an exhausted loop bound raises `Fault.outOfFuel`. A safety
theorem shows that no run raises either, except where it states otherwise.

**Heap, pointer.** The runtime model of memory in `ZlibF/Runtime/`. A pointer in fresh memory is
NULL. A proof shows that a pointer field was written before it is read.

**Trusted base.** What a proof depends on and the kernel does not check: the runtime, the hand
translation, the selected source, the model of the outside world. See [trusted base](trusted-base.md).

**Precondition, premise.** What a theorem assumes about its inputs.

**Deviation.** A precondition narrower than `zlib.h` allows. It is written in the theorem's
docstring and listed in [deviations](deviations.md).

**Separation precondition.** Caller memory regions do not overlap each other or the storage the
stream owns. A theorem states it as a hypothesis.

**Representation invariant.** A property of a stream's state that every call preserves, for
example `DGood` for a deflate stream, `Good` for an inflate stream and `GzInv` for a gz handle.
The init or open function establishes it.

**`StreamBuffers`.** The hypothesis on `next_in`, `avail_in`, `next_out` and `avail_out`. Each
range is NULL or readable (the output range writable), neither lies in the stream's own storage,
and the two ranges are separate. Every `inflate`, `deflate` and `deflateParams` call of a safety
goal assumes it.

## Checking

**Differential test.** A run of the real C and of the Lean translation on the same input, compared.
It is evidence of fidelity, not proof.

**Proof mutant.** A deliberately wrong translation, such as a dropped check. A sound proof must
fail on it.

**Fast gate.** The jobs `build` and `no-sorry`. They run on every push and pull request.

**Acceptance suite.** Axiom gate, exact goal match, self tests, proof mutants and differential
tests. It runs nightly on `main` and on request.

**Milestone.** `inflate` proved, `deflate` proved, a sequence goal proved, or about twenty newly
checked targets.

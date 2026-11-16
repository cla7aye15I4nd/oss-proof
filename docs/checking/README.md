# What a done result rests on

The [status page](../progress.md) calls a result done when a Lean theorem whose statement is
exactly the goal exists and passes every check of the project. This page says what that amounts
to: four things hold for a done result, and none of them is a proof that the Lean text describes
the C correctly.

## What holds for a done result

1. **The Lean kernel checked the proof.** The kernel is the small program at the core of Lean
   that accepts or rejects a proof term. No proof uses `sorry`, `native_decide`, or another
   construct that takes a result on trust instead of having the kernel check it.
2. **Only the three standard axioms are used.** The proof and everything it depends on use no
   axiom other than `propext`, `Classical.choice` and `Quot.sound`. No axiom was added for this
   project.
3. **The type of the theorem is exactly the goal.** A goal is a Lean definition of a
   proposition, written apart from the proofs. The theorem that makes it done has that
   proposition as its type, not a weaker or a nearby one. A narrower lemma does not count.
4. **The premises are written in the statement.** A theorem states every premise it uses. Where
   a premise is narrower than `zlib.h` allows, [deviations](../deviations.md) lists it.

## Evidence that is not proof

The theorems are about a Lean translation of the C, made by hand, statement by statement.
Differential tests compare the translation with the real C on many inputs, with and without
sanitizers. They are evidence of fidelity, not proof.

## What is trusted

That a done result says something true of the real zlib also depends on things the kernel does
not check: the Lean kernel itself, the runtime model of memory and faults, the hand translation,
the selected source with its patches, the model of the outside world, and the statements of the
goals. [Trusted base](../trusted-base.md) lists them with the reason each is believed.
[Model limits](../model-limits.md) lists the places where the model could differ from C.

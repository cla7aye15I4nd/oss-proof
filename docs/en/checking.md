# What a done result rests on

The [status page](progress.md) calls a result done when a Lean theorem whose statement is
exactly the goal exists and passes every check of the project. This page says what that amounts
to: four things hold for a done result, every change to the repository is checked for them, and
none of them is a proof that the Lean text describes the C correctly.

## What holds for a done result

1. **The Lean kernel checked the proof.** The kernel is the small program at the core of Lean
   that accepts or rejects a proof term. It checks every proof when the library is built. No
   proof uses `sorry`, `native_decide`, or another construct that takes a result on trust
   instead of having the kernel check it.
2. **Only the three standard axioms are used.** The proof and everything it depends on use no
   axiom other than `propext`, `Classical.choice` and `Quot.sound`. No axiom was added for this
   project.
3. **The type of the theorem is exactly the goal.** A goal is a Lean definition of a
   proposition, written apart from the proofs. The theorem that makes it done has that
   proposition as its type, not a weaker or a nearby one. A narrower lemma does not count.
4. **The premises are written in the statement.** A theorem states every premise it uses. Where
   a premise is narrower than `zlib.h` allows, [deviations](deviations.md) lists it.

## What every change is checked for

A change to the repository is accepted only when all of this holds for the changed sources.

- **The whole library builds.** The kernel checks every proof. A warning is an error, so a
  `sorry` (an admitted, unproved step) fails the build.
- **The results agree with their goals.** In the same build, a check goes through the list of
  results. The theorem of each done goal has exactly the goal as its type. It depends on no
  axiom beyond the three, and the check follows everything the theorem depends on. Every goal
  stated in the library is either proved or listed as not done, and every required goal is
  proved. The check is itself tested on small examples: it rejects a wrong type, an extra
  axiom, an unlisted goal and a required goal without a theorem.
- **No function is left out.** The required goals are compared with the pinned `zlib.h`: the
  safety goal of every documented function of the target build is among them.
- **Nothing bypasses the kernel.** The sources contain no forbidden construct and set no option
  that switches the kernel check off or weakens it. The compiled library is examined as well:
  no declaration in it is an axiom or is `opaque`, `extern` or `implemented_by`, none uses an
  axiom outside the three, and none is `unsafe` or `partial` apart from listed auxiliary
  declarations that the compiler generates.
- **The patches apply** to the pinned zlib.
- **The translation still agrees with the C on the test inputs.** When the translation, the
  runtime, the patches or the tests change, the differential tests run again, with the C built
  under AddressSanitizer and UndefinedBehaviorSanitizer.

A build reuses compiled modules only from builds of sources that were already accepted, never
from a proposed change.

One check is not made on every change: an independent replay, in which the kernel checks the
compiled results and everything they depend on again in a fresh environment. A reader can run
it with `lake env leanchecker --fresh ZlibF.Results`.

## Evidence that is not proof

The theorems are about a Lean translation of the C, made by hand, statement by statement.
Differential tests compare the translation with the real C on many inputs, with the C built
under AddressSanitizer and UndefinedBehaviorSanitizer. They are evidence of fidelity, not proof.

## What is trusted

That a done result says something true of the real zlib also depends on things the kernel does
not check: the Lean kernel itself, the runtime model of memory and faults, the hand translation,
the selected source with its patches, the model of the outside world, and the statements of the
goals. [Trusted base](trusted-base.md) lists them with the reason each is believed.
[Model limits](model-limits.md) lists the places where the model could differ from C.

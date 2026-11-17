# Why a green build is not enough

This page says why a build in which every proof compiles could still be worthless, and what
protects the results of this project against each way that could happen. The main point: Lean's
kernel checks a proof against the type of its theorem. It does not check that the type is the
statement the project claims. A result is called done only when more than the build holds.

The [trusted base](trusted-base.md) lists what no program checks at all.
[What a done result rests on](checking.md) is the short form of this page.

## What could go wrong, and what stands against it

| What could go wrong | Protection |
| --- | --- |
| A proof of a weaker statement is presented as the goal | **Exact statement.** A goal is proved only by a theorem whose type is exactly the goal. An extra premise, a similar name or a theorem about the abstract model does not count. |
| A proof rests on an unsupported assumption | **Allowed axioms only.** `propext`, `Classical.choice` and `Quot.sound`, the three standard axioms of Lean, are allowed. Every declaration that a theorem depends on is examined, and any other axiom is rejected. |
| A proof uses a construct that bypasses the kernel | **No forbidden construct.** The sources contain no `sorry`, `native_decide`, `bv_decide`, `axiom`, `implemented_by`, `extern`, `unsafe`, `partial` or `opaque`. |
| A proof term the kernel never saw | The kernel checks every proof when the library is built, a warning fails the build, and the sources may set no option that switches the kernel check off or weakens it. A build reuses compiled modules only from builds of sources that were already accepted, never from a proposed change. An independent replay of the compiled results in a fresh environment is a command a reader can run (`lake env leanchecker --fresh ZlibF.Results`); it is not run on every change. |
| A function of `zlib.h` is quietly left out | The list of functions is compared with the pinned `zlib.h`. Every documented function of the target build must have a safety goal with a theorem, and so must the sequence goals, the refusal goals and the non-vacuity goals. |
| An invariant that no heap satisfies, so that a theorem holds of nothing | The non-vacuity goals: init, or open, succeeds on a concrete heap and gives a stream or handle the other goals speak about. |
| A proof assumes the behaviour of a function it calls | No result assumes the contract of a library function that is not itself proved. Each callee has a theorem about its own translation. |
| A translation that differs from the C | Differential tests run the real C and the translation on the same inputs, with the C built under AddressSanitizer and UndefinedBehaviorSanitizer. They are evidence of fidelity, not proof. |

## What no program checks

No tool decides whether a goal says what it should, or whether the runtime model and the
translation mean what the C means. A statement could be changed to something easier together
with its proof, and every protection above would still hold for the changed statement:

- the goal is still proved only by a theorem of exactly its type, whatever that type is;
- only the three axioms are still allowed;
- differential tests still run against the translation as it is.

None of these detects a goal that was made easier. So a reader who relies on a result reads the
statement of its goal, and the definitions it names. The rule the project follows is: a statement
is never weakened, a domain never narrowed and a translation never changed to make a proof go
through. A statement is changed only when there is evidence that it was wrong, such as a
counterexample.

## What counts as a proof

- The type of the theorem is exactly the goal.
- The init function is proved to establish the invariant on the whole permitted domain. A
  concrete witness is added for a top-level theorem; it supplements the universal statement and
  never replaces it.
- No result assumes the contract of a library function that is not itself proved.
- An invariant that no permitted heap satisfies cannot justify a public claim: the non-vacuity
  goals rule this out.

The compiler generates some auxiliary declarations that are marked `unsafe` or `partial`, for
example `._unsafe_rec`. These are exempt from the rule on forbidden constructs. Any other
declaration of a forbidden kind is rejected.

## Human review

Review decides whether the contracts are complete, whether the runtime represents the semantics
of the selected C, and whether the translation matches the source. Kernel checking of proof
bodies cannot replace that. The objects of review are the statements, the preconditions, the
runtime, the [deviations](deviations.md) and the [patches](../../patches/README.md).

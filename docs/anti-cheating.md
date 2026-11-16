# Verification policy: fixed questions, editable proofs

This page says why a green build can still be worthless, which ways of cheating the acceptance
suite stops, and which it does not. The main point: a proof may change, but the question it
answers must not change to make the proof pass. The kernel checks a proof against its type; the
acceptance suite also checks that the type is exactly a registered goal.

A successful build is not acceptance. It makes a theorem checked. Only the acceptance suite,
green on a named commit, makes it accepted ([glossary](glossary.md#status)).
[Progress](progress.md#scope) records the level of each result. The
[checking guide](checking/README.md) says what each check establishes; the
[trusted base](trusted-base.md) lists the judgments that no program makes.

## What the acceptance suite defends against

| Attack | Defence |
| --- | --- |
| A proof of a weaker statement presented as the goal | A goal is proved only by a theorem whose type is exactly the goal. An extra premise, a similar name or an abstract-model theorem does not count. |
| An unsupported assumption | Only `propext`, `Classical.choice` and `Quot.sound` are allowed. The declaration audit rejects other axioms and forbidden declaration kinds in the import closure. The audit fails when a registry file is missing or empty or lists a name twice. |
| A proof term the kernel never saw | Compiled declarations are replayed in a fresh environment of the same Lean kernel. A cached build trace is not a certificate. |
| An unregistered goal | Every standalone `Goal` proposition in the audited closure must be registered. The inventory in `tests/audit/public-api.json` is checked against the pinned header, the translated entries and the manual sections. |
| A required goal left out or quietly dropped | The required goals are computed from `tests/audit/public-api.json`: the safety goal of every documented function of the target build, the listed safety goals, and the non-vacuity goals. The auditor fails when one of them is open. A registered theorem or a proved goal may not disappear without an entry and a reason in `tests/audit/registry-removals.json`. |
| A proof that does not depend on the translation | Not the acceptance suite. The defence is the proof mutants, which are additional evidence and run only on request: a deliberately wrong translation, such as a dropped check, must fail to check, with the error in that function's proof. The audit checks that every proved required goal has mutant rows; it does not run them ([below](#proof-mutants)). |
| A translation that differs from the C | Differential tests run the real C and the translation on the same inputs, with and without sanitisers. They are evidence of fidelity, not proof. |
| `sorry` and the other forbidden constructs | The fast gate rejects them on every push. |

## What it does not defend against

There are no lock files and no approved baseline. Definitions, translations, specifications and
statements are tracked by git alone. A silent change to a trusted definition, to the translation,
to a specification or to the statement of a goal, in the same commit as a proof that uses it, is
not rejected by any tool. It is visible only in git history and in review of the diff.

What still holds in that case:

- the goal is still proved only by a theorem of exactly its type, whatever that type is after
  the change;
- the axiom gate still applies;
- differential tests still run against the changed translation, and so do the proof mutants
  when a mutant run is requested.

None of these detects a goal that was changed to be easier. A reader who relies on a result
compares the statement of its goal with the earlier versions in git. The rules for correcting a
statement are in `AGENTS.md`: a correction needs evidence, its own commit and a regression under
`tests/verification/regressions/`. A statement is never weakened, a domain never narrowed and a
translation never changed to make a proof go through.

## What counts as a proof

- The type of the registered theorem is exactly the goal constant.
- The init function is proved to establish the invariant on the whole permitted domain. A
  concrete witness is added for a top-level theorem; it supplements the universal statement and
  never replaces it.
- No result assumes the contract of a library function that is not itself proved.
- An invariant that no permitted heap satisfies cannot justify a public claim: the non-vacuity
  goals rule this out.

The compiler generates some auxiliary declarations that are marked `unsafe` or `partial`, for
example `._unsafe_rec`. They are listed in `tests/audit/compiler-helpers.txt` and exempted. Any
other declaration of a forbidden kind is rejected.

## Proof mutants

Proof mutants are additional evidence, not part of acceptance. A full run takes several hours, so
it starts only on request (the manual trigger of the `lean` workflow with its `mutants` option).
A run is reported separately, with its commit, and it gates no merge, no acceptance and no
milestone. What the audit, which is part of acceptance, does check is that the rows exist.

Every proved required goal needs mutant rows, in one of two forms: its own key in
`tests/audit/public-mutants.json`, or an entry in the table `PINNED_EVIDENCE` of
`scripts/verification.py`, which names the mutant lists and the keyed goals that carry the
evidence for a goal without a key of its own, such as a sequence goal.

Each mutation of a keyed goal changes the translated body of that function and keeps its
signature. The audit fails when the record is missing, when the mutation changes another
function or only a specification, or when its row in the mutant list carries a flag that
exempts it from being killed. In a mutant run, a fresh-kernel
replay substitutes only the mutated declarations into the dependency closure of the original
registered proof. That proof must check before the mutation and fail after it. A failure only in
an unrelated or stronger theorem does not count.

That a proof is sensitive to a change does not show that the change alters behaviour. An
equivalent rewrite can break a particular proof term, so a mutation should change behaviour on
an allowed input. The command `verification.py mutants` runs three groups of lists: the
API-boundary list, every list that a key of `public-mutants.json` refers to, and the semantic
safety lists (`SAFETY_MUTANT_LISTS` in `scripts/verification.py`). A missing or empty safety
list is an error. The [mutant guide](checking/proof-mutants.md) explains the checks.

## Human review

Review decides whether the contracts are complete, whether the runtime represents the semantics
of the selected C, and whether the translation matches the source. Kernel checking of proof
bodies cannot replace that. The objects of review are the statements, the preconditions, the
runtime, the deviations and the patches. An obstacle in the audit is reported, not bypassed.

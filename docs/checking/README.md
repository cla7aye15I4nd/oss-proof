# Checking a verification claim

A green build says that the modules compile. It does not say that zlib is verified.
This page says what each check runs, what it establishes and where its limit is.
To run the checks, read [contributing](contributing.md). The current status and the planned
scope are on the [results page](../progress.md#scope).

## Two levels

- **Checked.** The theorem is on `dev`, and the fast gate is green on that commit. Lean's kernel
  has checked the proof. Day-to-day work is merged at this level.
- **Accepted.** The theorem is also listed in `tests/audit/theorems.txt`, and the acceptance suite
  is green on a commit you name. Only an accepted result may be reported as final.

## Two sets of checks

Both sets are jobs of the workflow `.github/workflows/lean.yml`.

```mermaid
flowchart LR
    P["Push to dev"] --> G["Fast gate"]
    G --> C["Checked"]
    C --> M["Milestone batch: register, mutants, progress view"]
    M --> A["Acceptance suite on a named commit"]
    A --> R["Accepted; main receives dev"]
```

### Fast gate

It runs on every push to `dev` or `main` and on every pull request. It is the only gate for merging.

| Job | Step | What fails it |
| --- | --- | --- |
| `build` | Build the library and the audit tools | A module of `ZlibF` that does not compile. A proof that the kernel rejects. |
| `build` | Build the differential drivers | A driver of `tests/list.txt` that does not compile against the translation. The drivers are built here and run only in the acceptance suite. |
| `build` | Forbidden constructs | `native_decide`, `bv_decide`, `implemented_by`, `axiom`, `partial`, `unsafe`, `opaque` or `extern` in the source text of `ZlibF`. |
| `build` | No unsafe or partial declaration (`tests/audit/PartialCheck.lean`) | A compiled declaration marked unsafe or partial that is not a listed compiler helper (`tests/audit/compiler-helpers.txt`). |
| `build` | Patches apply | A file of `patches/` that does not apply to a copy of the pinned `zlib/`. |
| `no-sorry` | `scripts/check-sorry.sh` | A `sorry` in the Lean sources. |
| `no-sorry` | `scripts/check-strlit.py` | A string literal of a translation that is missing from the runtime's string table. |
| `no-sorry` | `scripts/check-spec-layers.py` | A module under `ZlibF/Spec/Safety/` or `ZlibF/Spec/Public/` that imports, even transitively, a functional specification (`ZlibF/Spec/Functional/` or the old paths `ZlibF/Spec/Api*`, `ZlibF/Spec/Format*`). The script holds a list of the edges still allowed; the list may only shrink. |

The fast gate does not read the registries. A green fast gate says nothing about which goals are proved.

### Acceptance suite

It runs every night on `main` and on request (the manual trigger of the `lean` workflow, on any
branch). It has two required results, `audit` and `difftest`. Each one fails when any of its
workers fails, is skipped or is cancelled.

| Result | Worker | What it runs |
| --- | --- | --- |
| `audit` | `audit_core` | `python3 scripts/verification.py specs`: the inventory, a fresh-kernel recheck of the whole library, the declaration audit and the registry rules below. Then the tests of the auditor and of the scripts under `tests/verification/`, and `scripts/proof-progress.py --check`, which fails on a stale progress view. |
| `audit` | `audit_selftest`, two shards | `tests/audit/selftest.sh`: each file of `tests/audit/cheats/` (a `sorry`, an axiom, `native_decide`, `implemented_by`, an opaque constant, a partial or unsafe definition, a classical trick) must be rejected by the auditor. |
| `audit` | `audit_mutants`, twenty shards | `python3 scripts/verification.py mutants --shard-count 20 --shard-index N`: the [proof mutants](proof-mutants.md). |
| `difftest` | `diff_core` | `tests/run.sh`: the translation and the patched C on the same inputs. Then the same with the C built under AddressSanitizer and UndefinedBehaviorSanitizer. |
| `difftest` | `diff_harness`, eight shards | `tests/selftest.sh`: a mutated translation must make the differential test report a difference. |

A red nightly run is fixed before new acceptance work. It does not block proof work.
Acceptance work is done in batches at a milestone, not for each change.

**Pre-check with reused verdicts.** The manual trigger has an input `reuse`. With it, the mutant
shards skip each proof mutant whose inputs are byte for byte those of an execution that already
passed, and print how many units ran and how many were reused. The result then reports as
`audit (pre-check, reused verdicts)`. It is a faster check for `dev` and for branches. It is not
acceptance: an accepted result needs a full run, without the input, on the commit you name. The
nightly run is always full. [Proof mutants](proof-mutants.md#verdict-reuse) says what the key covers.

`python3 scripts/verification.py final` runs the whole suite in one process from a clean build, with
every mutant list in strict mode, and prints the commit. The workflow `verification-final` starts it
by hand for a named commit. The nightly suite does not run it.

## What `verification.py specs` decides

The script reads four registries under `tests/audit/`. [Public goals](goals.md) describes them.

1. **Inventory.** The functions of `public-api.json` are exactly the exported functions of the
   pinned `zlib.h`. Each has a manual section, a translated entry and a functional goal. Each
   documented function has a safety goal. The goal groups of the manifest equal the lists pinned in
   the script. The source pin equals the submodule commit, and the submodule has no local change.
2. **Fresh kernel.** `leanchecker --fresh ZlibF` rechecks the compiled proof terms.
3. **Declaration audit.** The auditor (`tests/audit/Audit.lean`) reads the compiled modules. It
   rejects an axiom, an opaque constant, `implemented_by`, `extern`, and an unsafe or partial
   declaration outside the listed compiler helpers. Every definition and theorem may depend only on
   `propext`, `Classical.choice` and `Quot.sound`. Every theorem of `theorems.txt` exists, is a
   theorem and has a doc string. Every `Goal.*` proposition is listed in `goals.txt`. A goal is
   PROVED only when a listed theorem has exactly the goal as its type.
4. **Registries agree.** `proved-goals.txt` equals the set of goals the auditor finds PROVED. Every
   required goal is PROVED or listed in `open_safety` of the manifest; a goal in `open_safety` is
   not PROVED.
5. **Shrink-only rules.** Along the commit chain, no registered theorem, proved goal, mutant
   reference or frozen mutant row disappears without a reasoned entry in
   `registry-removals.json`. A goal closed once is not open again. [Public goals](goals.md#shrink-only-rules)
   gives the rules.
6. **Mutant evidence.** Every proved goal of one public function has function mutants. Every
   proved required goal has a key in `public-mutants.json` or pinned evidence
   ([proof mutants](proof-mutants.md#which-goals-need-which-evidence)).

## What the checks establish

| Check | Evidence and limit |
| --- | --- |
| Kernel replay and axiom audit | Check the proof terms and dependencies. Only `propext`, `Classical.choice` and `Quot.sound` are allowed. A correct proof can still answer an incomplete question. |
| Exact goal matching | A registered theorem must have the fixed target as its type. Extra premises, a similar name or an abstract-model theorem do not count. Whether the target says enough is decided by review. |
| No-placeholder check | Rejects `sorry` and the other forbidden constructs listed in `AGENTS.md`. |
| Differential tests | Compare translated execution with real C, including errors and allocation failure. They are finite evidence of fidelity, not proof. Sanitizer runs extend that evidence. |
| Audit and differential self-tests | Deliberately break their inputs and require the checking mechanisms to detect the change. |
| Proof mutants | Change translated function behaviour and require the function's proof to reject it. Sensitivity does not prove that every error is covered. |

## Known limits

- **The checkers are trusted.** The auditor (`tests/audit/*.lean`), `scripts/`, `tests/audit/proofmut.sh`,
  `tests/audit/selftest.sh` and the mutator scripts (`tests/proof-mutants/*.py`) are protected by
  review of their diffs, not by another check.
- **A reused verdict is trusted like the scripts.** A pre-check believes a stored record whose key
  matches. The store is in the workflow cache; a run on a branch or on `main` can write the store
  that a pre-check on that branch reads. A full run reads no store.
  See [proof mutants](proof-mutants.md#verdict-reuse).
- **A reasoned removal is the reviewed escape.** An entry with a reason in
  `tests/audit/registry-removals.json` lifts a shrink-only rule for one name. It is visible in the
  diff. An entry that excuses nothing is rejected as stale.
- **The commit chain starts at pinned floors.** The shrink-only rules read the history after two
  commits pinned in the script. A force-push that rewrites the history after a floor escapes them.
  Branch protection against force-push is the defence.
- **A `script:` mutant row is checked by reading it.** The runner's guard against a bad mutant
  compares the first error with the row's file, which for a script row is the script. See
  [proof mutants](proof-mutants.md#known-limits).
- **There are no lock files.** A definition, a specification or a theorem statement is tracked by
  git alone, so a change to one is visible only in the diff. Review decides whether a statement
  says enough, whether the runtime represents C, and whether the translation matches the source.

[The anti-cheating page](../anti-cheating.md) says what the acceptance suite defends against and
what it does not. A statement that is wrong is corrected, not worked around: see `AGENTS.md`.

## Guides and records

| Page | Purpose |
| --- | --- |
| [Contributing](contributing.md) | Numbered steps and commands, from a clone to an accepted result. |
| [Public goals](goals.md) | The registries, the required set and the shrink-only rules. |
| [Proof mutants](proof-mutants.md) | How to add, run and read mutation checks, and their limits. |

The remaining pages in this folder are dated records of past reviews. They preserve evidence and
scope. They are not the current process and not current defect lists. Each one starts with a note
that says when it was written and what has changed since.

| Record | Content |
| --- | --- |
| [Public contract review](contract-review.md) | Statement layers, source-review corrections and counterexamples, from before the scope became safety only. |
| [Local registration review](registration-review.md) | What the recorded local registration checks established. |
| [Query registration review](query-registration-review.md) | Six exact public queries and their mutation evidence. |
| [Compiler helper review](compiler-helper-review.md) | Generated recursive execution helpers and their logical counterparts. |
| [Runtime review](runtime-review.md) | Findings R1–R13 and translation questions U1–U5, with their state today. |
| [Heap-table review](runtime-tables-review.md) | Findings F1–F6 about array-backed tables and in-place updates, with their state today. |

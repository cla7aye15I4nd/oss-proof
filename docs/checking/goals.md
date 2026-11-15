# Public verification goals

The claim is safety for every documented public function of zlib: no undefined behaviour, no memory
error, no leak, and termination, over call sequences. The target is the default x86_64 Linux static
build with the default allocator. Allocation failure is in scope. Functional correctness and other
build configurations are not planned ([scope](../progress.md#scope)).

This page says how the audit decides which goals are required, what registering a proved goal
needs, and which rules stop a registered result from disappearing. What a safety goal says is in
[safety claims](../spec/safety.md). The current status is only in [progress](../progress.md).

## The registries

All of them are under `tests/audit/`. The acceptance suite reads them; the fast gate does not.

| File | Content | Who checks it |
| --- | --- | --- |
| `goals.txt` | Every target statement: a definition of type `Prop` whose name contains `Goal`. | The auditor rejects a `Goal.*` proposition of the library that is not listed. |
| `theorems.txt` | The registered theorems, one fully qualified name per line. | The auditor: each exists, is a theorem, has a doc string and depends only on the allowed axioms. |
| `proved-goals.txt` | The goals that a registered theorem proves. | The auditor rejects any difference from the set it finds PROVED. So the scripts decide on this file, never on report text. |
| `public-api.json` | The manifest: every exported function of the pinned `zlib.h` with its manual section, translated entry, functional goal and safety goal; the goal groups; `open_safety`; `not_planned`. | `scripts/verification.py` (`coverage`). |
| `public-mutants.json` | For each keyed goal, the mutant rows that its exact proof must reject. | `scripts/verification.py`; see [proof mutants](proof-mutants.md). |
| `registry-removals.json` | Reasoned removals from the registries and the mutant tables. | `scripts/verification.py`: a stale entry is rejected. |

A goal is PROVED only when a theorem of `theorems.txt` has exactly the goal as its type. A theorem
with extra premises, or about an abstract model, proves nothing here. An entry of the manifest is
a requirement, not a proof.

## The required set

The manifest has 96 functions: 95 of the default build and the Windows-only `gzopen_w`. zlib.h
lists ten of them as undocumented; the manifest names them under `undocumented`, and the script
compares that list with the header. Their goals are not required. Their registered theorems stay
audited.

The required goals are computed by `required_public_goals` in `scripts/verification.py`:

- the safety goal of every documented function of the default build;
- the goals of the group `safety_goals` (57);
- the goals of the group `nonvacuity_goals` (4).

That is 63 goals today. Two rules stop a manifest edit from shrinking the set.

**The groups are pinned in the script.** `coverage` compares `sequence_goals`, `nonvacuity_goals`
and `safety_goals` of the manifest with lists written in the script. A group that differs is
rejected. So a goal leaves the required set only through a change to `scripts/`, which is reviewed.

**Each function's safety goal is fixed by the script** (`check_safety_binding`). A documented
function names exactly one of:

1. its own goal `Goal.<function>_safety` (or `_safe`), when that goal is in the pinned group;
2. its full contract, only for `compressBound` and `compressBound_z` (pure functions with no heap;
   the manifest carries a `safety_note`);
3. a shared sequence goal, only for the functions the script lists for it: the 31 documented gz
   functions name `Goal.gz_sequence_safety`, and `inflateBack`, `inflateBackInit_` and
   `inflateBackEnd` name `Goal.inflate_back_sequence_safety`.

The gz and `inflateBack` functions do not have per-function safety goals yet. Stating them is
planned work ([progress](../progress.md)); until then the sequence goals carry their safety.

The functional goals (`Goal.<function>` and the group `sequence_goals`) are not required. A proved
one is audited in full. An unproved one is reported as open and fails nothing.

### `open_safety` and `not_planned`

- `open_safety` lists the required goals that have no registered theorem yet, each with an owner.
  It is empty today. A required goal must be PROVED or listed there; a listed goal must not be
  PROVED. `verification.py final` rejects a list that is not empty.
- `not_planned` lists public goals that stay defined and stay in `goals.txt` as open targets, but
  that the project does not work on, each with a reason. It is not a way out of the required set:
  the pinned groups decide what is required. An entry must be in no group, named by no function,
  and not proved. Its one entry is `Goal.gz_initialisation_domain`, the functional contract of
  `gzopen`.

## What a registration needs

A goal counts as registered when all of these hold on one commit. [Contributing](contributing.md#at-a-milestone)
gives the commands.

1. The theorem has exactly the goal as its type, and it has a doc string. The doc string states
   any precondition narrower than zlib.h; the same precondition has a row in
   [deviations](../deviations.md).
2. The theorem's name is in `tests/audit/theorems.txt`.
3. The goal's name is in `tests/audit/proved-goals.txt`.
4. The goal is removed from `open_safety` in `tests/audit/public-api.json`, if it was there.
5. The goal has mutant evidence: a key in `tests/audit/public-mutants.json`, or pinned evidence
   for a goal that is not about one function ([proof mutants](proof-mutants.md#which-goals-need-which-evidence)).
6. The progress view in `docs/progress.md` is regenerated. The audit fails on a stale view.

A new goal also needs a line in `goals.txt`. A new required goal needs its name in the manifest
group and in the pinned list of the script, in one reviewed change.

Registered is not accepted. The result is accepted when the acceptance suite is green on that
commit, and a report names the commit.

## Shrink-only rules

A result that was registered once must not vanish quietly. The audit compares the present files
with every earlier commit of a chain.

**The chain.** It holds the base, the pinned floors, and every commit after the floors that `HEAD`
contains, through all parents of a merge. The base is the pull request's base branch, or
`origin/main`, or the first parent when `HEAD` is that commit. The two floors are fixed commits
written in the script (`CHAIN_FLOORS`), one on `dev` and one on `main`. At least one floor must be
an ancestor of `HEAD`, or the audit rejects the run. A floor moves forward only by an edit to the
script.

| Rule | What may not happen along the chain | Reviewed way out |
| --- | --- | --- |
| Open list | A required goal that was closed (required and not in `open_safety`) at some commit is in `open_safety` now. A goal that is new to the required set may enter the list. | None. |
| Registries | A name of `theorems.txt` or `proved-goals.txt` at some commit is missing now. | An entry `{name, reason}` under `theorems` or `proved_goals`. |
| Mutant references | A reference (goal, list, row) of a goal that is proved now is missing, or the referenced row has a different file, old text or new text. | An entry `{goal, list, name, reason}` under `mutant_references`. |
| Frozen rows | A row of a frozen mutant list is missing or differs in any field, or the mutator script of a `script:` row has different content. | An entry `{list, name, reason}` under `mutant_rows`. |
| Mutant waivers | The script's list of proved goals without function mutants (`MUTANT_COVERAGE_PENDING`, empty today) has a new entry. | None. |

The entries are in `tests/audit/registry-removals.json`. Each needs a reason that is not empty. An
entry that excuses nothing (the name was never registered on the chain, or is registered now) is
stale, and the audit rejects it. The file holds nine `mutant_rows` entries today, all for rows of
`api-boundary.tsv` whose specification file moved in the specification split.

## What a safety goal covers

| Part | Required statement |
| --- | --- |
| Domain | Every call that zlib.h permits. A rejected parameter has a specified error path. Internal helper bounds are established by the implementation, not added as caller requirements. A premise narrower than zlib.h is listed in [deviations](../deviations.md). |
| Execution | The actual translated entry returns without a fault, including fuel exhaustion, for every permitted initial heap and every allocation-failure oracle. An empty execution relation cannot satisfy the goal. |
| Frame | Memory outside the call's footprint is unchanged. Unrelated live objects are kept. |
| Ownership | Init and copy establish ownership. A failed init or copy releases its partial allocations. End and close release owned storage exactly once. |
| Sequences | The representation invariant is established by the init function and preserved by every permitted call, so the per-call statement holds along every legal history. |

The four non-vacuity goals show that the premises of the sequence goals can be met: init
establishes the representation invariant on its documented parameter domain. No registered
theorem may assume an unproved callee contract. The goal definitions are in `ZlibF/Spec/Safety/`
and, for the gz interface and `inflateBack`, in `ZlibF/Spec/Public/`; the layout is in
[the split design](../design/safety-functional-split.md).

## Caller assumptions and semantic limits

The caller supplies live objects and the readable or writable ranges required by the API.
Calls on one stream are sequential. The caller does not modify library-owned state.
Caller buffers with no semantic reason to overlap are assumed disjoint; each such premise is
explicit in the statement and listed in [deviations](../deviations.md).
Undefined behaviour in a permitted library call is a blocker, not a new caller restriction.

Callbacks and system calls are external. Their documented memory contracts are assumptions.
Termination also assumes that they return and that callback input is finite where an unlimited
stream could otherwise continue forever. This is not a theorem about arbitrary caller code
or the operating system.

The claim excludes compiler and operating-system correctness, performance, constant-time
behaviour and resource bounds against decompression bombs. Malformed compressed data remains
in scope. The trusted semantic limits are in [the trusted base](../trusted-base.md).

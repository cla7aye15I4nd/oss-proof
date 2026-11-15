# Proof mutants

A proof mutant is a deliberate error put into one translated function, in a temporary copy of the
sources. The proof of that function must then fail to check. If it still checks, the proof does
not depend on the code that was changed. This page shows one mutant from start to end, defines the
terms, and then gives the steps and the rules.

A kill is evidence that a proof is sensitive to one edit. It is not a proof that the goal covers
every error. Which rows carried the evidence when the goals were registered is a dated record:
[mutant evidence](mutant-evidence.md).

## One mutant, start to end

The C function `adler32` passes its arguments on:

```c
uLong ZEXPORT adler32(uLong adler, const Bytef *buf, uInt len) {
    return adler32_z(adler, buf, len);
}
```

The mutant `adler32-wrapper-length` makes the translation pass `len + 1`. It is one row of the
list `tests/proof-mutants/public-checksums.tsv`. A row has five fields separated by tabs:

| Field | Value in this row |
| --- | --- |
| `NAME` | `adler32-wrapper-length` |
| `FILE` | `ZlibF/Zlib/adler32.c.lean` |
| `OLD` | `adler32_z adler buf len.toUInt64` |
| `NEW` | `adler32_z adler buf (len.toUInt64 + 1)` |
| `PROOF_MODULES` | `adler32.c,adler32.c.public-any,adler32.c.public-one,public-adler-update` |

The mutant changes behaviour on an input the goal permits. `Goal.adler32_safety` allows a `NULL`
buffer with length 0. With length 0 the mutant calls `adler32_z` with length 1, and `adler32_z`
reads `buf[0]` when the length is 1, before it tests `buf` against `NULL`. So the mutant reads
through `NULL`, and no proof that `adler32` is safe can hold for it.

Run the row. The second argument is a regular expression on the name.

```sh
bash tests/audit/proofmut.sh tests/proof-mutants/public-checksums.tsv '^adler32-wrapper-length$'
```

The runner copies the workspace and its build cache to a temporary directory. It builds the four
proof modules unchanged; they must build. It replaces `OLD` by `NEW` in the copy of `FILE` and
builds the four modules again. Then it prints one line for the row: the name, the verdict, the
seconds of the second build, and the first error of that build.

```console
baseline: the listed proof modules build unmutated
adler32-wrapper-length                   KILLED        <N>s error: ZlibF/Proof/<module>.lean:<line>:<column>: ...
1 killed, 0 equivalent (build as expected), 0 known gaps (proofs still build), 0 bad mutants
PROOFMUT PASS
```

The first, third and fourth lines are the text the script prints. **The second line is
illustrative**: its layout is that of the script, and `<N>`, `<module>`, `<line>` and `<column>`
stand for values that only a run gives. The command needs a Lean build and was not run for this
page.

The verdict `KILLED` means that the first error is in one of the four modules named in
`PROOF_MODULES`. An error in the translation file itself, or in another proof, has a different
verdict and does not count ([verdicts](#verdicts)).

This row has a second use. The file `tests/audit/public-mutants.json` names it under two goals:

```json
"ZlibF.Spec.Public.Goal.adler32_safety": [
  {"list": "tests/proof-mutants/public-checksums.tsv", "name": "adler32-wrapper-length"}
]
```

(and the same under `Goal.adler32`). For each such entry the acceptance suite takes the
registered proof of the goal, substitutes the mutated `adler32` into it, and checks the result in
a fresh kernel. The kernel must report a type mismatch. On success the suite prints
`exact public proof rejects: ZlibF.Spec.Public.Goal.adler32_safety: adler32-wrapper-length` (text
from `scripts/verification.py`).

## A row that found a wrong goal

A mutant that survives is a finding. The macro `gzgetc()` of zlib.h reads from the buffer when
`have` is not zero and calls the function `gzgetc` otherwise. The row `macro-have-guard-dropped`
removes the test of `have`, so that the buffered path runs with nothing buffered. It survived at
first: the whole proof of `Goal.gz_sequence_safety` still built. The cause was the goal, which
ran the macro only with `have ≠ 0`, so the other branch was outside it. The goal was corrected in
commit `3c5292f7` (regression `tests/verification/regressions/gz-macro-have-zero.lean`), and the
row is killed in `zlib.h.gzgetc-macro`.

## Terms

| Term | Meaning |
| --- | --- |
| List | A `.tsv` file of rows. There are three directories of lists ([below](#the-three-list-directories)). |
| Row | One mutant: the five fields of the example, and an optional marker. |
| Key | The entry of a goal in `tests/audit/public-mutants.json`: the rows that the goal's registered proof must reject. A row named there is a **keyed row**; a goal with an entry is a **keyed goal**. |
| Structural mutant | An edit outside loop bodies and outside machine arithmetic: a dropped or replaced call, a dropped store, a changed constant, a wrong return value. Only structural mutants are keyed ([rule 5](#a-keyed-row)). |
| Restatement | A copy of a function's code inside a proof file, tied to the translation by an equation that holds by unfolding (`rfl`). The proof then reasons about the copy. |
| Script row | A row whose `FILE` is `script:PATH`. The script makes the edit in the translation and in every restatement of it. |
| Semantic list | One of the eight lists of `SAFETY_MUTANT_LISTS` in `scripts/verification.py`. Their rows are killed in a lemma about behaviour, not at a restatement. They are `deflate-header.tsv`, `deflate-strategies.tsv`, `deflate-ops.tsv`, `stream-refusal.tsv`, `infback-sequence.tsv`, `gz-refusal.tsv`, `gz-sequence.tsv` and `gz-read.tsv` under `tests/proof-mutants/`. |
| Pinned evidence | For a required goal that is not about one function: the lists and keyed goals that the script names as its evidence (`PINNED_EVIDENCE`). |

### The three list directories

| Directory | Content | Run by |
| --- | --- | --- |
| `tests/proof-mutants/` | The lists of the public goals (`public-*.tsv`), `api-boundary.tsv`, and the eight semantic lists with their mutator scripts. New rows go here. | The twenty mutant shards of the acceptance suite, and `verification.py final`. |
| `tests/audit/proofmut/` | Eight lists, one per C file (`adler32.tsv`, `crc32.tsv`, `deflate.tsv`, `inflate.tsv`, `inftrees.tsv`, `trees.tsv`, `trees-out.tsv`, `zutil.tsv`), about the checksum, utility, tree, inflate, deflate and decode-table proofs. No key names them. | Only `verification.py final`, and by hand. |
| `tests/proofmut/` | Nine small lists on single topics. Keys name rows of three of them (`crc-updates-public.tsv`, `deflate-default-init.tsv`, `gzip-frontier.tsv`); the shards run those three. The `.py` files there are stand-alone checks that no workflow runs. | The shards for the three lists; `verification.py final` for all nine. |

## Verdicts

`proofmut.sh` prints one of these for each row.

| Verdict | Interpretation |
| --- | --- |
| `KILLED` | The first error is in an expected proof module. The mutation check passes. |
| `SAME ok` | A mutation marked as equivalent still builds. Review the equivalence reason. |
| `GAP (known)` | A documented proof gap survives in development mode. It is not coverage and fails strict acceptance. |
| `SURVIVED` | A mutation with no marker still builds. Investigate missing coverage or equivalence. |
| `BAD MUTANT` | The translation or a file outside the proof tree fails. Repair the mutation. |
| `WRONG PLACE` | Another proof fails first. This does not satisfy the check of the designated function. |
| `SORRY` | The mutated copy contains `sorry`. Repair the mutation. |
| `NO ERROR` | The build failed without a recognized error, even after one retry. No proof rejection was established. |
| `UNEXPECTED` | A mutation marked equivalent failed. Review the marker and the mutation. |
| `NOT APPLIED` | The replacement text did not occur exactly once, or was unchanged, or the mutant script failed. Update the mutation. |

A killed mutation with a stale `gap:` marker also fails. Remove the marker once the gap is
closed.

## Add a mutant

1. Choose the list. A structural mutant of a public function that will be keyed goes in a list
   under `tests/proof-mutants/` (for example `public-safety.tsv`). A mutant in a loop body or in
   machine arithmetic, or one that needs paired edits, goes in a semantic list.
2. Add one tab-separated row. Lines starting with `#` are comments.

   ```text
   NAME <TAB> FILE <TAB> OLD <TAB> NEW <TAB> PROOF_MODULES [<TAB> same:REASON | gap:REASON]
   ```

   | Field | Meaning |
   | --- | --- |
   | `FILE` | Translation source relative to the repository root, such as `ZlibF/Zlib/adler32.c.lean`. Or `script:PATH`: the runner calls `python3 PATH <copy> NAME` to make the mutant; `OLD` and `NEW` are then `-`. |
   | `OLD`, `NEW` | Replacement text. A literal `\n` denotes a newline; `OLD` occurs exactly once in `FILE`. |
   | `PROOF_MODULES` | Comma-separated paths under `ZlibF/Proof`, without `.lean`, naming the proofs of the function. Only these are built. |
   | Optional marker | `same:` explains why the mutant is equivalent; `gap:` records missing coverage, for development only. Neither is allowed in a keyed row. |

3. Run the row with the list runner and read the verdict.

   ```sh
   bash tests/audit/proofmut.sh tests/proof-mutants/public-safety.tsv '^deflatePrime'
   ```

4. For a keyed row, add `{"list": ..., "name": ...}` under the goal in
   `tests/audit/public-mutants.json`, then check the key.

   ```sh
   python3 scripts/verification.py coverage
   ```

5. For a goal without a key, add or raise its entry in `PINNED_EVIDENCE`. This is a change to
   `scripts/` and is reviewed.

A useful mutation drops a check or an assignment, changes a bound or a comparison, alters an index
or a shift, or returns a wrong result. Choose different parts of a proved function. A syntax
error is not evidence. Review establishes that a required mutant changes behaviour on a permitted
input, as the example above does for `NULL` with length 0.

## Run the checks

From the repository root, with a warm `.lake` build cache:

```sh
python3 scripts/verification.py mutants
python3 scripts/verification.py mutants --shard-count 20 --shard-index 3
bash tests/audit/proofmut.sh tests/audit/proofmut/adler32.tsv
bash tests/audit/proofmut.sh tests/audit/proofmut/crc32.tsv '^combine'
```

The first command builds the project. Then, for every keyed goal, it checks the parsed mutation
boundaries, replays the original exact proof and replays each keyed row. It then runs, in strict
mode, `api-boundary.tsv`, the semantic lists and every list that a key references. The
second command runs one of twenty shards, as CI does. The last two run one list, optionally
filtered by mutant name. They are useful during development and do not replace acceptance.

**Shards.** A goal's unchanged control replay travels with all its keyed rows, as one item. Each
killable row of a list is an item; a `same:` row travels with the first killable row of its list.
The items are packed by recorded duration: longest first, each into the shard with the least load
so far. The durations are in `tests/proof-mutants/durations.json`, written from the verdicts of a
full run (`python3 scripts/mutant_reuse.py durations`); an item it does not name weighs one minute.
The file only balances the shards. Whatever it says, every item goes to exactly one shard, so no
row is lost or run twice. A shard with nothing to run is rejected.

**The list runner** copies the workspace and the warm cache into a temporary directory. It builds
the listed proof modules unchanged, applies each replacement exactly once and builds only
the designated modules. The first reported error must be in an expected proof module.
The original cache is left untouched. One mutant runs at a time.

**Strict mode** (`PROOFMUT_STRICT=1`) forces the unchanged build, rejects every `gap:` row and
requires at least one `KILLED` row; a `same:` row that builds is not evidence. The shards give each
`same:` row to a shard that also runs a row of its list that must be killed. A list with no such
row is rejected. A run that skipped the unchanged build cannot support acceptance.

**Runner settings.** `PROOFMUT_CACHE` selects the warm cache. `PROOFMUT_TIMEOUT` sets seconds per
build, defaulting to 3600. `PROOFMUT_KEEP=1` retains temporary copies; `PROOFMUT_SHOWLOG=1` prints
failure details. `PROOFMUT_BASELINE=0` skips the unchanged build, for local diagnosis only.
`PROOFMUT_STRICT=1` overrides that skip.

**What runs where.** The nightly suite runs the twenty shards, in full. A pre-check with
[verdict reuse](#verdict-reuse) runs the same shards and skips the units whose inputs are
unchanged. A list that no key references and
that is not a semantic list or `api-boundary.tsv` is not run by the shards; it runs only
in `python3 scripts/verification.py final`, which runs every list of the three directories in
strict mode. A list that was not run is not a passing check.

## The two checks

| Check | What it does | Counts as rejected when |
| --- | --- | --- |
| Re-elaboration (`tests/audit/proofmut.sh`) | Applies one row of a list to a copy of the workspace and builds the proof modules the row names. | The first error is in one of those proof modules (`KILLED`). |
| Kernel replay (`zlibf-proof-replay`) | Takes the registered exact proof of a goal and substitutes only the changed source declarations into its dependency closure, in a fresh kernel. | The kernel reports a type mismatch. The original is accepted first. |

Re-elaboration runs for every row of every list the suite runs. The kernel replay runs in
addition for the keyed rows.
For the replay, failure of an unrelated theorem, or of a stronger theorem with extra premises, is
insufficient. A timeout or a kernel resource error is not a rejection.

This is different from the differential self-test in `tests/selftest.sh`, which requires an
execution comparison to detect a mutation. A mutant caught only by testing can expose missing
proof coverage. What the acceptance suite does and does not defend against is in
[the verification policy](../anti-cheating.md).

## Which goals need which evidence

| Goal | Evidence the audit requires |
| --- | --- |
| The functional goal `Goal.<function>` of a public function, when it is proved | A key in `public-mutants.json` with at least one row. |
| A function's own safety goal (`Goal.<function>_safety` or `_safe`), when it is proved | A key of its own. |
| A proved required goal that is not about one function: the four sequence safety goals, the three refusal goals and the four non-vacuity goals | Pinned evidence in `PINNED_EVIDENCE` of `scripts/verification.py`. |

A proved goal of one public function without a key is rejected. The script has a list of
waivers for this (`MUTANT_COVERAGE_PENDING`); it is empty, and the audit rejects a new entry. A
proved required goal with neither a key nor a pin is rejected.

**Pinned evidence.** Eleven proved required goals have no key of their own. For each, the script
pins the semantic lists that carry its evidence, each with a minimum number of rows that must be
killed, and the keyed goals whose replay also checks it: their proofs are corollaries of this
goal, or share its run lemmas. Every pinned list is a list that the mutant shards run. Each
pinned keyed goal has at least one row. A pinned keyed goal may be a functional goal; the last two
rows of the table name one each.

| Goal | Pinned lists (minimum rows to kill) | Pinned keyed goals |
| --- | --- | --- |
| `Goal.gz_sequence_safety` | `gz-sequence.tsv` (43), `gz-read.tsv` (18) | none |
| `Goal.inflate_back_sequence_safety` | `infback-sequence.tsv` (11) | none |
| `Goal.deflate_sequence_safety` | `deflate-header.tsv` (5), `deflate-strategies.tsv` (10), `deflate-ops.tsv` (7) | `Goal.deflate_safety`, `Goal.deflateEnd_safety` |
| `Goal.inflate_sequence_safety` | none | `Goal.inflate_safety`, `Goal.inflateEnd_safety`, `Goal.inflateCopy_safety` |
| `Goal.inflate_refusal`, `Goal.deflate_refusal` | `stream-refusal.tsv` (5) | none |
| `Goal.gz_refusal` | `gz-refusal.tsv` (19) | none |
| `Goal.inflate_initialisation_domain` | none | `Goal.inflateInit2__safety` |
| `Goal.deflate_initialisation_domain` | none | `Goal.deflateInit2__safety` |
| `Goal.inflate_back_initialisation_domain` | `infback-sequence.tsv` (11) | `Goal.inflateBackInit_` (functional) |
| `Goal.gz_sequence_nonvacuity` | `gz-sequence.tsv` (43) | `Goal.gzdopen` (functional) |

All lists of the table are under `tests/proof-mutants/`.

## Rules

### A keyed row

A keyed row satisfies all of these. The script checks 1 to 4; the replay budget enforces 5.

1. The list is a `.tsv` file in one of the three list directories, and the name selects exactly
   one row.
2. The row's file is the translation source of the keyed function. The old text occurs exactly
   once in that file, inside the function's body, and differs from the new text. The signature is
   preserved. A parser checks both versions without loading candidate imports.
3. The row has no `same:` or `gap:` marker, and it names proof modules.
4. Mutations of another function, specification-only changes and injected declarations do not
   count.
5. **The row is a structural mutant: it does not edit a loop body or machine arithmetic.** A
   mutant of those kinds goes in a list without a key, where re-elaboration checks it.

Rule 5 exists because the kernel replay cannot refute every kind of mutation within its budget.
It counts a mutation as rejected only on a kernel type mismatch. Two kinds of change make the
kernel work without bound instead:

- A change to machine arithmetic over free variables, such as `x - left` to `x - len`. To refute
  it, the kernel unfolds the `UInt64` and `UInt32` operations down to `Nat` modulus with nothing
  to compute on. Measured on `uncompress2_z`: the 12 GiB budget was reached after 806 s.
- Any change inside a `cdoWhile` body, even a dropped test. After the two bodies fail to match,
  the kernel unfolds `cdoWhile` on both sides. Its fuel recursion then unrolls one iteration at a
  time and compares the bodies again at each step. Measured on `compress2_z`: the 12 GiB budget
  was reached after 467 s, and 16 GiB after 214 s for a dropped test.

Structural changes are rejected quickly. Each such row takes 120 s to 200 s at about 10.5 GB on
`uncompress2_z` and `compress2_z`. A replay over the budget (12 GiB of resident memory;
`ZLIBF_REPLAY_RSS_MB` changes it) is stopped and fails, and its message says to move the row. The
budget is not raised when a dependency closure grows; the fix is a smaller replay closure.

A list keeps its arithmetic and loop-body mutants as well, and every mutation shard checks those
by re-elaboration, where the proof fails in a lemma about behaviour.
`tests/proof-mutants/api-boundary.tsv` is the example: `uncompress2_z-destLen-count` and both
`refill-off-by-one` rows are checked by re-elaboration. Rows with the same intent and a
structural change carry the kernel replay: `uncompress2_z-destLen-drop`, a wrong `destLen` count,
and the two `initial-room` rows, output room beyond what remains.

### Restatements and script rows

Some proofs reason about a restatement of a function. A one-file edit of such a function fails
first at the equation that ties the restatement to the translation. That shows only that the proof
is tied to the translation. A script row solves this: its script makes the same edit in the
translation and in every restatement of it, so that only a lemma about behaviour can fail. A
script row cannot be keyed (rule 2), so it lives in a semantic list.

### Frozen rows

The rows of the semantic lists and of `tests/proof-mutants/api-boundary.tsv` are frozen along the
commit chain of the [rules against silent removal](goals.md#shrink-only-rules): every field, the
`PROOF_MODULES` column and the marker included, and the sha256 of the mutator of a script row.
Rows may be added. A changed or removed row needs a `mutant_rows` entry `{list, name, reason}` in
`tests/audit/registry-removals.json`, and an entry that excuses nothing is rejected as stale.

The references of a proved goal's key are protected in the same way: a reference may not
disappear, and its row may not change its file, old text or new text, without a
`mutant_references` entry `{goal, list, name, reason}`. So a committer cannot drop a goal's key,
cut its rows to one, or swap a row for a weaker one without a reason in the diff.

A shard fails when a semantic list is missing or empty.

## Verdict reuse

A full run executes every unit: about 2400 runner minutes on twenty shards. Most units have the
same inputs as in the run before. A **pre-check** reuses the stored verdict of such a unit. It
does not change what a mutant is: the mutated translation, the unchanged proof sources, and Lean
and the kernel as judges. It only skips an execution whose inputs are byte for byte those of an
execution that already passed.

**A pre-check is not acceptance.** An accepted result needs a full run on the commit you name.
The nightly run on `main` and the run before each merge to `main` are full runs.

```sh
python3 scripts/verification.py mutants --record verdicts.json
python3 scripts/verification.py mutants --reuse store.json --record verdicts.json
```

The first command is a full run that also writes its verdicts. It reads no store. The second is a
pre-check. It prints one line for each unit, `REUSED <key> from <commit> (run <run>) <unit>` or
`RAN <key> <unit>`, and ends with the counts:
`mutants: 31 units, 4 ran, 27 reused (pre-check with reused verdicts; an accepted result needs a full run)`.
A full run ends with `N ran, 0 reused (full run)`.

**Units.** There are three kinds: a row of a list (run by `proofmut.sh`), the control replay of a
keyed goal, and the replay of one keyed row against one goal.

**The key.** `scripts/mutant_reuse.py` derives the key, and nothing else does. It is a sha256 over:

| Input | Covered by |
| --- | --- |
| The scripts that produce a verdict | The bytes of `scripts/verification.py`, `scripts/mutant_reuse.py`, `scripts/mutation_spans.py`, `tests/audit/proofmut.sh`, `tests/audit/ReplayPublicProof.lean` and `tests/audit/DeclarationSpan.lean`. An edit to any of them changes every key. |
| The build configuration | `lean-toolchain`, `lakefile.toml`, the Lake manifest when present, the operating system and machine type. |
| The runner's settings | The `PROOFMUT_*` variables, `ZLIBF_REPLAY_RSS_MB` and `ZLIBF_REQUIRE_PREBUILT`. |
| The row | The list's path and the whole row, every field. |
| A text row's edit | The file's text before and after the edit. |
| A `script:` row's edit | The mutator's bytes. The mutator is run on a fresh copy of the workspace, as the runner does it, and the tree it leaves is the mutated tree. |
| The proofs (a row) | The import closure of the row's proof modules, each file by content: once in the unmutated tree (the baseline build) and once in the mutated tree (the mutant build). |
| The proofs (a replay) | Every Lean source of the library, the registry `theorems.txt`, the goal, and the function and its source file. A keyed row's replay adds the row and the source after the edit. |

The import closure is read from the `import` commands of each file's header. The reader accepts
`import Name` with the modifiers `public`, `private`, `meta` and `all`. Any other text on the line
of an import makes the unit unkeyable. A test compares the reader with the audited reading of
`check_imports` on every file of the library.

A replay is keyed by the whole library because the replay tool picks the registered proof from the
whole compiled library. So any edit under `ZlibF/` runs every replay again. The replays are about a
fifth of the stage; the rows, which are the rest, are keyed by their closure.

**What is never reused.**

- A unit without a key. No key is computed when the edit does not apply exactly once, the mutator
  fails, the row has a `gap:` flag, an input is a symbolic link, an import is not understood, or
  the mutated text contains the word `sorry`. When the word `sorry` occurs anywhere in the Lean
  sources, comments included, no row is reused: the runner's `sorry` scan reads the whole tree.
- A verdict that is not the passing verdict of the unit's kind: `KILLED` for a row, `SAME ok` for a
  `same:` row, an accepted control replay, a rejected mutant replay. A store holds only these. A
  unit that failed or survived is not recorded, so it runs again.
- A row's verdict from a list run that failed as a whole, or whose verdict lines do not match the
  rows that were asked for.
- A record made in another repository, or outside the workflow (its run is `local`).

A unit that cannot be keyed runs. It never fails the run for that reason.

**Strict mode is unchanged.** The runner still needs a killed row in every list it runs. When only
`same:` rows of a list are left to run, the first killable row of that list runs again beside them.

**The store** is a JSON file of records: key, kind of unit, verdict, the first error line or the
replay's last line, peak memory (replays only), seconds, and the commit and workflow run that
produced the verdict. It is never committed. Each mutant shard uploads the verdicts of the units
that passed in it. The job `mutant_store` merges them with the earlier store and saves the result
in the workflow cache under `mutant-verdicts-<run>`. A record older than 45 days is dropped.

**In the workflow.** The manual trigger of `lean` has an input `reuse`, off by default. With it the
shards restore the newest store and run with `--reuse`, and the required result reports as
`audit (pre-check, reused verdicts)`, not as `audit`. The scheduled run and a dispatch without the
input never restore the store. Every run writes its verdicts, so full runs seed the store.

**Who can write the store.** The store is trusted like the scripts: a record with the right key
and a passing verdict is believed. A workflow run can read the cache of its own branch and of
`main`. A run can write only the cache of the branch it runs on. So a record that a pre-check on
`dev` reads was written by a run on `dev` or on `main`, with the workflow file of that branch.
Whoever can push to those branches can already edit the scripts. A pull request from a fork writes
to a cache of its own, which no branch reads. A pre-check on a new branch reads the store of
`main` until the branch has run once. The cache is evicted when the repository's caches exceed
their quota; a pre-check without a store runs everything.

## Known limits

- Verdict reuse trusts the store, the key derivation and the mutators' determinism. A mutator
  that writes something else on a second run of the same inputs is not seen by the key. The key
  does not cover the compiled library itself: it relies on the build of the run being the build of
  the sources, which each shard checks with Lake before the stage starts. A full run does not
  depend on any of this.
- The auditor (`tests/audit/*.lean`), `proofmut.sh`, `selftest.sh` and the mutator scripts
  (`tests/proof-mutants/*.py`) are trusted and protected by review, like `scripts/`. A mutator's
  content is frozen by its hash, but what it does is checked only by reading it. In particular the
  `BAD MUTANT` guard of `proofmut.sh` compares the first error with the row's `FILE`, which for a
  script row is the script, so a mutator that writes an error into the expected proof module
  would count as `KILLED`. Closing this needs a redesign of script rows; review is the defence.
- A removal entry with a reason is the reviewed way out of every removal rule. It is visible
  in the diff, and a stale entry is rejected.
- The commit chain covers the history after the pinned floors that `HEAD` still contains. A
  force-push that rewrites `dev` after the floor escapes it; branch protection against force-push
  is the defence.
- A kill shows sensitivity to one edit. It does not show that the goal covers every error, and a
  list's existence or an earlier result is not proof that every function in its C file is covered.
- A row that is rejected at a restatement shows that the proof is tied to the translation, not
  that it depends on the mutated check. The semantic lists exist to cover that case.

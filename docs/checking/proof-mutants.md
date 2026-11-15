# Proof mutants

A proof must reject deliberate errors in the function it verifies. A proof mutant changes
one translated function in a temporary copy and requires the failure to occur in that
function's proof. The unmodified proof must pass first.

This is different from the differential self-test in `tests/selftest.sh`, which requires an
execution comparison to detect a mutation. A mutant caught only by testing can expose missing
proof coverage. A proof's rejection is evidence of sensitivity, not proof that the mutation
changes observable behaviour or that the theorem covers every error. Review must establish
that a required mutant changes behaviour on a permitted input.

The page has four parts: the two checks, the rules, how to add and run a mutant, and the recorded
evidence for each group of goals.

## The two checks

| Check | What it does | Counts as rejected when |
| --- | --- | --- |
| Re-elaboration (`tests/audit/proofmut.sh`) | Applies one row of a list to a copy of the workspace and builds the proof modules the row names. | The first error is in one of those proof modules (`KILLED`). |
| Kernel replay (`zlibf-proof-replay`) | Takes the registered exact proof of a goal and substitutes only the changed source declarations into its dependency closure, in a fresh kernel. | The kernel reports a type mismatch. The original must be accepted first. |

Re-elaboration runs for every row of every list the suite runs. The kernel replay runs in
addition for the rows that a goal names in `tests/audit/public-mutants.json` (its **key**).
For the replay, failure of an unrelated theorem, or of a stronger theorem with extra premises, is
insufficient. A timeout or a kernel resource error is not a rejection.
What the acceptance suite does and does not defend against is in [the anti-cheating policy](../anti-cheating.md).

## Which goals need which evidence

| Goal | Evidence the audit requires |
| --- | --- |
| The functional goal `Goal.<function>` of a public function, when it is proved | A key in `public-mutants.json` with at least one row. |
| A function's own safety goal (`Goal.<function>_safety` or `_safe`), when it is proved | A key of its own. |
| A proved required goal that is not about one function: the four sequence safety goals, the three refusal goals and the four non-vacuity goals | Pinned evidence in `PINNED_EVIDENCE` of `scripts/verification.py`. |

A proved goal of one public function without a key is rejected. The script has a list of
waivers for this (`MUTANT_COVERAGE_PENDING`); it is empty and may only shrink. A proved required
goal with neither a key nor a pin is rejected.

**Pinned evidence.** Eleven proved required goals have no key of their own. For each, the script
pins the semantic lists that carry its evidence, each with a minimum number of rows that must be
killed, and the keyed goals whose replay also checks it (their proofs are corollaries of this
goal, or share its run lemmas). Every pinned list must be a list that the mutant shards run. Each
pinned keyed goal must have at least one row.

| Goal | Pinned lists (minimum rows to kill) | Pinned keyed goals |
| --- | --- | --- |
| `gz_sequence_safety` | `gz-sequence.tsv` (43), `gz-read.tsv` (18) | none |
| `inflate_back_sequence_safety` | `infback-sequence.tsv` (11) | none |
| `deflate_sequence_safety` | `deflate-header.tsv` (5), `deflate-strategies.tsv` (10), `deflate-ops.tsv` (7) | `deflate_safety`, `deflateEnd_safety` |
| `inflate_sequence_safety` | none | `inflate_safety`, `inflateEnd_safety`, `inflateCopy_safety` |
| `inflate_refusal`, `deflate_refusal` | `stream-refusal.tsv` (5) | none |
| `gz_refusal` | `gz-refusal.tsv` (19) | none |
| `inflate_initialisation_domain` | none | `inflateInit2__safety` |
| `deflate_initialisation_domain` | none | `deflateInit2__safety` |
| `inflate_back_initialisation_domain` | `infback-sequence.tsv` (11) | `inflateBackInit_` |
| `gz_sequence_nonvacuity` | `gz-sequence.tsv` (43) | `gzdopen` |

All lists of the table are under `tests/proof-mutants/`.

## Rules

### A keyed row

A row named in `public-mutants.json` must satisfy all of these. The script checks 1 to 4; the
replay budget enforces 5.

1. The list is a `.tsv` file in `tests/audit/proofmut/`, `tests/proof-mutants/` or
   `tests/proofmut/`, and the name selects exactly one row.
2. The row's file is the translation source of the keyed function. The old text occurs exactly
   once in that file, inside the function's body, and differs from the new text. The signature is
   preserved. A parser checks both versions without loading candidate imports.
3. The row has no `same:` or `gap:` marker, and it names proof modules.
4. Mutations of another function, specification-only changes and injected declarations do not
   count.
5. **The row must not edit a loop body or machine arithmetic.** Such a mutant goes in a
   source-level list only, where re-elaboration checks it.

Rule 5 exists because the kernel replay cannot refute every kind of mutation within its budget.
It counts a mutation as rejected only on a kernel type mismatch. Two kinds of change make the
kernel work without bound instead:

- A change to machine arithmetic over free variables, such as `x - left` to `x - len`. To refute
  it, the kernel unfolds the `UInt64` and `UInt32` operations down to `Nat` modulus with nothing
  to compute on. Measured on `uncompress2_z`: the 12 GiB budget was reached after 806 s.
- Any change inside a `cdoWhile` body, even a dropped test. After the two bodies fail to match,
  lazy delta unfolds `cdoWhile` on both sides. Its fuel recursion then unrolls one iteration at a
  time and compares the bodies again at each step. Measured on `compress2_z`: the 12 GiB budget
  was reached after 467 s, and 16 GiB after 214 s for a dropped test.

Changes outside loops are rejected quickly: dropped or replaced calls, dropped stores, and
changed constants. Each such row takes 120 s to 200 s at about 10.5 GB on `uncompress2_z` and
`compress2_z`. So a key names structural mutants. A replay over the budget (12 GiB of resident
memory; `ZLIBF_REPLAY_RSS_MB` changes it) is stopped and fails, and its message says to move the
row. The budget is not raised when a closure grows; the fix is a smaller replay closure.

A list keeps its arithmetic and loop-body mutants as well, and every mutation shard checks those
by re-elaboration, where the proof must fail in a semantic lemma.
`tests/proof-mutants/api-boundary.tsv` is the example: `uncompress2_z-destLen-count` and both
`refill-off-by-one` rows are checked by re-elaboration. Rows with the same intent and a
structural change carry the kernel replay: `uncompress2_z-destLen-drop`, a wrong `destLen` count,
and the two `initial-room` rows, output room beyond what remains.

### A good mutant

Useful mutations drop a check or assignment, change a bound or comparison, alter an index or
shift, or return a wrong result. Choose different parts of a proved function. A syntax error
or a mutation that merely breaks a source-equality lemma is insufficient evidence for its
execution contract.

Some proofs restate the code of a function in an `rfl` equation and reason about the
restatement. A one-file edit of such a function fails first at the equation, which shows only
that the proof is tied to the translation. A `script:` row solves this: its script makes the same
edit in the translation and in every proof restatement of it, so that only a semantic lemma can
fail. A script row cannot be keyed (rule 2), so it lives in a semantic list.

### Frozen rows

The rows of the semantic safety lists (`SAFETY_MUTANT_LISTS` in the script) and of
`tests/proof-mutants/api-boundary.tsv` are frozen along the commit chain of the
[shrink-only rules](goals.md#shrink-only-rules): every field, the `PROOF_MODULES` column and the
marker included, and the sha256 of the mutator of a `script:` row. Rows may be added. A changed or
removed row needs a `mutant_rows` entry `{list, name, reason}` in
`tests/audit/registry-removals.json`, and an entry that excuses nothing is rejected as stale.

The references of a proved goal's key are protected in the same way: a reference may not
disappear, and its row may not change its file, old text or new text, without a
`mutant_references` entry `{goal, list, name, reason}`. So a committer cannot drop a goal's key,
cut its rows to one, or swap a row for a weaker one without a reason in the diff.

The semantic safety lists are `deflate-header.tsv`, `deflate-strategies.tsv`, `deflate-ops.tsv`,
`stream-refusal.tsv`, `infback-sequence.tsv`, `gz-refusal.tsv`, `gz-sequence.tsv` and `gz-read.tsv`
under `tests/proof-mutants/`. A shard fails when one of them is missing or empty.

### A kill per list

`proofmut.sh` in strict mode needs at least one `KILLED` row; a `same:` row that builds is not
evidence. The shards give each `same:` row to a shard that also runs a killable row of its list.
A list with no killable row is rejected.

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
   | `OLD`, `NEW` | Replacement text. A literal `\n` denotes a newline; `OLD` must occur exactly once. |
   | `PROOF_MODULES` | Comma-separated paths under `ZlibF/Proof`, without `.lean`, naming the expected function proofs. Only these are built. |
   | Optional marker | `same:` explains equivalence; `gap:` records missing coverage for development only. Neither is allowed in a keyed row. |

3. Run the row with the list runner and read the verdict (next section).

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

## Run the checks

From the repository root, with a warm `.lake` build cache:

```sh
python3 scripts/verification.py mutants
python3 scripts/verification.py mutants --shard-count 20 --shard-index 3
bash tests/audit/proofmut.sh tests/audit/proofmut/adler32.tsv
bash tests/audit/proofmut.sh tests/audit/proofmut/crc32.tsv '^combine'
```

The first command builds the project and then, for every keyed goal, checks the parsed mutation
boundaries, replays the original exact proof and replays each keyed row. It then runs, in strict
mode, `api-boundary.tsv`, the semantic safety lists and every list that a key references. The
second command runs one of twenty shards, as CI does. The last two run one list, optionally
filtered by mutant name. They are useful during development and do not replace acceptance.

**Shards.** The keyed goals are dealt to the shards in name order; a goal's unchanged control
replay travels with all its keyed rows. The killable rows of the lists are dealt round robin, so
no row is lost or run twice. A shard with nothing to run is rejected.

**The list runner** copies the workspace and warm cache into a temporary directory. It builds
the unmodified listed proof modules, applies each replacement exactly once and builds only
the designated modules. The first reported error must be in an expected proof module.
The original cache is left untouched. One mutant runs at a time.

| Verdict | Interpretation |
| --- | --- |
| `KILLED` | The first error is in an expected proof module. The mutation check passes. |
| `SAME ok` | An explicitly equivalent mutation still builds. Review the equivalence reason. |
| `GAP (known)` | A documented proof gap survives in development mode. It is not coverage and fails strict acceptance. |
| `SURVIVED` | An unexcused mutation still builds. Investigate missing coverage or equivalence. |
| `BAD MUTANT` | The translation or a file outside the proof tree fails. Repair the mutation. |
| `WRONG PLACE` | Another proof fails first. This does not satisfy the designated function's check. |
| `SORRY` | The mutated copy contains `sorry`. Repair the mutation. |
| `NO ERROR` | The build failed without a recognized error, even after one retry. No proof rejection was established. |
| `UNEXPECTED` | A mutation marked equivalent failed. Review the marker and mutation. |
| `NOT APPLIED` | The replacement text did not occur exactly once, or was unchanged, or the mutant script failed. Update the mutation. |

A killed mutation with a stale `gap:` marker also fails. Remove the marker once the gap is
closed. Strict mode forces the positive baseline, rejects known gaps and requires a `KILLED` row.
Skipping the baseline cannot support final acceptance.

**Runner settings.** `PROOFMUT_CACHE` selects the warm cache. `PROOFMUT_TIMEOUT` sets seconds per
build, defaulting to 3600. `PROOFMUT_KEEP=1` retains temporary copies; `PROOFMUT_SHOWLOG=1` prints
failure details. `PROOFMUT_BASELINE=0` skips the positive build for local diagnosis only.
`PROOFMUT_STRICT=1` overrides that skip, rejects all known gaps and requires a killed row.

**What runs where.** The nightly suite runs the twenty shards. A list that no key references and
that is not a semantic safety list or `api-boundary.tsv` is not run by the shards; it runs only
in `python3 scripts/verification.py final`, which runs every list of the three directories in
strict mode. Neither a proposed workflow snippet nor an unexecuted list counts as a passing check.

## Known limits

- The auditor (`tests/audit/*.lean`), `proofmut.sh`, `selftest.sh` and the mutator scripts
  (`tests/proof-mutants/*.py`) are trusted and protected by review, like `scripts/`. A mutator's
  content is frozen by its hash, but what it does is checked only by reading it. In particular the
  `BAD MUTANT` guard of `proofmut.sh` compares the first error with the row's `FILE`, which for a
  `script:` row is the script, so a mutator that writes an error into the expected proof module
  would count as `KILLED`. Closing this needs a redesign of script rows; for now review is the defence.
- A removal entry with a reason is the reviewed way out of every shrink-only check. It is visible
  in the diff, and a stale entry is rejected.
- The revision chain covers the history after the pinned floors that `HEAD` still contains. A
  force-push that rewrites `dev` after the floor escapes it; branch protection against force-push
  is the defence.
- A kill shows sensitivity to one edit. It does not show that the goal covers every error, and a
  list's existence or a historical result is not proof that every function in its C file is covered.

## Recorded evidence

This part records, for each group of goals, which rows carry the evidence and where they are
killed. The lists and `public-mutants.json` are the authority; the measurements are those of the
runs that registered the goals. Current coverage work is recorded in [progress](../progress.md).

### Lists

The lists under `tests/audit/proofmut/` cover checksum, utility, tree, inflate, deflate and
decode-table proof groups. Additional lists live under `tests/proof-mutants/` and
`tests/proofmut/`. The files and the keys define their exact scope.

### `Goal.deflate`

The keyed rows of `Goal.deflate` (`tests/proof-mutants/public-deflate.tsv`) are one-file edits of
the body of `deflate`. Each is rejected first at `deflate_phases`, the `rfl` equation that splits
`deflate` into its phases; any edit of the body fails there. So these rows show that the
registered proof is tied to the translation, not that it depends on the mutated check. They are
acceptable for the exact replay only because the semantic kills are covered by the script-row
lists that every mutant shard runs: `deflate-header.tsv` (header stages and `_tr_flush_block`),
`deflate-strategies.tsv` (`fill_window`, `longest_match` and the strategies) and `deflate-ops.tsv`
(the stream operations). Each script row makes the edit in the translation and in every proof
restatement of it, and must be killed in its semantic lemma.

### `Goal.deflateCopy` and the refusal goals

The five rows of `Goal.deflateCopy` in `tests/proof-mutants/public-streams.tsv` are all structural:
- a null destination returns `Z_OK`;
- the state-allocation failure returns `Z_OK`;
- the buffer-failure path keeps `dest->state`;
- the buffer-failure path skips the free of `pending_buf`;
- the copy's back pointer is set to the source.

Each is rejected by the replay; the replay of `deflate_copy_public` peaks at about 10.4 GB. The
refusal goals `Goal.inflate_refusal` and `Goal.deflate_refusal` have no key. Their rows are in
`tests/proof-mutants/stream-refusal.tsv`, which the mutation shards check by re-elaboration: each
row turns a refusal into `Z_OK`.

### Per-function safety goals

For most functions the rows of the safety goal are the rows of the functional goal: the safety
proofs of the stream calls are corollaries of the sequence theorems
(`inflate_sequence_safety_public`, `deflate_sequence_safety`, clause 2 for a call and clause 3 for
`End`), and those of the init, copy and stateless functions are corollaries of their functional
proofs, so the same translation edits must break them. Functions without such rows have rows in
`tests/proof-mutants/public-safety.tsv`, all structural:
- `compress`, `compress_z`, `compress2`: the length pointer is not passed on (`NULL` instead). The
  row of `api-boundary.tsv` that makes `compress2` return on a `NULL` `destLen` is not a mutant of
  `Goal.compress2_safety`: the C reads `*destLen` first, so the goal excludes a `NULL` length
  (`CompressorSafety` with `nullableLength = false`), and the replay accepts that row;
- `uncompress2`: the destination length is read from `sourceLen`; the free of a local cell is dropped;
- `uncompress_z`, `uncompress`: the source-length cell is passed as the destination length; the free
  of the local cell is dropped;
- `deflateBound`: the result is dropped; `deflateBound_z`: the state check is dropped;
- `deflatePrime`: the `bits > 16` test is dropped; the pending room test is dropped;
- `inflateSync`: the local buffer has three bytes, not four.

`deflateParams` and `deflateSetDictionary` use their refusal rows of `stream-refusal.tsv`. A dropped
`deflateEnd` or `inflateEnd` call is a row of `compress2_z` and `uncompress2_z`, the functions that
make the call. `Goal.deflate_initialisation_domain` has no key: it states the successful
runs of `deflateInit2_`, and the four `deflateInit2_` rows are its mutants: a kernel replay of
`deflate_initialisation_domain_public` rejects all four (peak about 3.4 GB).

### `Goal.inflate_back_sequence_safety`

Its eleven rows are in `tests/proof-mutants/infback-sequence.tsv`: four of `inflateBack`, four of
`inflateBackInit_` and three of `inflateBackEnd`, all structural:
- `inflateBack`: a null stream returns `Z_OK`; the mode is not reset to `TYPE`; the output starts at
  `NULL`, not the window; a refused last window after the end returns `Z_OK`;
- `inflateBackInit_`: the state is not stored in the stream; the window is not stored; an allocation
  failure returns `Z_OK`; `sane` is cleared;
- `inflateBackEnd`: the free of the state is skipped; `strm->state` is kept; it returns `Z_STREAM_ERROR`.

The row of the epilogue is a script (`infback-sequence.py`) that makes the same edit in the restatement
`backTail`, so that a semantic lemma fails and not the `rfl` of `inflateBack_eq`. The mutation shards
check the rows by re-elaboration. A kernel replay of `inflate_back_sequence_safety` with the
translation edit of each row also rejects all eleven; the replay of the original peaks at about 9.8 GB.

### The gz goals

The gz goals have no key; their rows are three semantic lists.
- `tests/proof-mutants/gz-refusal.tsv`, for `Goal.gz_refusal`: nineteen rows, each a different return value on a
  `NULL` handle or a dropped `NULL` test, of every gz function except `gzread` and `gzfread` (in `gz-read.tsv`) and
  `gzbuffer`, `gzeof` and `gzoffset64` (in `public-streams.tsv`). The goal's clauses hold by evaluation, so each row
  fails in `public-gz-refusal`.
- `tests/proof-mutants/gz-sequence.tsv`, for `Goal.gz_sequence_safety`: the write calls (`gzwrite`, `gzfwrite`,
  `gzputc`, `gzputs`, `gzvprintf` and so `gzprintf`, `gzflush`, `gzsetparams`), the closes (`gzclose_w`, `gzclose_r`,
  the dispatch of `gzclose`), the opens (`gz_open`, `gzdopen`), `gzseek64` and `gztell64`, `gz_error` (a skipped free;
  a message allocated for `Z_MEM_ERROR`), both branches of the `gzgetc()` macro (`zlib.h.lean`: the `have` test dropped;
  `pos` not advanced), the read leaves `gzgetc`, `gzungetc`, `gzgets` and `gzdirect`, and one row per hunk of
  patches 0002 to 0005 that removes the hunk (the unpatched C). Most rows are script rows (`gz-sequence.py`) that make
  the same edit in each `rfl` restatement of the code (`gzwrite_eq`, `putcSlow`, `closeTail`, `pfFmt`, `gTail`,
  `seekTail`, `openAfterMode`, `fetchBody`, `restK`, `getsRest`, the private copies of `gz_error`), so that a semantic
  lemma fails, not the restatement.
- `tests/proof-mutants/gz-read.tsv` (with `gz-read.py`), from the read side: `gzread`, `gzfread`, the refusals of
  `gzgetc` and `gzungetc`, and `gzclose_r`. Its two `gzungetc` rows `gzungetc-mode-check` and `gzungetc-skip-dropped`
  name the step lemma's module `gz.read-getc-step` as well: with `gzread.c.getc-ungetc` alone the proof of
  `gzungetc_step` is not built, and both rows built; with it both are killed there.

**Where the first error lands.** Each row is killed in a proof of the mutated function: its step lemma, the exact run
of its body, or (for a callee) the proof of that callee. Five rows name modules beyond the step lemma, all proofs of
the mutated function: the three `gz_open` rows fail in the exact runs of `gz_open` (`gz_open_empty_mode` in
`gzlib.c.open-init`, `openAfterPath_writer` in `gzlib.c.open-io`: the I/O tail of `gz_open`, which frees the path and
calls `gz_reset`), the `gzdopen` row in the run of `gzdopen` (`gzdopen_writer_regular_run`, `gzlib.c.dopen-entry`),
and the `gztell64` row in the run of `gztell64` (`gztell64_run`, `gzlib.c.simple`). The `gzclose_w` rows fail in
`closeTail_ok` (`gzwrite.c.close`), the release proof of `gzclose_w`; the dispatch row of `gzclose` in
`gzclose_dispatch`. One row is killed by a heartbeat timeout, not a type error: `patch0004-fetch-copy-room-removed`
in `fetch_look` (`gz.read-fetch`), a proof of the same function `gz_fetch`.

**A row that found a wrong goal.** The row `macro-have-guard-dropped` survived at first: the goal ran the macro only
with `x.have ≠ 0`, so its `have = 0` branch was never run. The goal was corrected (3c5292f7; regression
`tests/verification/regressions/gz-macro-have-zero.lean`) and the row is now killed in `zlib.h.gzgetc-macro`.

**Kernel replay of the gz lists.** The mutation shards check the three lists by re-elaboration. A kernel replay of
`gz_refusal` rejects all nineteen refusal rows (each replay ends within two seconds). A kernel replay of
`gz_sequence_safety_public` with the translation edit of each structural row (the rows in a loop body or in machine
arithmetic left out: `patch0003-*`, the three `patch0004` rows of `gz_fetch` and `gz_read`,
`patch0004-gets-room-removed`, `gzgets-left-whole-length`, `gztell64-adds-max`) accepts the original (51615
dependencies, peak about 10.7 GB) and rejects 29 of the 36 rows it was given, most at the restatement of the mutated
function (`gzwrite_eq`, `gzclose_w_eq`, `gzgetc_macro_eq`, ...), peaks 10.7 GB. Seven rows reach the 12 GiB budget
before a verdict: `gzvprintf-length-check-dropped`, `gz_open-open-failure-path-leak`, `gz_open-reset-skipped`,
`gzseek64-have-not-consumed`, `gzseek64-skip-wrong`, `patch0005-seek-next-unconditional` and
`patch0004-printf-position-check-removed`. Their functions (`gzvprintf`, `gz_open`, `gzseek64`) contain a loop, and
the kernel unfolds it when the bodies differ; for these rows the re-elaboration kill is the evidence.

# Contributing

This page lists the steps of four tasks: making any change, registering a proved goal, running
the acceptance suite, and running the proof mutants on request. Each step gives the command and the last line it prints on
success. Run every command from the repository root.

The rules are in `AGENTS.md`. What each check establishes, and the three levels checked,
registered and accepted, are in [the checking guide](README.md#three-levels).

**Which last lines are exact.** A line marked "(run)" was copied from a run of the command. It
is a sample: a number in it changes with the repository and is written `N` here; the current
numbers are in [progress](../progress.md#scope). A line marked "(from the script)" is the text the script prints on success,
read in its source; the command needs a Lean build and was not run for this page.

## Every change

1. Get the sources, including the upstream submodule. In a clone made without the submodule, run
   `git submodule update --init zlib`.

   ```bash
   git clone --recurse-submodules <repository-url>
   ```

2. Work on a branch from `dev`. Commit small steps. Stage files by path. Push to `dev`, or merge a
   pull request into `dev` once the fast gate is green. No review is needed.

3. Build the library and the audit tools. Use at most four parallel jobs and a 16 GB limit. The
   proofs of `crc32.c` and `inftrees.c` need 8 to 9 GB each.

   ```bash
   lake build ZlibF zlibf-audit zlibf-span zlibf-proof-replay
   ```

4. Run the other checks of the fast gate.

   | Command | Needs the build of step 3 | Last line on success |
   | --- | --- | --- |
   | `scripts/check-sorry.sh` | no | `sorry count: 0` (run) |
   | `python3 scripts/check-strlit.py` | no | `check-strlit: N literals used, all in strTable (N entries)` (run) |
   | `python3 scripts/check-spec-layers.py` | no | `specification layers: N safety and common modules import no functional module` (run) |
   | `lake env lean --run tests/audit/PartialCheck.lean` | yes | not run for this page |

   The last check is a search that prints nothing on success (run):

   ```bash
   grep -rnE '\b(native_decide|bv_decide|implemented_by)\b|^\s*axiom\b' ZlibF.lean ZlibF
   ```

   It is a short form of the pattern in `lean.yml`, which also rejects `partial`, `unsafe`,
   `opaque` and `extern`.

5. If you changed `patches/`, check that every patch applies to the pinned upstream source. The
   commands print nothing when every patch applies. They were not run in this form for this page;
   the five patches were applied to a copy of the pinned source with `patch -p1`, without error.

   ```bash
   rm -rf /tmp/zlib-verified && cp -r zlib /tmp/zlib-verified && rm -rf /tmp/zlib-verified/.git
   for p in patches/*.patch; do (cd /tmp/zlib-verified && git apply "$OLDPWD/$p"); done
   ```

6. If you changed `docs/`, build and check the website. Use Python 3.12 or newer.

   ```bash
   python3 -m pip install -r docs/web/requirements.txt
   python3 docs/web/build.py
   python3 docs/web/check.py
   node --test docs/web/tests/*.test.mjs
   ```

   `build.py` ends with `Built the landing page and the status summary` (run). `check.py` ends with
   a line that starts `Static checks passed:` and gives the number of pages (run); a broken link
   or anchor stops it with an `AssertionError` that names the page and the link. The `node` run
   ends with a summary in which `# fail 0` is the line to read (run).

7. Every English document has a Chinese twin `*.zh.md` next to it. The twin of a file outside
   `docs/` is under `docs/web/content/repository/`. The twin's first line records `source-sha256`
   of the English file. After you edit the English file, update the Chinese text in the same
   commit and set the hash.

   ```bash
   sha256sum docs/glossary.md
   ```

   Where `sha256sum` is missing, `shasum -a 256` prints the same hash.

   A stale twin does not fail the build. The Chinese page then shows a notice that the English
   source is newer.

8. Push to `dev`. The fast gate (`build`, `no-sorry`) runs on every push and pull request.
   It is the only gate for merging. If a push breaks it, fix that first.

A change to the translation also needs a differential test that would catch the old behaviour
(`AGENTS.md`). A change to a goal or a specification goes in its own commit, with the
counterexample kept under `tests/verification/regressions/`.

After step 8 with a green fast gate, a new theorem is **checked**.

## Register a result

Registration is done in batches at a milestone, not for each change. A milestone is `inflate`
proved, `deflate` proved, a sequence goal proved, or about twenty newly checked goals.
[Public goals](goals.md#what-a-registration-needs) says why each item is needed.

The example is the safety goal of `adler32`. Its registry lines are real: they are in the files
named.

1. **Check the theorem's type.** The type is exactly the goal: no extra premise, no other
   constant. The theorem has a doc string; the auditor rejects a registered theorem without one.
   If the goal's precondition is narrower than zlib.h, the doc string says so, and
   `docs/deviations.md` has a row for it.

   ```lean
   /-- `Goal.adler32_safety`: `adler32` runs without fault on every input its contract allows; ... -/
   theorem adler32_safety : Goal.adler32_safety := ...
   ```

   (`ZlibF/Proof/public-stateless-safety.lean`. The goal is defined in
   `ZlibF/Spec/Safety/Checksums.lean`.)

2. **Add the theorem to `tests/audit/theorems.txt`**: its fully qualified name, on a line of its
   own.

   ```text
   ZlibF.Spec.Public.StatelessSafetyProof.adler32_safety
   ```

3. **Add the goal to `tests/audit/proved-goals.txt`**: its fully qualified name, on a line of its
   own.

   ```text
   ZlibF.Spec.Public.Goal.adler32_safety
   ```

4. **Only for a goal that is new**: add the same goal name to `tests/audit/goals.txt`. The auditor
   rejects a `Goal.*` proposition of the library that is not listed there.

5. **Only for a goal that is new to the required set**: add its name to the group `safety_goals`
   of `tests/audit/public-api.json`, and to the list of the same name in the function `coverage` of
   `scripts/verification.py`. For the safety goal of one function, also set the `safety_goal` field
   of that function's entry in the manifest:

   ```json
   "safety_goal": "ZlibF.Spec.Public.Goal.adler32_safety"
   ```

   The change to `scripts/` is reviewed. If the goal is listed in `open_safety` of the manifest,
   remove that entry in this commit: a goal is not both open and proved.

6. **Add mutant rows.** A goal of one public function needs a key in
   `tests/audit/public-mutants.json` that names at least one mutant row. The audit checks that
   the key and the row exist; it does not run the row. The rows are there so that a later mutant
   run covers the goal.

   ```json
   "ZlibF.Spec.Public.Goal.adler32_safety": [
     {"list": "tests/proof-mutants/public-checksums.tsv", "name": "adler32-wrapper-length"}
   ]
   ```

   [Proof mutants](proof-mutants.md) explains this row and how to write one. Run the new row
   once, to see that the proof rejects it. This needs the build of step 3 above (a warm `.lake`) and builds four proof modules twice.

   ```bash
   bash tests/audit/proofmut.sh tests/proof-mutants/public-checksums.tsv '^adler32-wrapper-length$'
   ```

   Last line: `PROOFMUT PASS` (from the script).

7. **Check the inventory.** This needs the submodule and no build.

   ```bash
   python3 scripts/verification.py coverage
   ```

   Last two lines (run):

   ```console
   coverage: N public declarations, N default-build entries (N documented, the rest undocumented in zlib.h), N sequence targets, N non-vacuity targets, N safety targets; N required goals, N open
   coverage is not specification readiness or proof completion
   ```

   A failure prints one line `REJECTED: <reason>`. The second line above is a reminder: this
   command checks that the manifest, the header and the keys agree. It does not check any proof.

8. **Regenerate the progress view**, the block between the `proof-progress` markers in
   `docs/progress.md` and `docs/progress.zh.md`. It needs the build of step 3 above.

   ```bash
   python3 scripts/proof-progress.py
   python3 scripts/proof-progress.py --check
   ```

   Each prints one JSON line with the number of targets and their states; the second has
   `"checked": true` (from the script). A stale view makes the second command fail with
   `Progress generation failed: ...`.

9. **Commit the registry lines, the mutant rows and the regenerated view together, and push.**
   The goal is **registered** on that commit. It is not accepted yet: the lines are a claim until
   the acceptance suite has checked them.

## Run acceptance

The acceptance suite is the workflow `lean` started by hand, or its nightly run on `main`. The
local commands below are its parts. Run them before starting the workflow when a failure would be
slow to find in CI.

1. **The audit.** It needs the full history (`git fetch --unshallow` in a shallow clone) and the
   base branch `origin/main`.

   ```bash
   python3 scripts/verification.py specs
   ```

   Last line: `stage passed: specs` (from the script). A failure prints `REJECTED: <reason>`; when
   the auditor rejects, the lines before it start with `goal ` or `PROBLEM:`.

2. **The differential tests**, plain and with the C under the sanitizers.

   ```bash
   ZLIB_SRC=$PWD/zlib bash tests/run.sh
   SAN=1 ZLIB_SRC=$PWD/zlib bash tests/run.sh
   ```

   Each ends with exit status 0; the script stops at the first driver or regression that fails
   (from the script). The suite also runs two self tests, `bash tests/audit/selftest.sh` and
   `bash tests/selftest.sh`; the second ends with `SELFTEST PASS` (from the script).

3. **Start the suite on the pushed commit.** On the repository's Actions page, choose the workflow
   `lean`, then "Run workflow", then the branch `dev`. Leave the option `mutants` off. The
   workflow has a manual trigger (`workflow_dispatch` in `.github/workflows/lean.yml`); with it,
   the acceptance workers run in addition to the fast gate.

4. **Read the two results.** The run is green when its results `audit` and `difftest` are both
   green. Each of them fails when one of its workers fails, is skipped or is cancelled. The
   mutant stage is skipped in such a run, and `audit` does not need it.

5. **Report.** The result is **accepted** on that commit. A report says "accepted" together with
   the commit hash, and [progress, Scope](../progress.md#scope) records the commit. `main` receives
   `dev` after that.

Never report a check as passing unless it was run. Differential tests are evidence of fidelity,
not proof.

## Run the proof mutants

The mutants are additional evidence, not part of acceptance. They run only on request, and they
gate no merge, no acceptance and no milestone. A full run takes several hours.

1. **In CI.** Start the workflow `lean` by hand as above, with the option `mutants` on. The job
   `audit_mutants` then runs twenty shards (`--shard-count 20 --shard-index N`), and the result
   `audit` of that run also requires every shard to pass.

2. **Locally.** This runs every shard in one process and takes many hours.

   ```bash
   python3 scripts/verification.py mutants
   ```

   Last line: `stage passed: mutants` (from the script).

3. **Report.** A mutant run is reported separately from acceptance, with its commit.
   [Progress, Scope](../progress.md#scope) records it.

## Removing or changing a registered item

The audit rejects a registered theorem, a proved goal, a mutant reference or a frozen mutant row
that disappears or changes ([rules against silent removal](goals.md#shrink-only-rules)). When a
removal is right, add an entry with a reason to `tests/audit/registry-removals.json` in the same
commit. The entry is the reviewed record of the removal. The audit rejects an entry that excuses
nothing.

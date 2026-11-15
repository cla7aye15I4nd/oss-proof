# Contributing

This page lists the steps to change the proofs, the translation or the documentation, and the
steps that turn a checked result into an accepted one. Run every command from the repository
root. The rules are in `AGENTS.md`. What each check establishes is in [the checking guide](README.md).

The commands are those of the workflow `.github/workflows/lean.yml` and the scripts it calls.
For this page, the three script checks of step 4 and the site commands of step 6 were run; the
Lean builds and the acceptance commands were not re-run.

## Two levels

- **Checked.** The theorem is on `dev`, and the fast gate is green on that commit.
- **Accepted.** The theorem is also in `tests/audit/theorems.txt`, and the acceptance suite is
  green on a named commit. Only an accepted result is final.

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

   ```bash
   scripts/check-sorry.sh
   python3 scripts/check-strlit.py
   python3 scripts/check-spec-layers.py
   lake env lean --run tests/audit/PartialCheck.lean
   grep -rnE '\b(native_decide|bv_decide|implemented_by)\b|^\s*axiom\b' ZlibF.lean ZlibF
   ```

   The first three need no build. The fourth needs the build of step 3. The `grep` must print
   nothing; it is a short form of the pattern in `lean.yml`, which also rejects `partial`, `unsafe`,
   `opaque` and `extern`.

5. If you changed `patches/`, check that every patch applies to the pinned upstream source.

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

## At a milestone

Acceptance work is done in batches, not for each change. A milestone is `inflate` proved,
`deflate` proved, a sequence goal proved, or about twenty newly checked targets.
[Public goals](goals.md#what-a-registration-needs) says what a registration needs and why.

1. Give each theorem a doc string. The auditor rejects a registered theorem without one.

2. Register the theorem and its goal. Add the theorem's fully qualified name to
   `tests/audit/theorems.txt` and the goal's name to `tests/audit/proved-goals.txt`, one name per
   line. If the goal is listed in `open_safety` of `tests/audit/public-api.json`, remove that entry.

3. Add proof mutants for each newly proved public function, and key them in
   `tests/audit/public-mutants.json`. A mutated translation must fail to check, with the error in
   that function's proof. [Proof mutants](proof-mutants.md) gives the format and the rules. Run
   one list to try it:

   ```bash
   bash tests/audit/proofmut.sh tests/audit/proofmut/adler32.tsv
   ```

4. Check the inventory. This needs the submodule and no build.

   ```bash
   python3 scripts/verification.py coverage
   ```

5. Regenerate the progress view, the block between the `proof-progress` markers in
   `docs/progress.md` and `docs/progress.zh.md`. It needs the build of step 3 above.

   ```bash
   python3 scripts/proof-progress.py
   python3 scripts/proof-progress.py --check
   ```

6. Run the audit and the mutants. Both need the full history (`git fetch --unshallow` in a shallow
   clone) and the base branch `origin/main`.

   ```bash
   python3 scripts/verification.py specs
   python3 scripts/verification.py mutants
   ```

   The second command runs every shard in one process and takes many hours. In CI the mutants run
   in twenty shards (`--shard-count 20 --shard-index N`).

7. Run the differential tests, plain and with the C under the sanitizers.

   ```bash
   ZLIB_SRC=$PWD/zlib bash tests/run.sh
   SAN=1 ZLIB_SRC=$PWD/zlib bash tests/run.sh
   ```

8. Run the acceptance suite on the pushed commit: start the `lean` workflow with its manual
   trigger on `dev`. Steps 4 to 7 are its local parts; the suite also runs the self tests of the
   auditor and of the differential harness.

9. When the suite is green, report the result as accepted and name the commit. `main` receives
   `dev` after that.

Never report a check as passing unless it was run. Differential tests are evidence of fidelity,
not proof.

## Removing or changing a registered item

The audit rejects a registered theorem, a proved goal, a mutant reference or a frozen mutant row
that disappears or changes ([shrink-only rules](goals.md#shrink-only-rules)). When a removal is
right, add an entry with a reason to `tests/audit/registry-removals.json` in the same commit. The
entry is the reviewed record of the removal. The audit rejects an entry that excuses nothing.

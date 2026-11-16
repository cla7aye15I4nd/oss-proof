# Working rules

Goal: kernel-checked Lean 4 proofs about a faithful translation of upstream zlib `develop`.
The goal is full safety (no undefined behaviour, no memory error, no leak, termination) of every
public function, for the default x86_64 Linux build: `inflate` and `deflate` with their call
sequences, the other public functions, the gzip file interface and the callback decoder
`inflateBack`. One functional result is planned as well (owner's decision of 2026-11-15): the
round trip of the default zlib stream, with completeness, described below. Other functional goals
beyond what safety needs are not planned (owner's decision of 2026-11-11, to finish sooner): a
functional fact that a planned proof depends on is in scope. What is already proved stays. The
functions that zlib.h lists under "undocumented
functions (not part of the zlib API)" are not required. Read `docs/overview.md` first, then
`docs/spec/safety.md`. Keep proof explanations in `docs/proof/`. State the status only in
`docs/progress.md`, as done or not done (section Documents).

The project is finished when the safety results are accepted, in this order: `inflate` is safe on
every input; `deflate` is safe on every input; then every other public function, including the
gzip file interface and `inflateBack`. Each covers its call sequences, and the safety of `compress`
and `uncompress` follows as compositions.

After the safety results comes the round trip, for the default zlib stream (`deflateInit` at the
default level, `inflateInit`), in this order. First the conditional form: when a `deflate` call
sequence and an `inflate` call sequence both reach `Z_STREAM_END`, under any flush values and any
chunking, the bytes `inflate` writes are the bytes `deflate` read. Then completeness: with enough
output room and successful allocation, `deflate` with `Z_FINISH` consumes all input and ends; one
`deflate(Z_FINISH)` call ends when the room is at least `deflateBound`; `compress` returns `Z_OK`
when the room is at least `compressBound`; and `inflate` reads every stream the format accepts to
`Z_STREAM_END`. Then the unconditional results: the stream round trip, and
`uncompress(compress(x)) = x`. A `sorry` for these lives only on a skeleton branch.

Other functional correctness (other levels, strategies, window sizes and wrappers, preset
dictionaries, the gzip file interface and `inflateBack` as round-trip partners), model-only
statements and other build configurations are not planned. The undocumented functions are not required public targets;
proofs already registered for them stay. `docs/progress.md` lists what is not planned, with
the reason. Do not work on a not-planned target unless a planned one needs it. Work as fast as
honest work allows: process
exists to keep the result honest, not to slow it down.

## Source

- `zlib/` is the upstream submodule. Never modify it. The verified source is `zlib/` plus
  `patches/*.patch` applied in name order.
- A patch is allowed only for a confirmed zlib bug that blocks a proof. It must be minimal, match
  a fix submitted upstream, and be listed in `patches/README.md`. A patch may land before its
  upstream submission when the owner approves it; `patches/README.md` then marks it as local and
  pending, and it is replaced by the upstream fix when one exists. Delete a patch once upstream
  merges the fix and the pin moves past it.
- Translations mirror the C layout: `zlib/X.c` is `ZlibF/Zlib/X.c.lean`, and `zlib/X.h` is
  `ZlibF/Zlib/X.h.lean`. Each function keeps its C name, and its docstring starts with the C
  signature.
- Specifications are in `ZlibF/Spec/`. Proofs about `zlib/X.c` are in
  `ZlibF/Proof/X.c.<topic>.lean`. Proofs of public goals are in `ZlibF/Proof/public-<name>.lean`.
- Heap-free mathematics goes to `ZlibF/Math/`. The runtime (heap, pointers, loops, faults) is
  `ZlibF/Runtime/*.lean`.

## Translation

- Translate statement by statement. Do not reorder, merge or simplify.
  Four normalisations are accepted (owner's decision of 2026-11-15) and are not translation bugs:
  an out-parameter of an internal function is passed by value and returned as a second result;
  two reads of one location with no store between them are one read; consecutive assignments to
  fields of one record are one record update; a signed operation that a preceding test of the
  same function keeps in range uses the plain operator. Anything else is a translation bug.
  `docs/design/translation.md` shows an example of each.
- Every undefined behaviour the C can reach raises `Fault.ub`. Unsigned arithmetic wraps. Signed
  arithmetic is checked.
- Reading an uninitialised integer returns an arbitrary value, and a theorem must hold for every
  value. A pointer in fresh memory is NULL in the model, which is weaker than C: the proof shows that a pointer
  field was written before it is read (`docs/spec/safety.md`, section 3; `docs/trusted-base.md`, item 2).
- Never change a translation to make a proof easier. A mismatch with the C is a translation bug.
  Fix it, and add a differential test that catches it.
- Every proof depends on the runtime. Change it only for a confirmed mismatch with C.

## What counts as proved

There are two levels. Say which one you mean.

- **Checked.** The theorem is on `dev`, and the fast gate is green on that commit: everything
  builds, there is no `sorry`, and no forbidden construct. Lean's kernel has checked the proof.
  Day-to-day work is merged at this level.
- **Accepted.** The theorem is also listed in `tests/audit/theorems.txt`, and the acceptance suite
  is green on a commit you name: axiom gate, exact goal match, self tests and
  differential tests. Only an accepted result may be reported as final.

Proof mutants are additional evidence, not part of acceptance (owner's decision of 2026-11-15:
a full mutant run takes several hours). A mutant run is reported separately, with its commit.

Rules that hold at both levels:

- Only `propext`, `Classical.choice` and `Quot.sound` are allowed. Never use `sorry`,
  `native_decide`, `bv_decide`, `axiom`, `implemented_by`, `extern`, `unsafe`, `partial` or
  `opaque`. Do not look for ways around the checks; report the obstacle.
- A goal is proved only by a theorem whose type is exactly the goal.
- A theorem states its precondition explicitly. A precondition narrower than `zlib.h` allows is
  written in the theorem's docstring and listed in `docs/deviations.md`. Never shrink the domain
  silently.
- **Disjoint caller regions.** Caller-supplied memory regions with no semantic reason to overlap
  may be assumed fully disjoint when that makes the proof simpler: input, output, window and
  dictionary buffers, the `gz_header` record and its extra, name and comment buffers, and length
  cells. The premise is only that their byte ranges do not overlap: the regions may lie in one
  heap block. A caller string (the gzip `name` and `comment`) is assumed NUL-terminated, and its
  range is the string through its NUL. Each such premise stays explicit in the statement and gets
  a row in `docs/deviations.md`; no sanitizer reproduction is needed first. This does not allow
  narrowing by parameter value, or dropping a reachable case in which the regions do not alias.
- **No callee contracts as assumptions.** A callee's specification is a theorem about the
  translated callee. A representation invariant is established by the init function, which also
  shows that the invariant can hold. A concrete witness is needed only for a top-level theorem.
- When a proof is stuck, decide which of four causes it is, without assuming the answer: the
  proof technique, a wrong specification, a translation bug, or a real zlib bug. For a possible
  zlib bug, build a concrete input, run the real C under a sanitiser, and report it with the
  reproduction. Never narrow a precondition to hide it.
- Differential tests are evidence of fidelity, not proof. Say so when reporting.

## Correcting a specification, a goal or a translation

A wrong statement is corrected, not worked around.

- Change it when there is evidence: a checked counterexample, or a documented mismatch with
  `zlib.h` or the C source. Put the correction in its own commit. Say what was wrong and why.
- Keep the counterexample as a regression under `tests/verification/regressions/`.
- Never weaken a statement, narrow a domain or change a translation to make a proof go through.
  Strengthening a weak goal is allowed and wanted.
- A translation mismatch with the C is a bug. Fix it and add a differential test that catches it.
- A change to `ZlibF/Runtime/` is its own commit, with the reason and the proofs it affects.

## Proof workflow

Each core result (`inflate`, `deflate`) has one owner. The owner works in this order.

1. **Test the statement first.** Before a long proof, check the goal against reality. Run the
   executable format specification against the real C on many inputs. Check each clause of the
   goal on small concrete cases. A wrong statement found here costs minutes; found during the
   proof it costs days. Correct it as the section above says.
2. **Build the skeleton top down.** On the branch `skeleton/<result>`, write the proof of the goal
   from named lemma statements, with the lemma proofs left open. `sorry` is allowed on a skeleton
   branch and nowhere else. The skeleton must type-check. It is the list of remaining work.
3. **Publish the list.** Keep the list of open lemmas in a comment at the head of the skeleton
   file on the skeleton branch: name, one-line meaning, state (open, checked), estimate in hours.
   Keep it current. It does not go into `docs/`.
4. **Close lemmas on `dev`.** Prove one lemma at a time and push it to `dev`. Reuse existing
   proofs where they fit the lemma as stated. Do not prove what the skeleton does not need.
5. **Hide large definitions behind an interface.** A representation invariant has a small set of
   interface lemmas. Other modules use those lemmas and do not unfold the definition. Then a
   change to the invariant rebuilds its interface, not hundreds of modules.
6. **Delete what the skeleton does not use.** A proof tied to a fixed parameter or a default
   configuration that cannot serve the general lemma is removed, unless a registered theorem
   needs it.
7. **Do not stop between lemmas.** Report at a milestone, at a statement correction, or after two
   hours without progress on one lemma. The report names what is checked, the commit, and the
   remaining estimate.

Owners work in parallel on separate files. Heavy builds on the shared build host run one at a
time: wait for the other owner's build to end before starting yours.

## Checking

**Fast gate, on every push and pull request** (`build`, `no-sorry`): all modules build, no
forbidden construct, patches apply to the pinned `zlib/`, no `sorry`. This is the only gate for
merging.

**Acceptance suite, every night on `main` and on request** (`audit`, `difftest`): axiom gate,
exact goals, self tests, differential tests with and without sanitisers.
Run it on request with the `lean` workflow's manual trigger. A red nightly run is fixed before
new acceptance work, but it does not block proof work.

**Proof mutants, on request only**: the manual trigger's `mutants` option. A mutated translation
(a dropped check, an off-by-one) must fail to check, with the error in that function's proof.
They do not gate a merge, acceptance or a milestone.

There are no lock files. A definition, a specification or a theorem statement is tracked by git
alone: its history is the record of what changed and why. The protection that remains is the
audit itself: allowed axioms only, and a goal is proved only by a theorem of exactly that type.

Work that belongs to acceptance is done in batches at a milestone, not for each change:

- registering theorems in `tests/audit/theorems.txt`;
- proof mutant rows for each newly proved public function, so that a later mutant run covers it;
- updating the rows of `docs/progress.md`.

A milestone is one of: `inflate` proved, `deflate` proved, a stream sequence goal proved, or
about twenty newly checked targets. Never report a check as passing unless it was run.

Full builds use a lot of memory. `ZlibF/Proof/crc32.c.lean` and `ZlibF/Proof/inftrees.c.lean`
each need 8 to 9 GB. Build with at most four parallel jobs under a 16 GB limit. If one module
needs more than that, find out why before raising any limit.

## Findings

Record a confirmed zlib issue in `README.md`: give a short description, link a reproduction under
`docs/findings/`, and state the confidence and the scope. Keep an unconfirmed report out of `docs/`: it stays under
`tests/regression/<name>/`, marked unconfirmed, until it is confirmed or withdrawn. Every new sanitizer reproduction goes under `tests/regression/<name>/` with
`run.sh`, `report.txt` and a row in `docs/sanitizer-reports.md`.

## Documents

- File names are lowercase, with hyphens: `method.md`. `README.md` and `AGENTS.md` keep their
  conventional names.
- Write short sentences. Say what is proved, what is assumed, and what is not done.
- The documentation is for a reader who wants to know what was verified. It is about the
  specifications and the proofs. A result has one of two states there: **done** (a theorem whose
  statement is exactly the goal exists and passes every check) or **not done**; add "not
  planned" where it applies. The levels of the section "What counts as proved" are working terms
  and do not appear in `docs/` or `README.md`.
- Keep out of the documentation: commits, runs, pull requests, branches, dates of project
  events, gates and suites, registry files, the folder layout as a subject, the history of how a
  statement or a page changed, remaining-work lists and estimates, and any term that only has a
  meaning inside the project. Evidence may be named (differential tests, a reproduction under a
  sanitizer) without describing how it is stored or run.
- `docs/progress.md` is the only page that states a status: each result and each public function,
  done or not done, and what is not planned.
- Mark a reading of the C that the proof must still confirm with **to confirm**.
- Use diagrams (mermaid) for structure and order. Do not use a diagram for a list.
- Do not put machine names, addresses, user names, local paths or tool names in the repository.

## Collaboration

- Work lands on the integration branch `dev`. Commit small, self-contained steps and push them
  there directly, or merge a pull request into `dev` as soon as the fast gate is green. No review
  is needed. Keep `dev` building: if a push breaks the fast gate, fix it before anything else.
- `main` receives `dev` at each milestone, after the acceptance suite is green on that commit.
- Parallel work uses separate C files or functions. Two workers never edit the same file.
- Prove the universal goal. Do not add proofs for a fixed parameter or a default configuration
  unless they are a lemma of the universal proof.
- Commit messages describe the change. They carry no attribution lines for tools.
- Report what is checked, what is accepted and what is open. Name the commit.

[docs/anti-cheating.md](docs/anti-cheating.md) says why a green build can still be worthless,
and what the acceptance suite defends against.

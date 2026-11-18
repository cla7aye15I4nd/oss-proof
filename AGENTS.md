# Working rules (`oss-proof`)

Goal: kernel-checked Lean 4 safety proofs (and explicitly scoped functional theorems where stated)
about faithful, statement-by-statement translations of upstream open-source C libraries, verified
under one shared checking infrastructure (`framework/`) and published under one bilingual site
(`site/`, hosted at `https://www.dataisland.org/oss-proof/`).

Each verified C library lives in `projects/<id>/` with its own Lake package (`<Package>`), pinned
upstream submodule, minimal patches (`patches/`), specifications (`<Package>/Spec/`), proofs
(`<Package>/Proof/`), goal registry (`<Package>/Results.lean`), differential test suite (`tests/`),
bilingual documentation (`docs/en/`, `docs/zh/`), and project-specific `projects/<id>/AGENTS.md`.
Both this root `AGENTS.md` and `projects/<id>/AGENTS.md` apply when working on `projects/<id>/`;
on any shared rule (proof soundness, allowed axioms, C undefined behaviour, translation fidelity,
anti-cheating), this root `AGENTS.md` is authoritative.

Work as fast as honest work allows: process exists to keep the result honest, not to slow it down.

## Repository layout

- `lean-toolchain` — single pinned Lean 4 toolchain shared across every project (`projects/<id>/lean-toolchain` and `projects/<id>/tests/lean-toolchain` must equal it byte-for-byte).
- `framework/` — shared verification gate (`check_project.py`, `check_options.py`, `check_forbidden.py`, `check_runtime_ub.py`, `check_spec_layers.py`, `ci_matrix.py`), reusable Lean checkers (`framework/lean/ResultsCheck.lean`, `framework/lean/PartialCheck.lean`), strict runtime reference (`framework/lean/StrictPtr.lean`), project registry (`framework/projects.json`), and `framework/TEMPLATE_AGENTS.md`.
- `site/` — unified static site builder (`site/build.py`) and auditor (`site/check.py`), rendering the `oss-proof` portal (`site/dist/{en,zh}/`) and each project's subsite (`site/dist/<id>/{en,zh}/`).
- `projects/<id>/` — one verified C library per directory (currently `projects/zlib/`; incoming `*-f` libraries drop into `projects/<id>/` with a `project.json` manifest).

## Source and patches

- `projects/<id>/<upstream>/` is the upstream git submodule. **Never modify it.** The verified
  source is `<upstream>/` plus `projects/<id>/patches/*.patch` applied in name order.
- A patch is allowed **only** for a confirmed upstream bug or ISO C17 undefined behaviour reachable
  through documented API calls that blocks a proof. It must be minimal, match a fix submitted
  upstream, and be listed in `projects/<id>/patches/README.md`. A patch may land before its
  upstream submission when the owner approves it; `patches/README.md` then marks it as local and
  pending, and it is replaced by the upstream fix when one exists. Delete a patch once upstream
  merges the fix and the pin moves past it.
- Translations mirror the C layout: `<upstream>/.../X.c` is `<Package>/<Lib>/.../X.c.lean`, and
  `X.h` is `X.h.lean`. Each function keeps its C name, and its docstring starts with the C
  signature.
- Specifications live in `<Package>/Spec/{Common,Safety,Functional}/`. No `Safety` or `Common`
  module may import a `Functional` module, and no `Spec` module may import `<Package>/Proof/`.
- Proofs about `X.c` live in `<Package>/Proof/X.c.<topic>.lean`. Proofs of public goals live in
  `<Package>/Proof/public-<name>.lean`. Heap-free mathematics goes to `<Package>/Math/`.

## Translation

- Translate statement by statement. Do not reorder, merge or simplify.
  Four normalisations are accepted and are not translation bugs:
  1. an out-parameter of an internal function is passed by value and returned as a second result;
  2. two reads of one location with no store between them are one read;
  3. consecutive assignments to fields of one record are one record update;
  4. a signed operation that a preceding test of the same function keeps in range uses the plain
     operator.
  Anything else is a translation bug.
- Never change a translation to make a proof easier. A mismatch with the C is a translation bug.
  Fix it, and add a differential test that catches it.
- Every proof depends on `<Package>/Runtime/`. Change a runtime file only for a confirmed mismatch
  with ISO C17, in its own commit, naming the reason and the proofs it affects.

## C Undefined Behaviour Policy (Strict ISO C17 — Non-Negotiable)

**ISO C17 (ISO/IEC 9899:2018) on LP64 Linux is the sole semantic standard.** Every undefined
behaviour reachable in ISO C17 MUST raise `Fault.ub` in `<Package>/Runtime/` and in the translation.

**Do NOT argue "benign UB".** Agents must NEVER argue that an ISO C17 undefined behaviour is
"defined in C++", "permitted in C2y", "compiled to a no-op on x86_64", "accepted by GCC/Clang
without crashing", or "too strict in the runtime model". The owner has explicitly ruled all of the
following **unsupported** (`Fault.ub`):

| C construct | ISO C17 clause | Required model behaviour |
| --- | --- | --- |
| **Wild / uninitialised / freed ("dangling") pointer `+ 0` or `- 0`** (`p + 0`, `p += 0`, `&p[0]` when `p` is uninitialised or points into a freed block) | §6.5.6p8, §6.2.4p2 | **`Fault.ub`**. Never bypass pointer liveness or bounds checks when the offset `k` is `0` (`if k = 0 then .ok` is forbidden; see `framework/lean/StrictPtr.lean` and `framework/check_runtime_ub.py`). |
| **`NULL + 0`, `NULL - 0`, `&((T *)NULL)[0]`** | §6.5.6p8 | **`Fault.ub`**. C++ allows `nullptr + 0`; ISO C17 does not. `Ptr.add .null 0` must fault. |
| **`NULL - NULL` and `p - NULL`** | §6.5.6p9 | **`Fault.ub`**. Both operands of pointer subtraction must point into (or one past the end of) the **same live** array object. |
| **Cross-object pointer subtraction (`p - q`) and relational comparison (`<`, `<=`, `>`, `>=`)** | §6.5.6p9, §6.5.8p5 | **`Fault.ub`**, unless both pointers refer to `[0, size]` of the exact same live allocation. Never allow `virtualStart = buf - extSize` on `char *` across objects. |
| **Out-of-bounds pointer formation without dereference** (`p + k` outside `[0, size]` of its live array, even transiently before adding `-k` back) | §6.5.6p8 | **`Fault.ub`** at the exact point `p + k` is evaluated, whether or not the pointer is ever dereferenced. |
| **`memcpy`, `memmove`, `memset`, `memcmp` with `n == 0` and `NULL`, uninitialised, or dangling pointer** | §7.24.1p2, §7.1.4p1 | **`Fault.ub`**. Valid pointers to live objects are required even when the byte/element count `n` is `0`. |
| **Reading or using an uninitialised ("wild") pointer** | §6.3.2.1p2, §6.2.4 | Fresh struct pointer fields are represented as `.null` in the heap model, which is weaker than C: every struct pointer field MUST be written before it is read, offset, compared or freed. Never rely on default `.null` in fresh records to excuse an unwritten C pointer. |
| **Reading an uninitialised integer** | §6.2.6.1, §6.3.2.1 | Returns an arbitrary value from `Heap.garbage`; every theorem must quantify universally over all `Heap.garbage` functions. |
| **Signed integer overflow (`+`, `-`, `*`, unary `-`, `INT_MIN / -1`), division/modulo by `0`, and invalid shifts** (negative shift count, shift count `>= width`, or left-shift of a negative signed integer) | §6.5p5, §6.5.5, §6.5.7 | **`Fault.ub`**. Unsigned arithmetic wraps modulo $2^w$; signed arithmetic and shifts are explicitly checked. |
| **Out-of-bounds, dangling, or read-only dereference / store; `strlen` without in-object NUL; overlapping `memcpy`; invalid or double `free`** | §6.5.3.2, §7.22.3, §7.24 | **`Fault.ub`**. |

When upstream C executes any construct in this table on a path reachable from documented public API
calls:
1. Do **not** weaken `<Package>/Runtime/` and do **not** narrow the caller precondition to hide it
   (unless the library's own public header explicitly forbids that caller input).
2. Confirm the path on real C (under UBSan / ASan `detect_invalid_pointer_pair=2` where applicable,
   or by concrete trace for standard-letter UB such as `wild_ptr + 0` that hardware sanitizers miss),
   report it to the owner, record it in `docs/{en,zh}/findings.md`, and propose a minimal upstream
   C patch in `projects/<id>/patches/`.

*(Note on `projects/zlib`: `ZlibF/Runtime/Ptr.lean` currently retains a pre-existing legacy debt for
`Ptr.add p 0` and `Ptr.diff .null .null`, isolated in `LEGACY_PERMISSIVE_PTR_PROJECTS` of
`framework/check_runtime_ub.py`. That debt is scheduled for removal in its own dedicated PR and MUST
NEVER be copied to any other project or cited to justify permissive UB.)*

## What counts as proved

A result is proved when it is on `main`: `projects/<id>/<Package>/Results.lean` pairs its goal with
its theorem, and the `CI` gate was green on the pull request that brought it: everything builds with
`--wfail`, `Results.lean` passes (allowed axioms only, exact goal type, every goal listed, every
required goal proved), there is no `sorry` and no forbidden construct, public API coverage passes,
runtime UB checks pass, and differential tests pass under ASan + UBSan. A theorem on a branch is not
yet a result; say so when reporting it.

Rules that hold everywhere:

- Only `propext`, `Classical.choice` and `Quot.sound` are allowed. Never use `sorry`,
  `native_decide`, `bv_decide`, `axiom`, `implemented_by`, `extern`, `unsafe`, `partial` or
  `opaque` (except `sorry` on `skeleton/*` branches only). Do not look for ways around the checks;
  report the obstacle.
- A goal is proved only by a theorem whose type is syntactically equal to the goal.
- A theorem states its precondition explicitly. Any precondition narrower than the public C header
  allows is written in the theorem's docstring and listed in `projects/<id>/docs/en/deviations.md`
  (and `zh/deviations.md`). Never shrink the domain silently.
- **Disjoint caller regions.** Caller-supplied memory regions with no semantic reason to overlap may
  be assumed pairwise disjoint in byte range when that simplifies the proof (input, output, window,
  dictionary, header buffers, scalar out-cells). Each such premise stays explicit in the goal and
  gets a row in `deviations.md`. This never permits narrowing by parameter value or dropping valid
  non-aliasing cases (such as `NULL` buffer with length `0` when the public API allows it).
- **No callee contracts as assumptions.** Every internal helper's specification is a proved theorem
  about its translated C code. Representation invariants are established by init/create functions,
  paired with concrete non-vacuity witness theorems at the top level.
- Differential tests are evidence of translation fidelity, not proof. Say so when reporting.

## Proof workflow

1. **Bootstrap strict runtime and framework gates first.** Wire `projects/<id>/project.json` into
   `framework/projects.json` using `framework/lean/StrictPtr.lean`, `ResultsCheck.lean`, and
   `PartialCheck.lean` so every commit passes `python3 framework/check_project.py <id>` from day one.
2. **Test goal statements against real C first** before starting long proofs.
3. **Build the skeleton top down** on `skeleton/<id>-<result>` (`sorry` allowed only on `skeleton/*`
   branches). Keep open-lemma tracking in a header comment of the skeleton file, never in `docs/`.
4. **Hide large state invariants behind small interface lemmas** so editing an invariant clause does
   not rebuild hundreds of proof files.
5. **Delete unused proofs** that no goal in `Results.lean` depends on.
6. **Memory discipline.** Build with at most four parallel jobs (`-j 4`) under a 16 GB limit, and
   run heavy builds one at a time on shared hosts.

## Checking

One gate (`CI` workflow) runs on every pull request and every push to `main`:
- `framework` unit tests and path-scoped project matrix (`framework/ci_matrix.py`);
- `lake --dir projects/<id> build --wfail <targets>` (main builds from scratch and is the sole writer
  of the `.lake` cache; pull requests only restore `main`'s cache);
- `python3 framework/check_project.py <id> --skip-build` (options/lakefile/toolchain allow-list,
  forbidden constructs, strict runtime UB check, spec-layer DAG, string-literal table, `PartialCheck`
  on the compiled kernel environment, `ResultsCheck` fixtures, public API coverage, clean submodule
  and patch application);
- `differential-test` under AddressSanitizer and UndefinedBehaviorSanitizer whenever translations,
  runtime, patches, upstream submodule, or difftest harnesses change;
- `Docs` workflow (`python3 site/build.py && python3 site/check.py` + JS tests) when `site/` or
  project docs/specs change.

Never report a check as passing unless it was actually run.

## Findings and documents

- A finding goes in `projects/<id>/docs/{en,zh}/findings.md` only if it is a confirmed defect or
  ISO C17 undefined behaviour of the upstream C library itself, reachable through documented API
  calls.
- English and Chinese site sources live under `projects/<id>/docs/en/` and `docs/zh/` at mirrored
  lowercase-hyphenated paths, with no `.en.md`, `.zh.md` or folder `README.md` files. Repository
  files outside `docs/` link to `https://www.dataisland.org/oss-proof/...`.
- A result has only two states in reader-facing docs: **done** or **not done** (plus "not planned"
  where applicable). Keep commits, PRs, branches, CI jobs, registry filenames, folder layouts, and
  estimates out of reader-facing `docs/`.
- `projects/<id>/docs/{en,zh}/progress.md` is the sole status page of each project.
- Do not put machine names, addresses, user names, local paths or tool names in the repository or in
  commit messages.

See [anti-cheating](https://www.dataisland.org/oss-proof/zlib/en/anti-cheating.html) for why a green
build can still be worthless and what the gate defends against.

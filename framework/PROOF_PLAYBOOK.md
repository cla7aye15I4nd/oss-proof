# Proof Engineering Playbook (`oss-proof`)

This playbook distils proven patterns and failure modes from verifying large C libraries in Lean 4
under tight memory, CPU, and CI budgets. It supplements [`../AGENTS.md`](../AGENTS.md) with
concrete proof-authoring recipes.

---

## 1. Methodology: Contract-Free 4-Stage Hybrid

Experience across verified libraries shows that **pure top-down** decomposition with caller-invented
`_contract` assumptions fails badly (caller contracts are often false on real C, dummy witnesses
hide contradictions, and contract fixes ripple across every caller), while **unstructured bottom-up**
proving accumulates massive rework (parallel frame towers, invariant churn, and monolithic files).

Follow this **4-stage hybrid workflow** for every new library or major subsystem:

1. **Stage 0 — Freeze safety-only scope, translation, and differential tests (top-down)**
   - Define public `Goal.*_safety` statements under `<Package>/Spec/Safety/` first, with explicit
     caller-buffer **byte-range disjointness** premises documented in `docs/{en,zh}/deviations.md`.
   - Translate the in-scope C files statement by statement and wire ASan + UBSan differential tests
     early so translation mismatches are caught before long proofs start.
   - **Do not write speculative C patches upfront.** Add a patch only when a real public-API
     reproducer confirms an upstream bug or ISO C17 UB that blocks a proof.

2. **Stage 1 — Establish thin `Wp` + write-footprint + `grind` automation once**
   - Lean 4.36+ ships **`grind`** in its core standard library (zero external Lake dependencies,
     zero extra `set_option`s, pure kernel proof terms using only `[propext, Classical.choice,
     Quot.sound]`, no `bv_decide`). It handles congruence closure, linear arithmetic, and bounded
     `UInt*`/`Int*` no-wrap and shift reasoning cleanly under `--wfail`.
   - *(Note on `Std.Tactic.Do`: in Lean `v4.36.0`, `mvcgen` emits a deprecation warning and `vcgen`
     emits an experimental-feature warning requiring `set_option experimental.vcgen true`, which
     `framework/check_options.py` forbids under `--wfail`. Prefer a compact ~200-line `Wp` calculus
     over the project monad `M`, paired with `grind`, until `vcgen` stabilises without warnings.)*
   - Define (or share) the monad's `Wp` rules (`mono`, `pure`, `bind`, `bind'`, `ite`, `and`),
     decreasing-measure loop rules (`cwhile_measure`, `cfor`, `cdoWhile`), primitive `Ptr`/`Libc`
     specs, and a **single** generic write-footprint / preservation predicate (`Preserves` /
     `Modifies`) **once** per project.
   - Never build 5–10 parallel `FooFrameM`/`FooFrameX` towers that re-walk the same C module for
     different projections. Prove **one** write-footprint theorem per C function and derive every
     frame corollary in a few lines.

3. **Stage 2 — Type-checked top-down skeleton + real-C hypothesis falsification**
   - For any multi-file state machine, write a thin top-down composition on a `skeleton/<id>-<topic>`
     branch (the **only** place `sorry` is allowed) so all leaf lemma signatures type-check
     end-to-end before parallel proof work begins.
   - **Falsify every non-trivial goal, loop invariant, or state invariant on real C before proving
     it in Lean.** Run a small C assertion harness compiled with ASan + UBSan
     (`-fsanitize=address,undefined,pointer-subtract,pointer-compare`,
     `ASAN_OPTIONS=detect_invalid_pointer_pair=2`) across boundary inputs:
     - `NULL` pointers with length `0`,
     - `0`, `1`, word-size, and `INT_MAX`/`UINT_MAX` sizes,
     - every mode/strategy/compression level (including degenerate/raw/stored/huffman/RLE modes),
     - truncated/corrupt headers, allocation failure injection, and multi-call sequences
       (including calls after error or end-of-stream states).

4. **Stage 3 — Bottom-up leaf proofs in topological call-graph order**
   - Prove callees before callers (pure helpers → read-only scanners → mutating helpers → loops →
     public entry points).
   - Decouple leaf safety from global invariants whenever possible: ask *"what is the weakest local
     condition that makes this helper memory-safe?"* instead of threading the full top-level state
     invariant into every leaf.

---

## 2. Lean 4.36 Proof Craft Recipes

### 2.1 Built-in `grind` + Compact `Wp` Calculus (`--wfail`-clean)

Prefer Lean 4's built-in `grind` over 50-line manual `UInt64.toNat_add` / `Nat.mod_eq_of_lt` chains,
and compose monadic steps through `Wp.bind'` instead of manual `M.bind` unfolding or copy-pasted CPS
continuations:

```lean
-- Bounded unsigned arithmetic and shifts in one kernel-checked step (no bv_decide):
theorem bound_no_wrap (src : UInt64) (h : src.toNat ≤ 1000000000) :
    (src + (src >>> 12) + (src >>> 14) + (src >>> 25) + 13).toNat =
      src.toNat + src.toNat / 4096 + src.toNat / 16384 + src.toNat / 33554432 + 13 := by
  grind

-- Compact compositional Wp judgement over M (Heap → Except Fault (α × Heap)):
abbrev ExampleM (S α : Type) := S → Except String (α × S)

def Wp {S α : Type} (m : ExampleM S α) (s : S) (Q : α → S → Prop) : Prop :=
  ∃ a s', m s = .ok (a, s') ∧ Q a s'

theorem Wp.bind' {S α β : Type} {m : ExampleM S α} {f : α → ExampleM S β} {s : S}
    {Q : β → S → Prop} (R : α → S → Prop)
    (hm : Wp m s R) (hf : ∀ a s', R a s' → Wp (f a) s' Q) :
    Wp (fun s => match m s with | .ok (a, s') => f a s' | .error e => .error e) s Q := by
  rcases hm with ⟨a, s', he, hr⟩
  rcases hf a s' hr with ⟨b, s'', he', hq⟩
  exact ⟨b, s'', by simp [he, he'], hq⟩
```

Prove `Wp` rules for every runtime primitive (`Ptr.add`, `Ptr.load`, `Ptr.store`, `memcpy`,
`memset`, checked signed arithmetic) and every internal callee once, so callers compose steps
cleanly with `Wp.bind'` and `Wp.cwhile_measure`.

### 2.2 Two-Tier Invariants & Facade Accessors

Never reuse a call-boundary invariant at internal mid-call checkpoints where boundary-only clauses
are temporarily false. Split every major state-machine invariant into two layers:

- **`CoreInv` (mid-call invariant):** structural/bounds facts that hold across *every* internal
  helper call (live allocations, array bounds, pointer provenance, disjointness).
- **`BoundaryInv` (API-boundary invariant):** `CoreInv` plus call-boundary-only clauses (e.g.
  flushed pending header, idle lookahead, reset cursor), lifted once at public API entry/exit.

Hide large invariant records behind small accessor and updater lemmas:
- External proof files must **not** pattern-match or construct raw `{ ... }` fields of a shared
  invariant structure. Adding a new clause then edits only the invariant's owning module rather than
  breaking dozens of proof files.
- **No cross-subsystem barrel imports under `Spec/Common/`.** Never create a single `Spec/Common.lean`
  that re-exports unrelated subsystem invariants (e.g. both encoder and decoder invariants); doing so
  forces full cross-subsystem rebuilds on every single invariant edit.

### 2.3 Translation-Preserving Phase Splitting (`rfl`) & Join Points

Never edit a C translation to make a proof easier. When a translated C function or loop body is too
large to prove in one lemma:

1. Define `private def phase1 ...`, `private def phase2 ...`, ..., `private def phaseK ...` in the
   **proof file** (not the translation file).
2. Prove `private theorem fn_eq_phases : Translated.fn ... = (do phase1; phase2; ...) := rfl`
   (or a one-line `simp` with `bind_assoc`).
3. Prove each phase in its own 50–150 line lemma and compose them with `Wp.bind'`.
4. When Lean's `do`-notation produces `__do_jp` join points that blow up under `simp`/`whnf`, use
   `extract_lets` (or prove the join point as a local `have` spec) to verify each join point once
   instead of inlining it across every branch.

### 2.4 Preventing WHNF, Heartbeat, and RAM Explosions

| Anti-pattern | What goes wrong | What to do instead |
| --- | --- | --- |
| `by decide +kernel` over concrete `C.run` executions in `Proof/` | Evaluates large heaps/arrays in Lean's unboxed kernel WHNF reducer; single 135-line files spike to 7–9 GB RAM | Prove general lemmas via `Wp`/`grind`, or check concrete witnesses via theorem application; keep heavy concrete checks in C/Lean differential tests |
| Blindly bumping `set_option maxHeartbeats` (e.g. 2M–40M) | Masks exponential WHNF unfolding of large structs or nested `if`/`do` blocks; ruins edit-compile latency | Target **0 `maxHeartbeats` overrides** in new projects; profile with `lake env lean -Dprofiler=true -Dprofiler.threshold=10` to find the exact unfolding constant or tactic, then split phases or mark heavy updaters `@[irreducible]` with projection lemmas |
| Recursive `def` in `Proof/` without `noncomputable` | Compiles `_unsafe_rec` and fails `PartialCheck` late in CI | Mark every recursive helper in `Proof/` as `noncomputable def` (or use `Prop`/inductive predicates) |
| Monolithic proof files (2,000–9,000+ LOC) | Every tactic edit forces multi-minute full-file re-elaboration and blocks parallel workers | Keep proof files to **400–800 LOC** (split by phase/helper once a file approaches 1,200–1,500 LOC) |
| Repeating 20–30 unbundled hypotheses on every theorem | Verbose signatures, slow type-checking, brittle edits | Bundle recurring context into a small `structure` (e.g. `SliceCtx`, `LoopCtx`) with concise projection lemmas |
| `omega` failing on `let`-bound locals or `UInt*` coercions | `omega` treats opaque `let` bindings and field projections as unrelated atoms | Use `grind`, or `generalize` / expose explicit `have` bounds before calling `omega` |
| Placeholder `:= True` goals in `Spec/Safety/` | Creates misleading progress counts and fake green registries | Leave untranslated/unproved entries in `notDone` of `Results.lean`; never register a `:= True` placeholder goal |

---

## 3. One-Round Stall Stop-Loss Protocol

Do **not** spend 10–30 edit cycles brute-forcing tactics on a stuck subgoal. If a proof makes no
structural progress for **one** edit-compile cycle (or hits two heartbeat/`omega` timeouts on the same
subgoal), **stop tactic hacking immediately** and triage in strict order:

1. **Suspect a false statement or real C bug first:** write a 20-line C test with ASan + UBSan
   against the real patched C library to try to falsify the subgoal or invariant. Many historical
   stalls were real upstream C bugs (`gz_fetch`, `deflate_slow`, `fill_window`, `brotli`
   `dist_rb_idx`, `libarchive` RAR5/7z) or false invariant clauses (`RollingHash` on `huff`/`rle`,
   `ResetKeepReady` at level 1).
2. **Audit the translation line by line against C:** confirm no statement, branch, cast, or
   side-effect was dropped or reordered.
3. **Check mid-call vs call-boundary invariant mismatch:** confirm you are not demanding a
   `BoundaryInv` clause inside an internal helper where only `CoreInv` holds.
4. **Profile and split:** run `lake env lean -Dprofiler=true` on the file, split the function into
   `rfl`-linked phases, and isolate join points with `extract_lets`.

If a single mathematical lemma remains genuinely hard after triage, isolate it cleanly on a
`skeleton/*` branch as one named hypothesis so downstream API-sequence proofs can proceed in
parallel while the mathematical core is solved separately.

---

## 4. Patch & Upstream-PR Discipline

- **Proof-driven only:** never dump a speculative multi-file patch bundle before proving.
- **One patch per bug:** each patch fixes exactly one confirmed bug or ISO C17 UB, with its own
  minimal revert-to-fail / apply-to-pass regression test under ASan + UBSan.
- **Public-API-only reproducers:** every patch reproducer must `#include` only documented public
  headers and invoke only documented public API functions. Never call private internal/static C
  symbols to justify a patch.
- **Cross-architecture hygiene before upstream submission:** check 32-bit / `-Wtype-limits` and
  `-Wall -Wextra` warnings on C patches destined for upstream.
- **Sanitize upstream PR descriptions:** never leak internal patch numbering (`00NN`), repository
  layout jargon, local paths, hostnames, or internal process notes into upstream PRs.

---

## 5. Resource, Git & Multi-Agent Discipline

### 5.1 Build & Memory Discipline

- Always bound local parallelism with `-j 4` (or `-j 1` on workstations running a local memory guard)
  and keep every Lean build under a **16 GB** memory cap.
- Run heavy builds **one at a time** per host; serialize concurrent local builds with a host-wide
  lockfile rather than letting multiple `lean` processes thrash RAM or get SIGTERMed.
- When build hosts are configured outside the repository, offload full builds there (with per-job
  memory limits in isolated scopes, never putting multiple live workers in one shared scope where a
  single OOM kills all peers) or let pull-request CI run the full build rather than stalling idle.
- **Never write scratch files, logs, or temporary build copies inside `.lake/` or `/tmp` (tmpfs).**
  Stale files in `.lake/` bloat disk caches and slow backups; stale files in Linux `/tmp` tmpfs
  consume RAM directly.

### 5.2 Git & Worktree Hygiene

- **Sync to `origin/main` first:** before auditing, branching, or estimating status, fetch and check
  latest `origin/main` so you never audit stale branches.
- **Stage by explicit path only:** never run `git add -A` or `git add .` (past incidents silently
  deleted sibling proof files from another session).
- **Never use `git stash` in multi-worktree setups:** the stash stack is shared across all worktrees
  and easily cross-contaminates parallel sessions.
- **Never force-push shared branches** and **never commit bot identities or `Co-Authored-By`
  trailers.** Verify `git config user.name` and `git config user.email` before committing.
- **Shared-definition changes require a full-package build:** never rely on a partial target build
  after editing `Runtime/`, `Spec/`, or a shared `*Inv.lean` file.

### 5.3 Multi-Agent Coordination

- Assign **disjoint files** to parallel workers from a pre-checked skeleton; never let two workers
  edit the same shared invariant or index file concurrently.
- Keep durable coordination notes outside ephemeral `/tmp` directories so session interruptions do
  not lose briefs or progress state.
- When verifying external runtime dependencies of a new target library (e.g. which codecs a wrapper
  actually links and invokes), inspect the real built package/symbols empirically rather than
  guessing from summaries.

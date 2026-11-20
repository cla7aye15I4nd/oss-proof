# `oss-proof` verification framework

`framework/` holds the project-independent checks, CI drivers, and proof engineering playbook shared
by every C library verified in `oss-proof`. All Python scripts require **Python 3.11+** (`tomllib`).

See [`PROOF_PLAYBOOK.md`](PROOF_PLAYBOOK.md) for the proof-authoring methodology, Lean 4.36
`Wp`/`grind` recipes, invariant layering, stall triage, and resource discipline.

## Key files

- `manifest.py`, `projects.json` — project manifest loader and registered project registry.
- `check_project.py` — full per-project verification gate (`options`, `forbidden`, `runtime_ub`,
  orphan module closure, `spec_layers`, string-literal table, `PartialCheck --results`,
  `ResultsCheck` fixtures, coverage, clean submodule & patches).
- `check_options.py`, `check_forbidden.py`, `check_runtime_ub.py`, `check_spec_layers.py`,
  `check_proof_hygiene.py` — static soundness, UB policy, layer, and proof-craft/blast-radius checkers.
- `build_guarded.py`, `remote_runner.sh`, `builders.example.toml` — three-tier build/gate/difftest
  dispatcher (capability-aware remote Linux pool configured outside git in
  `~/.config/oss-proof/builders.toml`, plus serialized local fallback and memory-guard diagnostics).
- `worktree_ops.py` — APFS/reflink CoW `.lake/build` hydration, selective single-project submodule
  init, and `.lake/` scratch-junk audit/GC.
- `preflight.py`, `install_hooks.py` — 2-second pre-PR check (static gates + hygiene + blast radius
  + CI matrix + privacy leak scan) and local `.githooks/` installer.
- `plan_proof.py`, `falsify_spec.py`, `profile_lean.py`, `scaffold_project.py` — C call-graph
  topological proof planner, real-C ASan+UBSan+strict-C17 falsifier, Lean heartbeat/WHNF profiler,
  and new-library scaffolder.
- `patches.py`, `ci_matrix.py`, `run_difftest.py` — patch series checker, path-scoped CI matrix,
  and ASan + UBSan differential test runner.
- `lean/OssProof/` — shared zero-dependency Lean 4 core (strict ISO C17 `Runtime`, `Wp`,
  `Preserves`/`Modifies`, and `c_arith`/`freeze` helpers), alongside `PartialCheck.lean`,
  `ResultsCheck.lean`, and `StrictPtr.lean`.
- `TEMPLATE_AGENTS.md`, `PROOF_PLAYBOOK.md` — per-project rules template and proof engineering guide.

## Adding a library under `projects/<id>/`

```bash
python3 framework/scaffold_project.py <id> --repo-url <upstream-git-url>
```

Then append `"<id>"` to `framework/projects.json`, hydrate the pinned submodule, and verify with
`python3 framework/preflight.py` and `python3 framework/build_guarded.py <id> --mode gate`.

## Running checks

```bash
# 2-second pre-PR check (static gates, hygiene, blast radius, CI impact, privacy scan)
python3 framework/preflight.py

# Resource-guarded build / gate (auto-routes to ~/.config/oss-proof/builders.toml or serialized local)
python3 framework/build_guarded.py --doctor
python3 framework/build_guarded.py zlib-ng --affected
python3 framework/build_guarded.py zlib-ng --mode gate

# Hydrate a fresh worktree (selective submodule + CoW .lake/build clone)
python3 framework/worktree_ops.py hydrate zlib-ng

# Proof authoring tools
python3 framework/plan_proof.py projects/bzip2/bzip2
python3 framework/falsify_spec.py --scaffold-harness /tmp/check.c
python3 framework/profile_lean.py framework/lean/OssProof/Wp.lean
python3 framework/check_proof_hygiene.py --show-hubs

# Framework unit tests
python3 -m unittest discover -s framework/tests -p "test_*.py"
```

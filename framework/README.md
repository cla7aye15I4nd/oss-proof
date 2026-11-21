# `oss-proof` verification framework

`framework/` holds the project-independent checks, CI drivers, and proof engineering playbook shared
by every C library verified in `oss-proof`. All Python scripts require **Python 3.11+** (`tomllib`).

See [`PROOF_PLAYBOOK.md`](PROOF_PLAYBOOK.md) for the proof-authoring methodology, Lean 4.36
`Wp`/`grind` recipes, invariant layering, stall triage, and resource discipline.

## Key files

- `manifest.py`, `projects.json` — project manifest loader and registered project registry.
- `check_project.py` — full per-project verification gate (`options`, `forbidden`, `runtime_ub`,
  `spec_layers`, string-literal table, `PartialCheck`, `ResultsCheck` fixtures, coverage, patches).
- `check_options.py`, `check_forbidden.py`, `check_runtime_ub.py`, `check_spec_layers.py` —
  individual static and policy checkers.
- `patches.py` — patch series discovery, application, and clean-submodule verification (supports
  both flat `patches/*.patch` and directory `patches/NNNN-slug/upstream.patch` layouts).
- `ci_matrix.py`, `run_difftest.py` — path-scoped CI matrix calculation and ASan + UBSan
  differential test runner.
- `lean/PartialCheck.lean`, `lean/ResultsCheck.lean`, `lean/StrictPtr.lean` — kernel environment
  auditor, `Results.lean` verifier, and strict ISO C17 pointer reference.
- `TEMPLATE_AGENTS.md`, `PROOF_PLAYBOOK.md` — per-project rules template and proof engineering guide.

## Adding a library under `projects/<id>/`

1. Pin the upstream C repository as a submodule at `projects/<id>/<upstream>` (read-only; patches live in `projects/<id>/patches/*.patch`, or, with `"patch_layout": "directories"` under `upstream` in `project.json`, one directory per patch `projects/<id>/patches/NNNN-slug/` holding `upstream.patch` and `pr-summary.md`; see `framework/patches.py`).
2. Copy root `lean-toolchain` to `projects/<id>/lean-toolchain` (and `projects/<id>/tests/lean-toolchain` when differential tests use a child Lake package).
3. Define `projects/<id>/lakefile.toml` with package `<Package>` and roots `["<Package>", "<Package>.Results"]`, using only the allow-listed Lake keys (`name`, `version`, `defaultTargets`, `lean_lib`).
4. Copy `framework/lean/ResultsCheck.lean` to check `<Package>/Results.lean` at build time (`proved`, `notDone`, `required`), and build the strict runtime from `framework/lean/StrictPtr.lean`.
5. Create `projects/<id>/project.json` (following an existing registered project) and append `"<id>"` to `framework/projects.json`.

## Running checks

```bash
# Source, option, lakefile, toolchain, layer, string-literal, and patch checks (no build needed)
python3 framework/check_project.py --source-only

# Bounded local build + verification gate for one project (cap LEAN_NUM_THREADS=4 under 16 GB RAM)
LEAN_NUM_THREADS=4 lake --dir projects/zlib build --wfail ZlibF ZlibF.Results
python3 framework/check_project.py zlib --skip-build

# ASan + UBSan differential tests for one project
python3 framework/run_difftest.py zlib-ng

# Framework unit tests
python3 -m unittest discover -s framework/tests -p "test_*.py"
```

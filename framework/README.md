# `oss-proof` verification framework

`framework/` holds the project-independent checks and CI drivers shared by every C library verified in `oss-proof`.

## Adding a library under `projects/<id>/`

1. Pin the upstream C repository as a submodule at `projects/<id>/<upstream>` (read-only; patches live in `projects/<id>/patches/*.patch`).
2. Copy root `lean-toolchain` to `projects/<id>/lean-toolchain` (and `projects/<id>/tests/lean-toolchain` when differential tests use a child Lake package).
3. Define `projects/<id>/lakefile.toml` with package `<Package>` and roots `["<Package>", "<Package>.Results"]`, using only the allow-listed Lake keys (`name`, `version`, `defaultTargets`, `lean_lib`).
4. Copy or import `framework/lean/ResultsCheck.lean` to check `<Package>/Results.lean` at build time (`proved`, `notDone`, `required`).
5. Create `projects/<id>/project.json` (following `projects/zlib/project.json`) and append `"<id>"` to `framework/projects.json`.

## Running checks

```bash
# Source, option, lakefile, toolchain, layer, string-literal, and patch checks (no build needed)
python3 framework/check_project.py --source-only

# Full verification gate for one project (builds with --wfail, audits kernel env, checks coverage & patches)
python3 framework/check_project.py zlib

# Framework unit tests
python3 -m unittest discover -s framework/tests -p "test_*.py"
```

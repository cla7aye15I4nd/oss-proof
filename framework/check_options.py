#!/usr/bin/env python3
"""No option and no build setting that weakens checking, across framework and projects.

Checks by allow-list:
1. Every `set_option` in `framework/lean/*.lean` and in each project's library (`<Package>.lean`,
   `<Package>/`) and CI-executed Lean files (`scripts/*.lean`, `tests/audit/`, `tests/lean/`,
   `tests/results-check/`) names an option in `ALLOWED_OPTIONS` or under `linter.` (with `«»` stripped).
2. Every project uses `lakefile.toml` with only `LAKEFILE_KEYS` (and `TESTS_LAKEFILE_KEYS` for optional
   `tests/lakefile.toml`), has no `lakefile.lean`, requires only its own `<Package>` by path `..` in
   `tests/lakefile.toml`, and keeps `lean-toolchain` identical to the repository root `lean-toolchain`.
"""
from __future__ import annotations

import argparse
import re
import sys
import tomllib
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from framework.manifest import REPO, load_all_projects, load_project

ALLOWED_OPTIONS = {"autoImplicit", "maxHeartbeats", "maxRecDepth", "hygiene"}
ALLOWED_PREFIXES = ("linter.",)

LAKEFILE_KEYS = {"": {"name", "version", "defaultTargets", "lean_lib"}, "lean_lib": {"name", "roots"}}
TESTS_LAKEFILE_KEYS = {
    "": {"name", "version", "require", "lean_lib", "lean_exe"},
    "require": {"name", "path"},
    "lean_lib": {"name", "srcDir"},
    "lean_exe": {"name", "root", "srcDir"},
}

SET_OPTION = re.compile(r"\bset_option\s+(\S+)")


def scan_lean_options(files: list[Path], base: Path) -> list[str]:
    errors: list[str] = []
    for f in files:
        if not f.is_file():
            continue
        for number, line in enumerate(f.read_text().splitlines(), 1):
            for match in SET_OPTION.finditer(line):
                name = match.group(1).replace("«", "").replace("»", "")
                if name not in ALLOWED_OPTIONS and not name.startswith(ALLOWED_PREFIXES):
                    errors.append(f"{f.relative_to(base)}:{number}: option {name} is not allowed")
    return errors


def table_errors(label: str, data: dict, allowed: dict) -> list[str]:
    errors = [f"{label}: key {k} is not allowed" for k in data if k not in allowed[""]]
    for table, keys in allowed.items():
        if not table:
            continue
        entries = data.get(table, [])
        for entry in entries if isinstance(entries, list) else [entries]:
            if not isinstance(entry, dict):
                errors.append(f"{label}: {table} is not a table")
                continue
            errors += [f"{label}: [[{table}]] key {k} is not allowed" for k in entry if k not in keys]
    return errors


def project_lean_files(project_root: Path, package: str) -> list[Path]:
    files = [project_root / f"{package}.lean"]
    pkg_dir = project_root / package
    if pkg_dir.is_dir():
        files += sorted(pkg_dir.rglob("*.lean"))
    scripts_dir = project_root / "scripts"
    if scripts_dir.is_dir():
        files += sorted(scripts_dir.glob("*.lean"))
    for sub in ("tests/audit", "tests/lean", "tests/results-check"):
        sub_dir = project_root / sub
        if sub_dir.is_dir():
            files += sorted(sub_dir.rglob("*.lean"))
    return [f for f in files if f.is_file()]


def check_project_options(project_root: Path, package: str, root_toolchain: str | None = None, base: Path | None = None) -> list[str]:
    base = base or project_root
    errors = scan_lean_options(project_lean_files(project_root, package), base)
    for lean_config in (project_root / "lakefile.lean", project_root / "tests/lakefile.lean"):
        if lean_config.exists():
            errors.append(f"{lean_config.relative_to(base)}: a Lean Lake configuration is not allowed")
    main_lake = project_root / "lakefile.toml"
    if not main_lake.is_file():
        errors.append(f"{main_lake.relative_to(base)}: missing lakefile.toml")
    else:
        data = tomllib.loads(main_lake.read_text())
        errors += table_errors(str(main_lake.relative_to(base)), data, LAKEFILE_KEYS)
    tests_lake = project_root / "tests/lakefile.toml"
    if tests_lake.is_file():
        data = tomllib.loads(tests_lake.read_text())
        label = str(tests_lake.relative_to(base))
        errors += table_errors(label, data, TESTS_LAKEFILE_KEYS)
        if data.get("require", []) != [{"name": package, "path": ".."}]:
            errors.append(f"{label}: the test project may require only {package}, by path ..")
    if root_toolchain is not None:
        for tc in (project_root / "lean-toolchain", project_root / "tests/lean-toolchain"):
            if tc.is_file() and tc.read_text() != root_toolchain:
                errors.append(f"{tc.relative_to(base)}: toolchain differs from root lean-toolchain")
        if not (project_root / "lean-toolchain").is_file():
            errors.append(f"{(project_root / 'lean-toolchain').relative_to(base)}: missing lean-toolchain")
    return errors


def check_repo(repo: Path = REPO, project_ids: list[str] | None = None) -> list[str]:
    errors: list[str] = []
    if (repo / "lakefile.lean").exists() or (repo / "lakefile.toml").exists():
        errors.append("root lakefile is not allowed; each verified library is an isolated package under projects/<id>/")
    tc_path = repo / "lean-toolchain"
    if not tc_path.is_file():
        errors.append("lean-toolchain: missing root toolchain file")
        root_toolchain = None
    else:
        root_toolchain = tc_path.read_text()
    fw_lean = sorted((repo / "framework/lean").rglob("*.lean")) if (repo / "framework/lean").is_dir() else []
    errors += scan_lean_options(fw_lean, repo)
    projects = [load_project(pid, repo) for pid in project_ids] if project_ids else load_all_projects(repo)
    for proj in projects:
        errors += check_project_options(proj.root, proj.package, root_toolchain=root_toolchain, base=repo)
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("projects", nargs="*", help="Optional project IDs to check (default: all registered)")
    args = parser.parse_args()
    errors = check_repo(REPO, args.projects or None)
    for err in errors:
        print(err)
    if errors:
        print("option, toolchain, or build setting that may weaken checking found")
        return 1
    print("options, lakefiles, and toolchains passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())

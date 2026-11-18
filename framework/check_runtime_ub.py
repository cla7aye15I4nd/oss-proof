#!/usr/bin/env python3
"""Enforce strict ISO C17 undefined-behaviour rules in `<Package>/Runtime/` across projects.

Rejects known permissive runtime shortcuts that ISO C17 leaves undefined:
1. `Ptr.add` bypassing null/liveness/bounds checks when `k = 0` (which silently permits `NULL + 0`
   and wild/dangling pointer `+ 0`, violating ISO C17 §6.5.6p8).
2. `Ptr.diff` returning `0` on `NULL - NULL` (`| .null, .null => .ok`, violating ISO C17 §6.5.6p9).
3. `Ptr.memcpy` / `Ptr.memmove` / `Ptr.memset` / `Ptr.fill` bypassing null/dangling checks when `n = 0`
   (violating ISO C17 §7.24.1p2).

`LEGACY_PERMISSIVE_PTR_PROJECTS` is a shrink-only debt list: `zlib` currently retains items (1) and (2)
from before the strict rule was codified; no new project may enter this list, and once `zlib` removes
them its entry must be deleted here.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from framework.manifest import Project, REPO, load_all_projects, load_project

# Shrink-only legacy debt list. Never add a project ID here.
LEGACY_PERMISSIVE_PTR_PROJECTS: frozenset[str] = frozenset({"zlib"})

ADD_ZERO_SHORTCUT = re.compile(r"\bif\s+k\s*==?\s*0\s+then\s+\.ok\b")
DIFF_NULL_NULL_SHORTCUT = re.compile(r"\|\s*\.null\s*,\s*\.null\s*=>\s*\.ok\b")
MEM_ZERO_LEN_SHORTCUT = re.compile(
    r"def\s+Ptr\.(?:memcpy|memmove|fill|memset)\b[\s\S]{0,300}?\bif\s+n\s*==?\s*0\s+then\s+\.ok\b"
)


def check_project_runtime_ub(proj: Project, base: Path = REPO) -> list[str]:
    errors: list[str] = []
    runtime_dir = proj.root / proj.package / "Runtime"
    if not runtime_dir.is_dir():
        return errors

    ptr_file = runtime_dir / "Ptr.lean"
    found_legacy = False
    if ptr_file.is_file():
        text = ptr_file.read_text()
        rel = ptr_file.relative_to(base)
        has_add_zero = bool(ADD_ZERO_SHORTCUT.search(text))
        has_diff_null = bool(DIFF_NULL_NULL_SHORTCUT.search(text))
        if has_add_zero or has_diff_null:
            found_legacy = True
            if proj.id not in LEGACY_PERMISSIVE_PTR_PROJECTS:
                if has_add_zero:
                    errors.append(
                        f"{rel}: Ptr.add permits `p + 0` without checking liveness/non-null "
                        "(NULL + 0 and wild/dangling pointer + 0 are UB in ISO C17 §6.5.6p8; see AGENTS.md)"
                    )
                if has_diff_null:
                    errors.append(
                        f"{rel}: Ptr.diff permits `NULL - NULL` "
                        "(undefined in ISO C17 §6.5.6p9; see AGENTS.md)"
                    )
        if proj.id in LEGACY_PERMISSIVE_PTR_PROJECTS and not found_legacy:
            errors.append(
                f"{proj.id} no longer has permissive Ptr shortcuts: remove '{proj.id}' from "
                "LEGACY_PERMISSIVE_PTR_PROJECTS in framework/check_runtime_ub.py"
            )

    libc_file = runtime_dir / "Libc.lean"
    if libc_file.is_file():
        text = libc_file.read_text()
        rel = libc_file.relative_to(base)
        if MEM_ZERO_LEN_SHORTCUT.search(text):
            errors.append(
                f"{rel}: memcpy/memmove/memset/fill bypasses null/liveness check when n = 0 "
                "(undefined in ISO C17 §7.24.1p2; see AGENTS.md)"
            )
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("projects", nargs="*", help="Optional project IDs (default: all registered)")
    args = parser.parse_args()
    projects = [load_project(pid, REPO) for pid in args.projects] if args.projects else load_all_projects(REPO)
    errors: list[str] = []
    for proj in projects:
        errors += check_project_runtime_ub(proj, base=REPO)
    for err in errors:
        print(err)
    if errors:
        print("runtime UB policy check failed")
        return 1
    print("runtime UB policy check passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Scan Lean sources for forbidden constructs (`native_decide`, `bv_decide`, `axiom`, `partial`, `unsafe`, `opaque`, `implemented_by`, `extern`)."""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from framework.manifest import REPO, load_all_projects, load_project

FORBIDDEN = re.compile(
    r"\b(native_decide|bv_decide|implemented_by)\b"
    r"|^\s*(@\[[^]]*\]\s*)?((private|protected|noncomputable|local|scoped)\s+)*axiom\b"
    r"|^\s*(@\[[^]]*\]\s*)?(private\s+|protected\s+|noncomputable\s+)*"
    r"((partial|unsafe)\s+(def|instance|theorem|abbrev|structure|inductive)\b"
    r"|opaque\s+[A-Za-z_.]+\s*[:(\[{])"
    r"|@\[[^]]*\bextern\b"
)


def scan_files(files: list[Path], base: Path) -> list[str]:
    hits: list[str] = []
    for path in files:
        if not path.is_file():
            continue
        for lineno, line in enumerate(path.read_text().splitlines(), 1):
            if FORBIDDEN.search(line):
                hits.append(f"{path.relative_to(base)}:{lineno}:{line}")
    return hits


def check_project_forbidden(project_root: Path, package: str, base: Path | None = None) -> list[str]:
    base = base or project_root
    files = [project_root / f"{package}.lean"]
    pkg_dir = project_root / package
    if pkg_dir.is_dir():
        files += sorted(pkg_dir.rglob("*.lean"))
    return scan_files(files, base)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("projects", nargs="*", help="Optional project IDs to scan (default: all registered)")
    args = parser.parse_args()
    projects = [load_project(pid, REPO) for pid in args.projects] if args.projects else load_all_projects(REPO)
    hits: list[str] = []
    for proj in projects:
        hits += check_project_forbidden(proj.root, proj.package, base=REPO)
    for hit in hits:
        print(hit)
    if hits:
        print("forbidden construct found")
        return 1
    print("no forbidden constructs found")
    return 0


if __name__ == "__main__":
    sys.exit(main())

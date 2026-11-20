#!/usr/bin/env python3
"""Scan Lean sources for forbidden constructs (`sorry`, `admit`, `native_decide`, `bv_decide`, `axiom`, `partial`, `unsafe`, `opaque`, `implemented_by`, `extern`)."""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from framework._py import ensure_python311

ensure_python311()
from framework.manifest import REPO, load_all_projects, load_project

FORBIDDEN_LINE = re.compile(
    r"\b(native_decide|bv_decide|implemented_by)\b"
    r"|^\s*(@\[[^]]*\]\s*)?((private|protected|noncomputable|local|scoped)\s+)*axiom\b"
    r"|^\s*(@\[[^]]*\]\s*)?(private\s+|protected\s+|noncomputable\s+)*"
    r"((partial|unsafe)\s+(def|instance|theorem|abbrev|structure|inductive)\b"
    r"|opaque\s+[A-Za-z_.]+\s*[:(\[{])"
    r"|@\[[^]]*\bextern\b"
)

FORBIDDEN_MULTILINE = re.compile(
    r"(?:^|\n)\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|local|scoped)\s+)*"
    r"(?:(partial|unsafe)\s+(def|instance|theorem|abbrev|structure|inductive)\b|axiom\b)",
    re.S,
)

SORRY_RE = re.compile(r"\b(sorry|admit)\b")


def strip_comments_and_strings(text: str) -> str:
    """Replace Lean comments (`-- ...`, `/- ... -/`) and string literals with spaces, preserving newlines."""
    out: list[str] = []
    i, n = 0, len(text)
    depth = 0
    in_str = False
    while i < n:
        ch = text[i]
        if depth > 0:
            if text[i : i + 2] == "/-":
                depth += 1
                i += 2
            elif text[i : i + 2] == "-/":
                depth -= 1
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
        elif in_str:
            if ch == "\\" and i + 1 < n:
                out.append("  ")
                i += 2
            elif ch == '"':
                in_str = False
                out.append('"')
                i += 1
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
        else:
            if text[i : i + 2] == "--":
                while i < n and text[i] != "\n":
                    i += 1
            elif text[i : i + 2] == "/-":
                depth = 1
                i += 2
            elif ch == '"':
                in_str = True
                out.append('"')
                i += 1
            else:
                out.append(ch)
                i += 1
    return "".join(out)


def scan_files(files: list[Path], base: Path, *, allow_sorry: bool = False) -> list[str]:
    hits: list[str] = []
    for path in files:
        if not path.is_file():
            continue
        raw = path.read_text()
        clean = strip_comments_and_strings(raw)
        raw_lines = raw.splitlines()
        clean_lines = clean.splitlines()
        seen_lines: set[int] = set()
        for lineno, line in enumerate(clean_lines, 1):
            if FORBIDDEN_LINE.search(line) or (not allow_sorry and SORRY_RE.search(line)):
                seen_lines.add(lineno)
                src_line = raw_lines[lineno - 1] if lineno - 1 < len(raw_lines) else line
                hits.append(f"{path.relative_to(base)}:{lineno}:{src_line}")
        for match in FORBIDDEN_MULTILINE.finditer(clean):
            lineno = clean[: match.start()].count("\n") + 1
            if match.group(0).startswith("\n"):
                lineno += 1
            if lineno not in seen_lines:
                seen_lines.add(lineno)
                src_line = raw_lines[lineno - 1] if lineno - 1 < len(raw_lines) else ""
                hits.append(f"{path.relative_to(base)}:{lineno}:{src_line}")
    return hits


def check_project_forbidden(
    project_root: Path,
    package: str,
    base: Path | None = None,
    *,
    allow_sorry: bool = False,
) -> list[str]:
    base = base or project_root
    files = [project_root / f"{package}.lean"]
    pkg_dir = project_root / package
    if pkg_dir.is_dir():
        files += sorted(pkg_dir.rglob("*.lean"))
    return scan_files(files, base, allow_sorry=allow_sorry)


def check_shared_core_forbidden(repo: Path = REPO, *, allow_sorry: bool = False) -> list[str]:
    core_dir = repo / "framework/lean/OssProof"
    if not core_dir.is_dir():
        return []
    files = [repo / "framework/lean/OssProof.lean", *sorted(core_dir.rglob("*.lean"))]
    return scan_files(files, repo, allow_sorry=allow_sorry)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("projects", nargs="*", help="Optional project IDs to scan (default: all registered)")
    parser.add_argument(
        "--allow-sorry",
        action="store_true",
        help="Allow `sorry`/`admit` (for `skeleton/*` branches only)",
    )
    args = parser.parse_args()
    projects = [load_project(pid, REPO) for pid in args.projects] if args.projects else load_all_projects(REPO)
    hits = check_shared_core_forbidden(REPO, allow_sorry=args.allow_sorry)
    for proj in projects:
        hits += check_project_forbidden(proj.root, proj.package, base=REPO, allow_sorry=args.allow_sorry)
    for hit in hits:
        print(hit)
    if hits:
        print("forbidden construct found")
        return 1
    print("no forbidden constructs found")
    return 0


if __name__ == "__main__":
    sys.exit(main())

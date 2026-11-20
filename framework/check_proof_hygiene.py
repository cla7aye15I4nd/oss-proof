#!/usr/bin/env python3
"""Static proof-craft, blast-radius, and hygiene auditor for oss-proof projects.

Checks in <1 second without running Lean:
1. Executable recursive `def` in `*/Proof/*.lean` (catches `_unsafe_rec` before `PartialCheck`).
2. `decide +kernel` in `*/Proof/*.lean` (major single-module RAM spike hazard).
3. `set_option maxHeartbeats` overrides (new projects target 0 overrides).
4. Placeholder `:= True` / `:= False` goals in `*/Spec/Safety/*.lean`.
5. Monolithic proof files (> `max_loc`, default 1500 LOC).
6. Import-graph blast radius (top transitive hubs, changed-file impact, and orphan modules).
"""
from __future__ import annotations

import argparse
import re
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from framework._py import ensure_python311

ensure_python311()
from framework import check_spec_layers
from framework.check_forbidden import strip_comments_and_strings
from framework.manifest import Project, REPO, load_all_projects, load_project

DECIDE_KERNEL_RE = re.compile(r"\bdecide\s*\+kernel\b")
HEARTBEAT_RE = re.compile(r"\bset_option\s+maxHeartbeats\s+(\d+)")
PLACEHOLDER_GOAL_RE = re.compile(r"\b(?:def|abbrev)\s+(?:[A-Za-z0-9_'.]*\.)?Goal\.[A-Za-z0-9_']+\b[^:=\n]*:\s*Prop\s*:=\s*(?:True|False)\b")
DEF_HEADER_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(private|protected|local|scoped|noncomputable|meta)\s+)*def\s+([A-Za-z_][A-Za-z0-9_']*)\b"
)


def build_import_graph(proj: Project) -> tuple[dict[str, list[str]], dict[str, set[str]], dict[str, Path]]:
    pkg = proj.package
    pkg_dir = proj.root / pkg
    mod_to_path: dict[str, Path] = {}
    if (proj.root / f"{pkg}.lean").is_file():
        mod_to_path[pkg] = proj.root / f"{pkg}.lean"
    if pkg_dir.is_dir():
        for p in sorted(pkg_dir.rglob("*.lean")):
            parts = list(p.relative_to(proj.root).parts)
            mod = check_spec_layers.canonical(parts[:-1] + [parts[-1][: -len(".lean")]])
            mod_to_path[mod] = p

    imports: dict[str, list[str]] = {}
    rev: dict[str, set[str]] = defaultdict(set)
    for mod, path in mod_to_path.items():
        imps: list[str] = []
        for raw in check_spec_layers.header_imports(path.read_text()):
            canon = check_spec_layers.canonical(check_spec_layers.components(raw))
            if canon in mod_to_path:
                imps.append(canon)
                rev[canon].add(mod)
        imports[mod] = imps
    return imports, rev, mod_to_path


def transitive_dependents(mod: str, rev: dict[str, set[str]]) -> set[str]:
    seen: set[str] = set()
    stack = list(rev.get(mod, ()))
    while stack:
        cur = stack.pop()
        if cur in seen:
            continue
        seen.add(cur)
        stack.extend(rev.get(cur, ()))
    return seen


def find_executable_recursive_proof_defs(path: Path) -> list[tuple[int, str]]:
    """Heuristic static detector for executable recursive `def`s in `Proof/` missing `noncomputable`."""
    clean = strip_comments_and_strings(path.read_text())
    lines = clean.splitlines()
    hits: list[tuple[int, str]] = []
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        m = DEF_HEADER_RE.match(line)
        if not m:
            i += 1
            continue
        is_noncomp = "noncomputable" in line[: m.start(2)] or "meta" in line[: m.start(2)]
        name = m.group(2)
        start_ln = i + 1
        body_lines = [line[m.end(2) :]]
        i += 1
        while i < n:
            nxt = lines[i]
            if nxt and not nxt[0].isspace() and not nxt.startswith("|") and not nxt.startswith("where"):
                break
            body_lines.append(nxt)
            i += 1
        if is_noncomp:
            continue
        body = "\n".join(body_lines)
        if re.search(rf"\b{re.escape(name)}\b", body):
            hits.append((start_ln, name))
    return hits


def analyze_project(
    proj: Project,
    *,
    max_loc: int = 1500,
    changed_paths: list[str] | None = None,
) -> dict:
    pkg = proj.package
    imports, rev, mod_to_path = build_import_graph(proj)
    proof_dir = proj.root / pkg / "Proof"
    safety_dir = proj.root / pkg / "Spec" / "Safety"

    rec_defs: list[str] = []
    decide_kernels: list[str] = []
    heartbeats: list[tuple[str, int, int]] = []
    monoliths: list[tuple[str, int]] = []
    placeholder_goals: list[str] = []

    if proof_dir.is_dir():
        for p in sorted(proof_dir.rglob("*.lean")):
            rel = str(p.relative_to(REPO)) if p.is_relative_to(REPO) else str(p.relative_to(proj.root))
            raw = p.read_text()
            loc = len(raw.splitlines())
            if loc > max_loc:
                monoliths.append((rel, loc))
            clean = strip_comments_and_strings(raw)
            for ln, line in enumerate(clean.splitlines(), 1):
                if DECIDE_KERNEL_RE.search(line):
                    decide_kernels.append(f"{rel}:{ln}")
                hm = HEARTBEAT_RE.search(line)
                if hm:
                    heartbeats.append((f"{rel}:{ln}", int(hm.group(1)), loc))
            for ln, name in find_executable_recursive_proof_defs(p):
                rec_defs.append(f"{rel}:{ln}: def {name} (consider `noncomputable def` to avoid _unsafe_rec)")

    if safety_dir.is_dir():
        for p in sorted(safety_dir.rglob("*.lean")):
            rel = str(p.relative_to(REPO)) if p.is_relative_to(REPO) else str(p.relative_to(proj.root))
            clean = strip_comments_and_strings(p.read_text())
            for ln, line in enumerate(clean.splitlines(), 1):
                if PLACEHOLDER_GOAL_RE.search(line):
                    placeholder_goals.append(f"{rel}:{ln}: {line.strip()}")

    # Orphan detection
    roots = [r for r in (pkg, proj.results_module) if r in mod_to_path]
    reachable = set(roots)
    stack = list(roots)
    while stack:
        cur = stack.pop()
        for child in imports.get(cur, ()):
            if child not in reachable:
                reachable.add(child)
                stack.append(child)
    orphans = sorted(set(mod_to_path) - reachable)

    # Top blast-radius hubs
    hubs = sorted(
        ((mod, len(transitive_dependents(mod, rev))) for mod in mod_to_path),
        key=lambda x: x[1],
        reverse=True,
    )[:10]

    # Changed-file blast radius
    changed_blast: list[tuple[str, int]] = []
    if changed_paths:
        path_to_mod = {p.resolve(): m for m, p in mod_to_path.items()}
        for cp in changed_paths:
            full = (REPO / cp).resolve()
            if full in path_to_mod:
                mod = path_to_mod[full]
                changed_blast.append((mod, len(transitive_dependents(mod, rev))))

    return {
        "project": proj.id,
        "modules": len(mod_to_path),
        "orphans": orphans,
        "rec_defs": rec_defs,
        "decide_kernels": decide_kernels,
        "heartbeats": heartbeats,
        "monoliths": sorted(monoliths, key=lambda x: x[1], reverse=True),
        "placeholder_goals": placeholder_goals,
        "top_hubs": hubs,
        "changed_blast": sorted(changed_blast, key=lambda x: x[1], reverse=True),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("projects", nargs="*", help="Project IDs (default: all registered)")
    parser.add_argument("--max-loc", type=int, default=1500, help="Warn on proof files exceeding this LOC")
    parser.add_argument("--strict", action="store_true", help="Exit non-zero on hygiene warnings")
    parser.add_argument("--show-hubs", action="store_true", help="Print top-10 transitive blast-radius hubs")
    args = parser.parse_args()

    projects = [load_project(pid, REPO) for pid in args.projects] if args.projects else load_all_projects(REPO)
    any_warn = False
    for proj in projects:
        rep = analyze_project(proj, max_loc=args.max_loc)
        print(
            f"[{proj.id}] modules={rep['modules']} orphans={len(rep['orphans'])} "
            f"rec_proof_defs={len(rep['rec_defs'])} decide_kernel={len(rep['decide_kernels'])} "
            f"maxHeartbeats={len(rep['heartbeats'])} monoliths(>{args.max_loc}L)={len(rep['monoliths'])} "
            f"placeholder_goals={len(rep['placeholder_goals'])}"
        )
        for label, items in (
            ("orphan", rep["orphans"]),
            ("placeholder goal", rep["placeholder_goals"]),
            ("recursive proof def", rep["rec_defs"]),
            ("decide +kernel", rep["decide_kernels"]),
        ):
            for item in items[:10]:
                print(f"  WARN [{label}]: {item}")
            if len(items) > 10:
                print(f"  ... and {len(items) - 10} more {label}(s)")
        for path, loc in rep["monoliths"][:5]:
            print(f"  WARN [monolith]: {path} ({loc} LOC)")
        if args.show_hubs and rep["top_hubs"]:
            print("  Top blast-radius hubs:")
            for mod, cnt in rep["top_hubs"][:8]:
                print(f"    {cnt:5d} deps <- {mod}")
        if (
            rep["orphans"]
            or rep["placeholder_goals"]
            or rep["rec_defs"]
            or rep["decide_kernels"]
            or rep["heartbeats"]
            or rep["monoliths"]
        ):
            any_warn = True
    return 1 if (args.strict and any_warn) else 0


if __name__ == "__main__":
    sys.exit(main())

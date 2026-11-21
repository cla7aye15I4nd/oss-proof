#!/usr/bin/env python3
"""Fast (~2 second) pre-PR local preflight check for oss-proof.

Runs without invoking Lean:
1. Computes exact CI matrix impact (`framework/ci_matrix.py`) for changed files vs base ref.
2. Runs `check_options`, `check_forbidden`, `check_runtime_ub`, `check_spec_layers`, and
   `ResultsCheck.lean` sync verification.
3. Runs `check_proof_hygiene` on affected projects, reporting blast radius of modified `.lean` files.
4. Checks `docs/en/` vs `docs/zh/` file-path parity on touched project docs.
5. Scans added diff lines for privacy/hygiene leaks (private Tailscale/RFC1918 IPs, absolute home
   paths, bot identities, `Co-Authored-By` trailers).
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from framework._py import ensure_python311

ensure_python311()
from framework import (
    check_forbidden,
    check_options,
    check_proof_hygiene,
    check_runtime_ub,
    check_spec_layers,
    ci_matrix,
    scaffold_project,
)
from framework.manifest import REPO, load_all_projects

# Patterns forbidden in committed repository files (AGENTS.md privacy/attribution policy).
LEAK_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("private IPv4 (100.x / 10.x / 192.168.x)", re.compile(r"\b(?:100\.(?:6[4-9]|[7-9]\d|1[01]\d|12[0-7])|192\.168)\.\d{1,3}\.\d{1,3}\b")),
    ("absolute macOS/Linux home path", re.compile(r"(?:/Users/|/home/)[A-Za-z0-9._-]+/")),
    ("bot author marker", re.compile(r"\[bot\]")),
    ("Co-Authored-By trailer", re.compile(r"^\s*Co-Authored-By:", re.I)),
)


def scan_added_diff_leaks(diff_text: str, *, skip_files: set[str] | None = None) -> list[str]:
    skip = skip_files or set()
    hits: list[str] = []
    cur_file = "<diff>"
    for line in diff_text.splitlines():
        if line.startswith("+++ b/"):
            cur_file = line[6:]
            continue
        if not line.startswith("+") or line.startswith("+++"):
            continue
        if cur_file in skip:
            continue
        content = line[1:]
        for label, pat in LEAK_PATTERNS:
            m = pat.search(content)
            if m:
                hits.append(f"{cur_file}: possible {label} ({m.group(0)!r})")
    return hits


def check_bilingual_doc_parity(project_ids: list[str]) -> list[str]:
    errors: list[str] = []
    for pid in project_ids:
        docs_root = REPO / "projects" / pid / "docs"
        en_dir, zh_dir = docs_root / "en", docs_root / "zh"
        if not (en_dir.is_dir() and zh_dir.is_dir()):
            continue
        en_files = {str(p.relative_to(en_dir)) for p in en_dir.rglob("*.md")}
        zh_files = {str(p.relative_to(zh_dir)) for p in zh_dir.rglob("*.md")}
        for missing in sorted(en_files - zh_files):
            errors.append(f"[{pid}] docs/zh/{missing} is missing (present in docs/en/)")
        for missing in sorted(zh_files - en_files):
            errors.append(f"[{pid}] docs/en/{missing} is missing (present in docs/zh/)")
    return errors


def git_changed_and_diff(base: str) -> tuple[list[str], str]:
    status_out = subprocess.check_output(["git", "status", "--porcelain"], cwd=REPO, text=True)
    dirty = [line[3:].strip().split(" -> ")[-1] for line in status_out.splitlines() if line.strip()]
    changed = list(dirty)
    diff_chunks: list[str] = []
    if ci_matrix.commit_exists(REPO, base):
        branch_changed = ci_matrix.changed_files(REPO, base)
        changed = sorted(set(changed + branch_changed))
        diff_chunks.append(subprocess.check_output(["git", "diff", base], cwd=REPO, text=True))
    else:
        diff_chunks.append(subprocess.check_output(["git", "diff"], cwd=REPO, text=True))
    return changed, "\n".join(diff_chunks)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", default="origin/main", help="Base git ref for diff/matrix (default: origin/main)")
    parser.add_argument("--allow-sorry", action="store_true", help="Allow sorry/admit (skeleton/* branches only)")
    parser.add_argument("--strict-hygiene", action="store_true", help="Fail on proof hygiene warnings")
    args = parser.parse_args()

    changed, diff_text = git_changed_and_diff(args.base)
    projects = load_all_projects(REPO)
    build_ids, difftest_ids = ci_matrix.compute_matrices(projects, "pull_request", changed)

    print(f"==> Preflight ({len(changed)} changed file(s) vs {args.base})")
    print(f"    CI build matrix    : {build_ids}")
    print(f"    CI difftest matrix : {difftest_ids}")

    failed = False

    opt_errs = check_options.check_repo(REPO)
    if opt_errs:
        failed = True
        for e in opt_errs:
            print("FAIL [options]:", e, file=sys.stderr)
    else:
        print("OK   [options] lakefiles, toolchains, and set_option allow-list")

    forb_hits = check_forbidden.check_shared_core_forbidden(REPO, allow_sorry=args.allow_sorry)
    for proj in projects:
        forb_hits += check_forbidden.check_project_forbidden(
            proj.root, proj.package, base=REPO, allow_sorry=args.allow_sorry
        )
    if forb_hits:
        failed = True
        for h in forb_hits[:20]:
            print("FAIL [forbidden]:", h, file=sys.stderr)
    else:
        print("OK   [forbidden] no forbidden constructs")

    ub_errs = check_runtime_ub.check_runtime_dir_ub(REPO / "framework/lean/OssProof/Runtime", "OssProof", base=REPO)
    for proj in projects:
        ub_errs += check_runtime_ub.check_project_runtime_ub(proj, base=REPO)
    if ub_errs:
        failed = True
        for e in ub_errs:
            print("FAIL [runtime_ub]:", e, file=sys.stderr)
    else:
        print("OK   [runtime_ub] strict ISO C17 runtime policy")

    rc_errs = scaffold_project.check_results_check_sync()
    if rc_errs:
        failed = True
        for e in rc_errs:
            print("FAIL [results_check]:", e, file=sys.stderr)
    else:
        print("OK   [results_check] ResultsCheck.lean core invariants present in all projects")

    layer_fail = False
    for proj in projects:
        spec_cfg = proj.data.get("checks", {}).get("spec_layers")
        if not spec_cfg:
            continue
        allow = check_spec_layers.load_math_allowlist(proj.root, spec_cfg)
        errs, _, _ = check_spec_layers.SpecLayerChecker(proj.root, proj.package, allow).run()
        if errs:
            layer_fail = True
            failed = True
            for e in errs:
                print(f"FAIL [spec_layers:{proj.id}]:", e, file=sys.stderr)
    if not layer_fail:
        print("OK   [spec_layers] all registered projects")

    # Proof hygiene & blast radius on affected projects
    touched_pids = sorted(
        {
            p.id
            for p in projects
            if any(c.startswith(f"projects/{p.id}/") for c in changed)
        }
    )
    for proj in [p for p in projects if p.id in touched_pids]:
        rep = check_proof_hygiene.analyze_project(proj, changed_paths=changed)
        print(
            f"INFO [hygiene:{proj.id}] orphans={len(rep['orphans'])} rec_defs={len(rep['rec_defs'])} "
            f"decide_kernel={len(rep['decide_kernels'])} maxHeartbeats={len(rep['heartbeats'])} "
            f"monoliths={len(rep['monoliths'])}"
        )
        for mod, deps in rep["changed_blast"][:5]:
            warn = " [HIGH BLAST RADIUS]" if deps >= 50 else ""
            print(f"    blast radius: {mod} -> {deps} transitive dependent(s){warn}")
        if args.strict_hygiene and (rep["orphans"] or rep["placeholder_goals"]):
            failed = True

    doc_errs = check_bilingual_doc_parity(touched_pids)
    if doc_errs:
        failed = True
        for e in doc_errs:
            print("FAIL [docs-parity]:", e, file=sys.stderr)
    else:
        print("OK   [docs-parity] en/zh mirrored")

    leak_hits = scan_added_diff_leaks(
        diff_text,
        skip_files={
            "framework/preflight.py",
            "framework/install_hooks.py",
            "framework/tests/test_framework.py",
        },
    )
    if leak_hits:
        failed = True
        for h in leak_hits:
            print("FAIL [privacy/hygiene]:", h, file=sys.stderr)
    else:
        print("OK   [privacy/hygiene] 0 leaked IPs, home paths, or bot trailers in diff")

    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())

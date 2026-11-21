#!/usr/bin/env python3
"""Compute affected build and differential-test project matrices for CI."""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from framework._py import ensure_python311

ensure_python311()
from framework.manifest import Project, REPO, load_all_projects

SHARED_INFRA_PREFIXES = (".github/", "framework/", "lean-toolchain", ".gitmodules")
PROJECT_DOC_ONLY_EXACT = frozenset({"AGENTS.md", "README.md", "patches/README.md"})
PROJECT_DOC_ONLY_PREFIXES = ("docs/",)


def commit_exists(repo: Path, rev: str) -> bool:
    if not rev or set(rev) == {"0"}:
        return False
    res = subprocess.run(["git", "cat-file", "-e", f"{rev}^{{commit}}"], cwd=repo, capture_output=True)
    return res.returncode == 0


def changed_files(repo: Path, base: str, head: str = "HEAD") -> list[str]:
    out = subprocess.check_output(["git", "diff", "--name-only", base, head], cwd=repo, text=True)
    return [line.strip() for line in out.splitlines() if line.strip()]


def is_shared_change(path: str) -> bool:
    # Pure documentation files under framework/ (README.md, TEMPLATE_AGENTS.md, PROOF_PLAYBOOK.md)
    # do not affect Lean proofs or verification code.
    if path.startswith("framework/") and path.endswith(".md"):
        return False
    return any(path == p or path.startswith(p) for p in SHARED_INFRA_PREFIXES)


def is_project_doc_only(rel_path: str) -> bool:
    return rel_path in PROJECT_DOC_ONLY_EXACT or any(
        rel_path.startswith(prefix) for prefix in PROJECT_DOC_ONLY_PREFIXES
    )


def matches_difftest(proj: Project, rel_path: str) -> bool:
    difftest = proj.data.get("difftest")
    if not difftest:
        return False
    if is_project_doc_only(rel_path):
        return False
    always = {"lakefile.toml", "lean-toolchain", "project.json"}
    if rel_path in always or re.match(r"^tests/[^/]+$", rel_path):
        return True
    for watch in difftest.get("watch_paths", []):
        if watch.endswith("/"):
            if rel_path.startswith(watch):
                return True
        elif rel_path == watch or rel_path.startswith(watch + "/"):
            return True
    return False


def compute_matrices(
    projects: list[Project],
    event: str,
    changed: list[str] | None,
) -> tuple[list[str], list[str]]:
    """Return (build_projects, difftest_projects).

    When `changed` is None (push to main, workflow_dispatch, or unknown base commit),
    every registered project builds, and every project with difftests runs them.
    """
    all_build = [p.id for p in projects]
    all_difftest = [p.id for p in projects if p.data.get("difftest")]
    if event in ("push", "workflow_dispatch") or changed is None:
        return all_build, all_difftest
    if any(is_shared_change(path) for path in changed):
        return all_build, all_difftest

    build_ids: list[str] = []
    difftest_ids: list[str] = []
    for proj in projects:
        prefix = f"projects/{proj.id}/"
        proj_changes = [path[len(prefix) :] for path in changed if path.startswith(prefix)]
        if not proj_changes:
            continue
        if all(is_project_doc_only(rel) for rel in proj_changes):
            continue
        build_ids.append(proj.id)
        if proj.data.get("difftest") and any(matches_difftest(proj, rel) for rel in proj_changes):
            difftest_ids.append(proj.id)
    return build_ids, difftest_ids


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--event", default=os.environ.get("EVENT", "workflow_dispatch"))
    parser.add_argument("--base", default=os.environ.get("BASE", ""))
    parser.add_argument("--github-output", default=os.environ.get("GITHUB_OUTPUT", ""))
    args = parser.parse_args()

    projects = load_all_projects(REPO)
    changed: list[str] | None = None
    if args.event not in ("push", "workflow_dispatch") and commit_exists(REPO, args.base):
        changed = changed_files(REPO, args.base)

    build_ids, difftest_ids = compute_matrices(projects, args.event, changed)
    outputs = {
        "build_projects": json.dumps(build_ids),
        "difftest_projects": json.dumps(difftest_ids),
        "has_build": "true" if build_ids else "false",
        "has_difftest": "true" if difftest_ids else "false",
    }
    for key, value in outputs.items():
        print(f"{key}={value}")
    if args.github_output:
        with open(args.github_output, "a", encoding="utf-8") as fh:
            for key, value in outputs.items():
                fh.write(f"{key}={value}\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())

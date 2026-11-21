#!/usr/bin/env python3
"""Unified verification gate runner for an oss-proof project."""
from __future__ import annotations

import argparse
import os
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from framework._py import ensure_python311

ensure_python311()
from framework import check_forbidden, check_options, check_runtime_ub, check_spec_layers
from framework import patches as patch_check
from framework.manifest import Project, REPO, load_all_projects, load_project

PARTIAL_CHECK = REPO / "framework/lean/PartialCheck.lean"


def bounded_env(threads: int | None = None) -> dict[str, str]:
    env = os.environ.copy()
    if threads is None:
        raw = env.get("OSS_PROOF_THREADS") or env.get("LEAN_NUM_THREADS")
        if raw and raw.isdigit() and int(raw) > 0:
            threads = min(4, int(raw))
        else:
            threads = min(4, max(1, os.cpu_count() or 1))
    env["LEAN_NUM_THREADS"] = str(threads)
    return env


def run_cmd(cmd: list[str], *, cwd: Path, label: str, env: dict[str, str] | None = None) -> None:
    print(f"==> {label}")
    subprocess.run(cmd, cwd=cwd, env=env, check=True)


def check_orphan_modules(proj: Project) -> list[str]:
    """Ensure every `.lean` file under `<Package>/` is reachable from `<Package>` or `results_module`."""
    pkg = proj.package
    pkg_dir = proj.root / pkg
    if not pkg_dir.is_dir():
        return []
    all_mods: set[str] = set()
    if (proj.root / f"{pkg}.lean").is_file():
        all_mods.add(pkg)
    for path in pkg_dir.rglob("*.lean"):
        parts = list(path.relative_to(proj.root).parts)
        all_mods.add(check_spec_layers.canonical(parts[:-1] + [parts[-1][: -len(".lean")]]))
    roots = [r for r in (pkg, proj.results_module) if r in all_mods]
    seen = set(roots)
    stack = list(roots)
    while stack:
        mod = stack.pop()
        parts = check_spec_layers.components(mod)
        fp = proj.root.joinpath(*parts[:-1], parts[-1] + ".lean")
        if not fp.is_file():
            continue
        for imp in check_spec_layers.header_imports(fp.read_text()):
            canon = check_spec_layers.canonical(check_spec_layers.components(imp))
            if (canon == pkg or canon.startswith(pkg + ".")) and canon not in seen:
                seen.add(canon)
                stack.append(canon)
    return sorted(all_mods - seen)


def check_patches_apply(proj: Project) -> None:
    upstream_cfg = proj.data["upstream"]
    sub_rel = upstream_cfg["submodule"]
    sub_dir = proj.root / sub_rel
    if not sub_dir.is_dir():
        raise RuntimeError(f"[{proj.id}] missing upstream submodule directory: {sub_dir}")
    # Verify the submodule is actually initialized rather than an empty directory whose `git -C`
    # walks up into the parent repository.
    if not (sub_dir / ".git").exists():
        raise RuntimeError(
            f"[{proj.id}] upstream submodule {sub_rel} is not initialized "
            f"(run: git submodule update --init --depth=1 -- projects/{proj.id}/ "
            f"or: python3 framework/worktree_ops.py hydrate {proj.id})"
        )
    top = subprocess.check_output(
        ["git", "-C", str(sub_dir), "rev-parse", "--show-toplevel"],
        text=True,
    ).strip()
    if Path(top).resolve() != sub_dir.resolve():
        raise RuntimeError(
            f"[{proj.id}] upstream submodule {sub_rel} resolved to parent repo {top}; initialize the submodule"
        )
    dirty = subprocess.check_output(
        ["git", "-C", str(sub_dir), "status", "--porcelain", "--untracked-files=all"],
        text=True,
    )
    if dirty:
        raise RuntimeError(f"[{proj.id}] upstream submodule {sub_rel} has local modifications")
    try:
        patch_check.check_project_patches(proj.id, proj.root, proj.data)
    except patch_check.PatchError as exc:
        raise RuntimeError(str(exc)) from exc


def check_one(
    proj: Project,
    *,
    skip_build: bool = False,
    skip_compiled: bool = False,
    skip_patches: bool = False,
    allow_sorry: bool = False,
    threads: int | None = None,
) -> None:
    print(f"=== Checking project: {proj.id} ({proj.package}) ===")
    build_env = bounded_env(threads)
    if not skip_build:
        run_cmd(
            ["lake", "build", "--wfail", *proj.targets],
            cwd=proj.root,
            label=f"[{proj.id}] lake build (LEAN_NUM_THREADS={build_env['LEAN_NUM_THREADS']})",
            env=build_env,
        )

    opt_errors = check_options.check_repo(REPO, [proj.id])
    if opt_errors:
        for err in opt_errors:
            print(err, file=sys.stderr)
        raise RuntimeError(f"[{proj.id}] option/lakefile/toolchain check failed")
    print(f"==> [{proj.id}] options, lakefiles, and toolchains passed")

    forb_hits = check_forbidden.check_project_forbidden(
        proj.root, proj.package, base=REPO, allow_sorry=allow_sorry
    )
    if forb_hits:
        for hit in forb_hits:
            print(hit, file=sys.stderr)
        raise RuntimeError(f"[{proj.id}] forbidden constructs found")
    print(f"==> [{proj.id}] no forbidden constructs in source")

    ub_errors = check_runtime_ub.check_project_runtime_ub(proj, base=REPO)
    if ub_errors:
        for err in ub_errors:
            print(err, file=sys.stderr)
        raise RuntimeError(f"[{proj.id}] runtime strict ISO C17 UB policy check failed")
    print(f"==> [{proj.id}] runtime UB policy passed")

    orphans = check_orphan_modules(proj)
    if orphans:
        for mod in orphans:
            print(f"  orphan module (not imported by {proj.package} or {proj.results_module}): {mod}", file=sys.stderr)
        raise RuntimeError(f"[{proj.id}] {len(orphans)} unimported orphan Lean module(s) found")
    print(f"==> [{proj.id}] import closure passed (0 orphan modules)")

    checks = proj.data.get("checks", {})
    if "spec_layers" in checks:
        allow = check_spec_layers.load_math_allowlist(proj.root, checks["spec_layers"])
        checker = check_spec_layers.SpecLayerChecker(proj.root, proj.package, allow)
        layer_errors, count, remaining = checker.run()
        if layer_errors:
            for err in layer_errors:
                print("  " + err, file=sys.stderr)
            raise RuntimeError(f"[{proj.id}] specification layer check failed")
        print(f"==> [{proj.id}] specification layers passed ({count} spec modules, {remaining} Math->Proof imports)")

    if "strlit" in checks:
        run_cmd([sys.executable, checks["strlit"]], cwd=proj.root, label=f"[{proj.id}] string literal table check")

    for test_rel in checks.get("self_tests", []):
        if skip_compiled and "coverage" in Path(test_rel).name:
            continue
        run_cmd([sys.executable, test_rel], cwd=proj.root, label=f"[{proj.id}] self-test {test_rel}")

    if not skip_compiled:
        partial_args = ["lake", "env", "lean", "--run", str(PARTIAL_CHECK), proj.package]
        if proj.compiler_helpers:
            partial_args.append(str(proj.compiler_helpers))
        if proj.results_module:
            partial_args += ["--results", proj.results_module]
        run_cmd(partial_args, cwd=proj.root, label=f"[{proj.id}] compiled-environment audit (PartialCheck)")

        if "results_self_test" in checks:
            run_cmd(["bash", checks["results_self_test"]], cwd=proj.root, label=f"[{proj.id}] ResultsCheck fixtures")

        if "coverage" in checks:
            run_cmd(
                [sys.executable, checks["coverage"]["script"]],
                cwd=proj.root,
                label=f"[{proj.id}] public API coverage",
            )

    if not skip_patches:
        check_patches_apply(proj)
    print(f"=== Project {proj.id}: ALL CHECKS PASSED ===")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("projects", nargs="*", help="Project IDs to check (default: all registered)")
    parser.add_argument("--skip-build", action="store_true", help="Skip `lake build` (assume already built)")
    parser.add_argument("--source-only", action="store_true", help="Run source/patch checks without compiled environment")
    parser.add_argument(
        "--skip-patches",
        action="store_true",
        help="Skip upstream submodule/patch application check (useful in cold worktrees with uninitialized submodules)",
    )
    parser.add_argument(
        "--allow-sorry",
        action="store_true",
        help="Allow `sorry`/`admit` during source scan (skeleton/* branches only)",
    )
    parser.add_argument(
        "--threads",
        type=int,
        default=None,
        help="Cap LEAN_NUM_THREADS for `lake build` (default: min(4, cpu_count))",
    )
    args = parser.parse_args()

    projects = [load_project(pid, REPO) for pid in args.projects] if args.projects else load_all_projects(REPO)
    try:
        for proj in projects:
            check_one(
                proj,
                skip_build=args.skip_build or args.source_only,
                skip_compiled=args.source_only,
                skip_patches=args.skip_patches,
                allow_sorry=args.allow_sorry,
                threads=args.threads,
            )
        return 0
    except (RuntimeError, subprocess.CalledProcessError) as exc:
        print(f"FAILED: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())

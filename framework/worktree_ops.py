#!/usr/bin/env python3
"""Worktree hydration (CoW `.lake/build` + selective submodule init) and disk-hygiene tool."""
from __future__ import annotations

import argparse
import platform
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from framework._py import ensure_python311

ensure_python311()
from framework.manifest import REPO, load_project

ALLOWED_LAKE_ENTRIES = frozenset({"build", "packages", "config", "package-overrides.json"})


def list_worktrees() -> list[dict]:
    out = subprocess.check_output(["git", "worktree", "list", "--porcelain"], cwd=REPO, text=True)
    entries: list[dict] = []
    cur: dict = {}
    for raw in out.splitlines():
        if not raw.strip():
            if cur:
                entries.append(cur)
                cur = {}
            continue
        key, _, val = raw.partition(" ")
        if key == "worktree":
            cur["path"] = Path(val)
        elif key == "HEAD":
            cur["head"] = val
        elif key == "branch":
            cur["branch"] = val.removeprefix("refs/heads/")
        elif key in ("detached", "prunable", "bare"):
            cur[key] = True
    if cur:
        entries.append(cur)
    return entries


def primary_worktree() -> Path:
    wts = list_worktrees()
    if not wts:
        return REPO
    return wts[0]["path"]


def cow_copy_tree(src: Path, dst: Path) -> None:
    """Copy a directory using copy-on-write reflinks when supported (APFS `cp -cR`, Linux `--reflink=auto`)."""
    dst.parent.mkdir(parents=True, exist_ok=True)
    if dst.exists():
        shutil.rmtree(dst)
    system = platform.system()
    if system == "Darwin":
        res = subprocess.run(["cp", "-cR", str(src), str(dst)])
        if res.returncode == 0:
            return
    elif system == "Linux":
        res = subprocess.run(["cp", "--reflink=auto", "-a", str(src), str(dst)])
        if res.returncode == 0:
            return
    shutil.copytree(src, dst)


def find_lake_junk(lake_dir: Path) -> list[Path]:
    """Return unexpected scratch files/dirs dumped directly inside `.lake/` (outside `build/`, `packages/`, etc.)."""
    if not lake_dir.is_dir():
        return []
    return sorted(p for p in lake_dir.iterdir() if p.name not in ALLOWED_LAKE_ENTRIES)


def dir_size_mb(path: Path) -> float:
    if not path.exists():
        return 0.0
    res = subprocess.run(["du", "-sk", str(path)], capture_output=True, text=True)
    if res.returncode == 0 and res.stdout.strip():
        return int(res.stdout.split()[0]) / 1024.0
    return 0.0


def cmd_hydrate(args: argparse.Namespace) -> int:
    proj = load_project(args.project, REPO)
    seed = Path(args.seed).resolve() if args.seed else primary_worktree().resolve()
    sub_rel = proj.data["upstream"]["submodule"]
    sub_path = proj.root / sub_rel

    if not args.skip_submodule:
        if (sub_path / ".git").exists():
            print(f"==> [{proj.id}] Submodule {sub_rel} already initialized")
        else:
            ref_args: list[str] = []
            seed_sub = seed / "projects" / proj.id / sub_rel
            if seed != REPO.resolve() and (seed_sub / ".git").exists():
                ref_args = ["--reference", str(seed_sub)]
            print(f"==> [{proj.id}] Initializing submodule projects/{proj.id}/{sub_rel}")
            subprocess.run(
                [
                    "git",
                    "submodule",
                    "update",
                    "--init",
                    "--depth=1",
                    *ref_args,
                    "--",
                    f"projects/{proj.id}/{sub_rel}",
                ],
                cwd=REPO,
                check=True,
            )

    if args.skip_lake:
        return 0

    seed_proj = seed / "projects" / proj.id
    seed_build = seed_proj / ".lake/build"
    if seed.resolve() == REPO.resolve():
        print("==> Seed equals current worktree; skipping .lake/build clone")
        return 0
    if not seed_build.is_dir():
        print(f"==> No seed .lake/build found at {seed_build}; skipping CoW cache hydration")
        return 0

    # Safety check: only copy `.lake/build` when toolchain and lakefile.toml match byte-for-byte.
    for fname in ("lean-toolchain", "lakefile.toml"):
        a, b = seed_proj / fname, proj.root / fname
        if not a.is_file() or not b.is_file() or a.read_bytes() != b.read_bytes():
            print(f"==> Skipping .lake/build hydration: {fname} differs from seed worktree")
            return 0

    dst_build = proj.root / ".lake/build"
    print(f"==> [{proj.id}] CoW-cloning .lake/build from {seed_build} -> {dst_build}")
    cow_copy_tree(seed_build, dst_build)
    print(f"==> [{proj.id}] Hydration complete")
    return 0


def cmd_audit(args: argparse.Namespace) -> int:
    wts = list_worktrees()
    print(f"Found {len(wts)} git worktree(s):")
    total_junk_mb = 0.0
    for wt in wts:
        p: Path = wt["path"]
        branch = wt.get("branch", "(detached)" if wt.get("detached") else "(unknown)")
        flags = [k for k in ("prunable", "detached") if wt.get(k)]
        flag_str = f" [{','.join(flags)}]" if flags else ""
        size_mb = dir_size_mb(p) if args.sizes and p.is_dir() else 0.0
        size_str = f" {size_mb:8.1f} MiB" if args.sizes else ""
        print(f"  {branch:40s}{size_str}{flag_str}  {p}")
        if p.is_dir():
            for lake_dir in sorted(p.glob("projects/*/.lake")):
                junk = find_lake_junk(lake_dir)
                if junk:
                    jmb = sum(dir_size_mb(j) for j in junk)
                    total_junk_mb += jmb
                    print(
                        f"    JUNK in {lake_dir}: {len(junk)} non-build item(s), "
                        f"~{jmb:.1f} MiB (e.g. {', '.join(j.name for j in junk[:5])})"
                    )
    if total_junk_mb > 0:
        print(f"\nTotal non-build junk inside .lake/ directories: ~{total_junk_mb:.1f} MiB")
    return 0


def cmd_gc(args: argparse.Namespace) -> int:
    wts = list_worktrees()
    targets: list[Path] = []
    for wt in wts:
        p: Path = wt["path"]
        if not p.is_dir():
            continue
        for lake_dir in sorted(p.glob("projects/*/.lake")):
            targets.extend(find_lake_junk(lake_dir))

    if not targets:
        print("No non-build junk found inside any projects/*/.lake/ directory.")
        return 0

    total_mb = sum(dir_size_mb(t) for t in targets)
    mode = "REMOVING" if args.apply else "DRY-RUN (pass --apply to remove)"
    print(f"{mode}: {len(targets)} non-build item(s) inside .lake/ (~{total_mb:.1f} MiB):")
    for t in targets:
        print(f"  {t}")
        if args.apply:
            if t.is_dir() and not t.is_symlink():
                shutil.rmtree(t)
            else:
                t.unlink(missing_ok=True)
    if args.apply:
        subprocess.run(["git", "worktree", "prune"], cwd=REPO, check=False)
        print("Cleanup complete.")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_hyd = sub.add_parser("hydrate", help="CoW-clone .lake/build and initialize a single project's submodule")
    p_hyd.add_argument("project", help="Project ID to hydrate")
    p_hyd.add_argument("--from", dest="seed", help="Seed worktree path (default: primary checkout)")
    p_hyd.add_argument("--skip-submodule", action="store_true")
    p_hyd.add_argument("--skip-lake", action="store_true")
    p_hyd.set_defaults(func=cmd_hydrate)

    p_aud = sub.add_parser("audit", help="Audit worktrees and non-build junk inside .lake/")
    p_aud.add_argument("--sizes", action="store_true", help="Compute disk size per worktree (slower)")
    p_aud.set_defaults(func=cmd_audit)

    p_gc = sub.add_parser("gc", help="Remove non-build scratch junk dumped inside .lake/ (dry-run by default)")
    p_gc.add_argument("--apply", action="store_true", help="Actually delete non-build .lake/ junk and prune stale worktrees")
    p_gc.set_defaults(func=cmd_gc)

    args = parser.parse_args()
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())

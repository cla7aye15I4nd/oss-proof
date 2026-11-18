#!/usr/bin/env python3
"""Build differential test drivers and execute ASan + UBSan differential tests for a project."""
from __future__ import annotations

import argparse
import os
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from framework.manifest import Project, REPO, check_relative_path, load_project


def driver_targets(list_file: Path) -> list[str]:
    targets: list[str] = []
    for raw in list_file.read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        targets.append(f"difftest_{line}")
    if not targets:
        raise RuntimeError(f"no differential test drivers listed in {list_file}")
    return targets


def run_project_difftest(proj: Project, *, san: bool = True) -> None:
    dt = proj.data.get("difftest")
    if not dt:
        raise RuntimeError(f"[{proj.id}] has no difftest configuration in project.json")

    root_tc = (REPO / "lean-toolchain").read_text()
    for rel in ("lean-toolchain", f"{dt['dir']}/lean-toolchain"):
        tc_path = proj.root / check_relative_path(rel)
        if tc_path.is_file() and tc_path.read_text() != root_tc:
            raise RuntimeError(f"[{proj.id}] {tc_path} differs from root lean-toolchain")

    dt_dir = proj.root / check_relative_path(dt["dir"])
    if dt.get("list"):
        list_file = proj.root / check_relative_path(dt["list"])
        targets = driver_targets(list_file)
        print(f"==> [{proj.id}] Building {len(targets)} differential drivers with --wfail")
        subprocess.run(["lake", "build", "--wfail", *targets], cwd=dt_dir, check=True)

    upstream_sub = proj.root / check_relative_path(proj.data["upstream"]["submodule"])
    env = os.environ.copy()
    env["PROJECT_DIR"] = str(proj.root)
    env["UPSTREAM_DIR"] = str(upstream_sub)
    if dt.get("upstream_env"):
        env[dt["upstream_env"]] = str(upstream_sub)
    if san:
        env["SAN"] = "1"

    runner = dt.get("script", f"{dt['dir']}/run.sh")
    runner_path = proj.root / check_relative_path(runner)
    print(f"==> [{proj.id}] Running differential test suite ({runner}) with SAN={env.get('SAN', '0')}")
    subprocess.run(["bash", str(runner_path)], cwd=proj.root, env=env, check=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", help="Project ID to differential-test")
    parser.add_argument("--no-san", action="store_true", help="Run without ASan/UBSan")
    args = parser.parse_args()
    proj = load_project(args.project, REPO)
    try:
        run_project_difftest(proj, san=not args.no_san)
        return 0
    except (RuntimeError, subprocess.CalledProcessError) as exc:
        print(f"FAILED: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())

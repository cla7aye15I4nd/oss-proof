#!/usr/bin/env python3
"""Build the unified oss-proof site (portal + all registered project subsites) into site/dist/."""
from __future__ import annotations

from pathlib import Path
import shutil
import subprocess
import sys

SITE_DIR = Path(__file__).resolve().parent
REPO = SITE_DIR.parent
OUT = SITE_DIR / "dist"

sys.path.insert(0, str(REPO))
from framework.manifest import load_all_projects
import portal


def main() -> int:
    if OUT.exists():
        shutil.rmtree(OUT)
    OUT.mkdir(parents=True, exist_ok=True)
    portal.build_portal()
    for proj in load_all_projects(REPO):
        builder = proj.data.get("site", {}).get("builder")
        if builder:
            subprocess.run([sys.executable, builder], cwd=proj.root, check=True)
    print("Built complete oss-proof site in site/dist/")
    return 0


if __name__ == "__main__":
    sys.exit(main())

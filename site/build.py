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
import hidden_pages
import portal
import project_docs


def main() -> int:
    if OUT.exists():
        shutil.rmtree(OUT)
    OUT.mkdir(parents=True, exist_ok=True)
    summaries = portal.build_portal()
    hidden_pages.build_unlisted_pages(summaries)
    for summary in summaries:
        builder = summary.project.data.get("site", {}).get("builder")
        if builder:
            subprocess.run([sys.executable, builder], cwd=summary.project.root, check=True)
        else:
            project_docs.build_standard_subsite(summary, summaries)
    print("Built complete oss-proof site in site/dist/")
    return 0


if __name__ == "__main__":
    sys.exit(main())

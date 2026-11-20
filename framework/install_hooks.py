#!/usr/bin/env python3
"""Install local git hooks (`.githooks/`) enforcing oss-proof commit and privacy hygiene.

Guards against historical git accidents:
- Bot author/committer identities (`[bot]`) and `Co-Authored-By:` trailers.
- Privacy leaks (private IPs, absolute `/Users/` or `/home/` paths) in staged diffs or commit messages.
- Accidental mass deletion of >10 tracked `.lean` files (e.g. from `git add -A`), overrideable with
  `ALLOW_MASS_DELETE=1`.
"""
from __future__ import annotations

import argparse
import os
import stat
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from framework._py import ensure_python311

ensure_python311()
from framework.manifest import REPO

PRE_COMMIT_HOOK = r"""#!/usr/bin/env bash
set -euo pipefail

author_name="$(git var GIT_AUTHOR_IDENT)"
if printf '%s' "$author_name" | grep -qi '\[bot\]'; then
  echo "pre-commit: refusing bot author identity: $author_name" >&2
  exit 1
fi

if [ "${ALLOW_MASS_DELETE:-0}" != 1 ]; then
  deleted_lean="$(git diff --cached --diff-filter=D --name-only -- '*.lean' | wc -l | tr -d ' ')"
  if [ "$deleted_lean" -gt 10 ]; then
    echo "pre-commit: refusing to delete $deleted_lean tracked .lean files (set ALLOW_MASS_DELETE=1 to override)" >&2
    exit 1
  fi
fi

staged_diff="$(git diff --cached -U0)"
if printf '%s\n' "$staged_diff" | grep -E '^\+[^+]' | grep -Eq '(/Users/|/home/)[A-Za-z0-9._-]+/|100\.(6[4-9]|[7-9][0-9]|1[01][0-9]|12[0-7])\.[0-9]{1,3}\.[0-9]{1,3}'; then
  echo "pre-commit: staged diff appears to contain an absolute home path or private 100.64/10 IP" >&2
  echo "  (review staged lines; never commit local paths, usernames, hostnames, or IPs)" >&2
  exit 1
fi
"""

COMMIT_MSG_HOOK = r"""#!/usr/bin/env bash
set -euo pipefail
msg_file="$1"
if grep -qiE '^\s*Co-Authored-By:|\[bot\]|(/Users/|/home/)[A-Za-z0-9._-]+/|100\.(6[4-9]|[7-9][0-9]|1[01][0-9]|12[0-7])\.[0-9]{1,3}\.[0-9]{1,3}' "$msg_file"; then
  echo "commit-msg: refusing commit message containing Co-Authored-By, [bot], local path, or private IP" >&2
  exit 1
fi
"""


def install_hooks(repo: Path = REPO, *, configure_git: bool = True) -> Path:
    hooks_dir = repo / ".githooks"
    hooks_dir.mkdir(parents=True, exist_ok=True)
    for name, body in (("pre-commit", PRE_COMMIT_HOOK), ("commit-msg", COMMIT_MSG_HOOK)):
        p = hooks_dir / name
        p.write_text(body)
        p.chmod(p.stat().st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)
    if configure_git:
        subprocess.run(["git", "config", "core.hooksPath", ".githooks"], cwd=repo, check=True)
    return hooks_dir


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-git-config", action="store_true", help="Write hooks without setting core.hooksPath")
    args = parser.parse_args()
    hooks_dir = install_hooks(REPO, configure_git=not args.no_git_config)
    print(f"Installed oss-proof git hooks in {hooks_dir}")
    if not args.no_git_config:
        print("Configured git core.hooksPath = .githooks")
    return 0


if __name__ == "__main__":
    sys.exit(main())

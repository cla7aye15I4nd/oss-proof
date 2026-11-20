"""Python 3.11+ interpreter guard for oss-proof framework scripts.

macOS ships Python 3.9 as `/usr/bin/python3`, which lacks `tomllib`. Calling
`ensure_python311()` before importing `tomllib` transparently re-execs with an
installed Python 3.11+ interpreter when available, or exits with an actionable error.
"""
from __future__ import annotations

import os
import shutil
import sys


def ensure_python311() -> None:
    if sys.version_info >= (3, 11):
        return
    candidates = [
        "/opt/homebrew/bin/python3.14",
        "/opt/homebrew/bin/python3.13",
        "/opt/homebrew/bin/python3.12",
        "/opt/homebrew/bin/python3.11",
        "/usr/local/bin/python3.13",
        "/usr/local/bin/python3.12",
        "/usr/local/bin/python3.11",
    ]
    for name in ("python3.14", "python3.13", "python3.12", "python3.11"):
        found = shutil.which(name)
        if found:
            candidates.append(found)
    seen: set[str] = set()
    for exe in candidates:
        if exe in seen or not os.path.isfile(exe) or not os.access(exe, os.X_OK):
            continue
        seen.add(exe)
        os.execv(exe, [exe, *sys.argv])
    sys.stderr.write(
        f"error: oss-proof framework scripts require Python 3.11+ (current: {sys.version.split()[0]})\n"
    )
    sys.exit(2)

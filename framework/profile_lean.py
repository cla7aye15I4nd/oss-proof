#!/usr/bin/env python3
"""Profile a Lean 4 proof file to pinpoint heartbeat and WHNF unfolding bottlenecks.

Runs `lake env lean -Dprofiler=true -Dprofiler.threshold=<ms>` on a single file and ranks the
slowest declarations and compiler phases (`elaboration`, `whnf`, `simp`, `omega`, `grind`,
`type checking`), helping eliminate blind `set_option maxHeartbeats` bumps.
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from framework._py import ensure_python311

ensure_python311()
from framework.manifest import REPO

TIME_LINE_RE = re.compile(r"^\s*\[([^\]]+)\]\s+\[([0-9.]+)(ms|s)\]\s*(.*)$")
CUMULATIVE_RE = re.compile(r"^\s*([a-zA-Z0-9_ .:-]+?)\s+([0-9.]+)(ms|s)\s*$")
HEARTBEAT_RE = re.compile(r"^\s*set_option\s+maxHeartbeats\s+(\d+)")


def to_ms(val: str, unit: str) -> float:
    f = float(val)
    return f * 1000.0 if unit == "s" else f


def parse_profiler_output(output: str) -> dict:
    events: list[tuple[float, str, str]] = []
    by_category: dict[str, float] = defaultdict(float)
    in_cumulative = False
    cumulative: list[tuple[float, str]] = []
    for line in output.splitlines():
        if "cumulative profiling times:" in line:
            in_cumulative = True
            continue
        if in_cumulative:
            cm = CUMULATIVE_RE.match(line)
            if cm:
                cumulative.append((to_ms(cm.group(2), cm.group(3)), cm.group(1).strip()))
            continue
        m = TIME_LINE_RE.match(line)
        if m:
            cat, ms, msg = m.group(1).strip(), to_ms(m.group(2), m.group(3)), m.group(4).strip()
            events.append((ms, cat, msg))
            by_category[cat] += ms
    events.sort(reverse=True)
    cumulative.sort(reverse=True)
    return {
        "events": events,
        "by_category": sorted(by_category.items(), key=lambda x: x[1], reverse=True),
        "cumulative": cumulative,
    }


def detect_project_dir(lean_file: Path) -> Path:
    for parent in [lean_file.parent, *lean_file.parents]:
        if (parent / "lakefile.toml").is_file():
            return parent
    raise RuntimeError(f"could not locate lakefile.toml above {lean_file}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("lean_file", help="Path to a .lean file inside a project or framework/lean")
    parser.add_argument("--threshold", type=int, default=20, help="Profiler threshold in ms (default: 20)")
    parser.add_argument("--top", type=int, default=15, help="Number of hottest entries to print")
    args = parser.parse_args()

    target = Path(args.lean_file)
    if not target.is_absolute():
        target = (REPO / target).resolve()
    if not target.is_file():
        print(f"error: file not found: {target}", file=sys.stderr)
        return 2

    proj_dir = detect_project_dir(target)
    raw = target.read_text()
    loc = len(raw.splitlines())
    hb_lines = [
        (ln, int(m.group(1)))
        for ln, line in enumerate(raw.splitlines(), 1)
        for m in [HEARTBEAT_RE.match(line)]
        if m
    ]

    cmd = [
        "lake",
        "env",
        "lean",
        "-Dprofiler=true",
        f"-Dprofiler.threshold={args.threshold}",
        str(target),
    ]
    print(f"==> Profiling {target.relative_to(REPO) if target.is_relative_to(REPO) else target} ({loc} LOC)")
    if hb_lines:
        print(f"    Existing maxHeartbeats overrides: {hb_lines}")
    res = subprocess.run(cmd, cwd=proj_dir, text=True, capture_output=True)
    combined = (res.stdout or "") + "\n" + (res.stderr or "")
    parsed = parse_profiler_output(combined)

    if parsed["cumulative"]:
        print("\n=== Cumulative profiling phases ===")
        for ms, cat in parsed["cumulative"][: args.top]:
            print(f"  {ms:9.1f} ms  {cat}")

    if parsed["events"]:
        print(f"\n=== Top {args.top} slowest profiler events ===")
        for ms, cat, msg in parsed["events"][: args.top]:
            print(f"  {ms:9.1f} ms  [{cat}] {msg[:120]}")

    if loc > 1500:
        print(
            f"\nHINT: File is {loc} LOC (>1500). Split into 400-800 LOC phase modules linked via `rfl` "
            "(see framework/PROOF_PLAYBOOK.md §2.3)."
        )
    if res.returncode != 0:
        print(f"\nLean exited with code {res.returncode}; tail of output:")
        for line in combined.splitlines()[-25:]:
            print("  " + line)
    return res.returncode


if __name__ == "__main__":
    sys.exit(main())

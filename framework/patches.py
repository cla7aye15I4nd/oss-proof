"""Discover and check the patches of an oss-proof project.

Two layouts are supported, chosen by `upstream.patch_layout` in `project.json`:

* `"flat"` (the default): `patches_dir/*.patch`, applied in name order.
* `"directories"`: one directory per patch, `patches_dir/NNNN-slug/`, numbered consecutively from 0001 and
  applied in name order. Each directory holds `upstream.patch` (a `git format-patch` series of one or more
  commits, library and test hunks) and `pr-summary.md`; it may also hold `gtest.txt` (the GoogleTest cases the
  series adds, read by the project's own test runner). `patches_dir/README.md` must list exactly the directories,
  in order, as index rows `| [NNNN-slug](NNNN-slug/pr-summary.md) | ...`. The verified source is the pinned
  submodule with every `upstream.patch` applied in full by `git apply`, in directory name order.

A project that declares patches (`site.patches_count` above 0, or the directory layout) and has none fails the
check instead of passing silently.
"""
from __future__ import annotations

import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

SERIES_DIR = re.compile(r"^(\d{4})-[a-z0-9][a-z0-9-]*$")
INDEX_ROW = re.compile(r"^\|\s*\[(\d{4}-[a-z0-9][a-z0-9-]*)\]\(\1/pr-summary\.md\)\s*\|")
SERIES_FILES = ("upstream.patch", "pr-summary.md")
OPTIONAL_FILES = ("gtest.txt",)
LAYOUTS = ("flat", "directories")


class PatchError(RuntimeError):
    pass


def layout_of(upstream_cfg: dict) -> str:
    layout = upstream_cfg.get("patch_layout", "flat")
    if layout not in LAYOUTS:
        raise PatchError(f"unknown upstream.patch_layout {layout!r} (expected one of {', '.join(LAYOUTS)})")
    return layout


def discover(patches_dir: Path, layout: str) -> list[Path]:
    """The patch files to apply, in order. Raises PatchError on a malformed directory layout."""
    if not patches_dir.is_dir():
        return []
    if layout == "flat":
        return sorted(patches_dir.glob("*.patch"))
    stray = sorted(p.name for p in patches_dir.glob("*.patch"))
    if stray:
        raise PatchError(f"{patches_dir}: flat patch files in a directory layout: {', '.join(stray)}")
    errors: list[str] = []
    series: list[Path] = []
    entries = sorted(p for p in patches_dir.iterdir() if p.is_dir())
    for expected, d in enumerate(entries, start=1):
        m = SERIES_DIR.match(d.name)
        if not m:
            errors.append(f"{d.name}: not a patch directory name (NNNN-slug)")
            continue
        if int(m.group(1)) != expected:
            errors.append(f"{d.name}: expected number {expected:04d} (directories are numbered consecutively from 0001)")
        names = {p.name for p in d.iterdir()}
        for f in SERIES_FILES:
            if f not in names:
                errors.append(f"{d.name}: missing {f}")
        extra = sorted(names - set(SERIES_FILES) - set(OPTIONAL_FILES))
        if extra:
            errors.append(f"{d.name}: unexpected files {', '.join(extra)}")
        series.append(d / "upstream.patch")
    if errors:
        raise PatchError(f"{patches_dir}: " + "; ".join(errors))
    readme = patches_dir / "README.md"
    if not readme.is_file():
        raise PatchError(f"{patches_dir}: missing README.md (the patch index)")
    listed = [m.group(1) for line in readme.read_text().splitlines() if (m := INDEX_ROW.match(line))]
    names = [p.parent.name for p in series]
    if listed != names:
        raise PatchError(
            f"{readme}: index rows {listed} do not list exactly the patch directories {names} in order"
        )
    return series


def declared_count(data: dict) -> int | None:
    count = data.get("site", {}).get("patches_count")
    return count if isinstance(count, int) else None


def apply_all(tree: Path, patches: list[Path]) -> None:
    """Apply every patch in full with `git apply` to `tree`, which must not be inside a git work tree."""
    env = os.environ.copy()
    env["GIT_CEILING_DIRECTORIES"] = str(tree.resolve().parent)
    for patch in patches:
        res = subprocess.run(
            ["git", "apply", "--whitespace=nowarn", str(patch.resolve())],
            cwd=tree, env=env, capture_output=True, text=True,
        )
        if res.returncode != 0:
            raise PatchError(f"{patch} does not apply in order:\n{res.stderr}")


def check_project_patches(project_id: str, root: Path, data: dict) -> int:
    """Check that the declared patches exist and apply cleanly, in order, to a copy of the submodule.

    Returns the number of patch files applied."""
    upstream_cfg = data["upstream"]
    patches_rel = upstream_cfg.get("patches_dir")
    layout = layout_of(upstream_cfg)
    count = declared_count(data)
    if not patches_rel:
        if layout == "directories" or (count or 0) > 0:
            raise PatchError(f"[{project_id}] declares patches but has no upstream.patches_dir")
        return 0
    patches_dir = root / patches_rel
    patches = discover(patches_dir, layout)
    if not patches:
        if layout == "directories" or (count or 0) > 0:
            raise PatchError(f"[{project_id}] declares patches but none were found in {patches_dir}")
        return 0
    if layout == "directories" and count != len(patches):
        raise PatchError(
            f"[{project_id}] site.patches_count is {count}, but {patches_dir} holds {len(patches)} patch directories"
        )
    sub_dir = root / upstream_cfg["submodule"]
    print(f"==> [{project_id}] Applying {len(patches)} patches ({layout} layout) to a clean copy of {upstream_cfg['submodule']}")
    with tempfile.TemporaryDirectory() as tmp:
        copy_dir = Path(tmp) / "verified-src"
        shutil.copytree(sub_dir, copy_dir, symlinks=True)
        git_marker = copy_dir / ".git"
        if git_marker.is_dir():
            shutil.rmtree(git_marker)
        elif git_marker.is_file():
            git_marker.unlink()
        apply_all(copy_dir, patches)
    return len(patches)

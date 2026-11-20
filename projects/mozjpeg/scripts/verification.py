#!/usr/bin/env python3
"""Coverage of the public API against `mozjpeg/jpeglib.h` and `MozjpegF/Results.lean`."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = Path("tests/audit/public-api.json")
HEADER = "mozjpeg/jpeglib.h"
SUBMODULE = "mozjpeg"
PACKAGE = "MozjpegF"
SAFETY = PACKAGE + ".Spec.Safety.Goal."
FUNCTIONAL = PACKAGE + ".Spec.Functional.Goal."
STATUSES = ("done", "not-done")
API_KEYS = {"function", "status", "scope", "source", "implementation", "safety_goal", "other_goals", "reason"}


class Rejected(Exception):
    pass


def results(root: Path = ROOT) -> dict[str, list[str]]:
    """The lists `proved`, `notDone` and `required` of MozjpegF/Results.lean as Lean evaluates them."""
    out = subprocess.run(
        ["lake", "env", "lean", "--run", "scripts/results-lists.lean"],
        cwd=root,
        text=True,
        capture_output=True,
        check=True,
    ).stdout
    lists: dict[str, list[str]] = {"proved": [], "notDone": [], "required": []}
    for line in out.splitlines():
        kind, name = line.split(" ", 1)
        lists[kind].append(name)
    return lists


def strip_comments(header: str) -> str:
    return re.sub(r"/\*.*?\*/", "", header, flags=re.S)


def public_names(header: str) -> list[str]:
    """Every function `mozjpeg/jpeglib.h` declares with `EXTERN(...)`, in order, each once."""
    names = re.findall(r"EXTERN\s*\([^)]*\)\s*(\w+)\s*(?:JPP|\()", strip_comments(header), re.S)
    return list(dict.fromkeys(names))


def check_entry_point(root: Path, api: dict) -> None:
    source = api.get("source")
    path = Path(source) if isinstance(source, str) else None
    if (
        path is None
        or path.is_absolute()
        or ".." in path.parts
        or not path.parts
        or path.parts[0] != PACKAGE
        or (root / path).is_symlink()
        or not (root / path).is_file()
    ):
        raise Rejected(f"translated source must be an ordinary file under {PACKAGE}/: {api['function']}: {source}")
    text = (root / path).read_text()
    if not re.search(r"^def\s+«?" + re.escape(api["function"]) + r"»?(?:\s|:)", text, re.M):
        raise Rejected(f"missing translated entry: {api['function']} in {source}")
    namespace = re.search(r"^namespace\s+(\S+)", text, re.M)
    if not namespace or api.get("implementation") != namespace[1] + "." + api["function"]:
        raise Rejected(f"wrong translated entry binding: {api['function']}: {api.get('implementation')}")


def check_manifest(manifest: dict, header: str, lists: dict[str, list[str]], root: Path = ROOT) -> dict:
    """Check the inventory against the header and the lists of MozjpegF/Results.lean; return counts."""
    if manifest.get("version") != 1:
        raise Rejected("unknown public API manifest version")
    if manifest.get("header") != HEADER:
        raise Rejected(f"the manifest must name the header {HEADER}")
    apis = manifest.get("apis")
    if not isinstance(apis, list):
        raise Rejected("apis must be a list")
    names = [a.get("function") for a in apis]
    exports = public_names(header)
    if len(names) != len(set(names)) or set(names) != set(exports):
        raise Rejected(
            f"public API coverage differs from {HEADER}: missing={sorted(set(exports) - set(names))}, "
            f"extra={sorted(set(names) - set(exports))}, "
            f"duplicated={sorted({n for n in names if names.count(n) > 1})}"
        )
    proved, not_done, required = set(lists["proved"]), set(lists["notDone"]), set(lists["required"])
    counts = {status: 0 for status in STATUSES}
    named: list[str] = []
    for api in apis:
        function = api["function"]
        extra = set(api) - API_KEYS
        if extra:
            raise Rejected(f"unknown keys in the entry of {function}: {sorted(extra)}")
        status = api.get("status")
        if status not in STATUSES:
            raise Rejected(f"status of {function} must be one of {STATUSES}: {status}")
        if api.get("scope") != "lp64-linux":
            raise Rejected(f"scope of {function} must be lp64-linux")
        counts[status] += 1
        own = SAFETY + function + "_safety"
        if status == "done":
            if api.get("safety_goal") != own:
                raise Rejected(f"a done function names its own safety goal {own}: {function}: {api.get('safety_goal')}")
            others = api.get("other_goals", [])
            if not isinstance(others, list) or not all(isinstance(g, str) for g in others):
                raise Rejected(f"other_goals of {function} must be a list of goal names")
            for goal in [own] + others:
                if not (goal.startswith(SAFETY) or goal.startswith(FUNCTIONAL)):
                    raise Rejected(f"goal outside the specification namespaces: {function}: {goal}")
                if goal not in proved:
                    raise Rejected(f"goal named by the done function {function} is not proved in Results.lean: {goal}")
                if goal not in required:
                    raise Rejected(
                        f"goal named by the done function {function} is missing from `required` "
                        f"in Results.lean: {goal}"
                    )
                named.append(goal)
            if "reason" in api:
                raise Rejected(f"a done function has no reason: {function}")
            check_entry_point(root, api)
        else:
            if not isinstance(api.get("reason"), str) or not api["reason"].strip():
                raise Rejected(f"a {status} function needs a reason: {function}")
            if any(k in api for k in ("safety_goal", "other_goals", "implementation", "source")):
                raise Rejected(f"a {status} function names no goal and no translation: {function}")
            if own in proved:
                raise Rejected(f"{function} is listed as {status} but its safety goal is proved: {own}")
    if len(named) != len(set(named)):
        raise Rejected("a goal is named by two functions")
    stale = sorted(g for g in named if g in not_done)
    if stale:
        raise Rejected("goals named by done functions are listed as not done: " + ", ".join(stale))
    return {"declared": len(exports), "goals": len(named), **counts}


def check_source_pin(manifest: dict, root: Path = ROOT) -> None:
    pin = subprocess.check_output(["git", "-C", SUBMODULE, "rev-parse", "HEAD"], cwd=root, text=True).strip()
    if pin != manifest.get("source_pin"):
        raise Rejected(f"the checked-out submodule {SUBMODULE} is at {pin}, the manifest pins {manifest.get('source_pin')}")
    index = subprocess.check_output(["git", "ls-files", "-s", "--", SUBMODULE], cwd=root, text=True).split()
    if len(index) < 2 or index[0] != "160000":
        raise Rejected(f"{SUBMODULE} must be a submodule recorded in the repository index")
    if index[1] != pin:
        raise Rejected(
            f"the repository index records {SUBMODULE} at {index[1]}, not at the pinned and checked-out commit {pin}"
        )
    dirty = subprocess.check_output(
        ["git", "-C", SUBMODULE, "status", "--porcelain", "--untracked-files=all"],
        cwd=root,
        text=True,
    )
    if dirty:
        raise Rejected(f"the pinned source submodule {SUBMODULE} has local changes")


def check_imports(root: Path = ROOT) -> None:
    """Every module under MozjpegF/ is in the import closure of MozjpegF.lean and MozjpegF/Results.lean."""
    seen: set[Path] = set()

    def visit(path: Path) -> None:
        if path in seen:
            return
        seen.add(path)
        for line in path.read_text().splitlines():
            if not line.startswith("import "):
                continue
            for name in line[7:].split("--", 1)[0].split():
                local = name == PACKAGE or name.startswith(PACKAGE + ".")
                standard = any(name == p or name.startswith(p + ".") for p in ("Init", "Std", "Lean"))
                if not local and not standard:
                    raise Rejected(f"unapproved external module: {name}")
                parts = re.findall(r"«[^»]+»|[^.]+", name)
                child = root / ("/".join(p.strip("«»") for p in parts) + ".lean")
                if child.is_file():
                    if not local:
                        raise Rejected(f"local source shadows a standard module: {name}")
                    visit(child)
                elif local:
                    raise Rejected(f"import has no source (a stale object could hide it): {name}")

    visit(root / (PACKAGE + ".lean"))
    visit(root / PACKAGE / "Results.lean")
    missing = set((root / PACKAGE).rglob("*.lean")) - seen
    if missing:
        raise Rejected(
            "modules outside the audited import closure: "
            + ", ".join(str(p.relative_to(root)) for p in sorted(missing))
        )


def main() -> int:
    argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter).parse_args()
    try:
        manifest = json.loads((ROOT / MANIFEST).read_text())
        header = (ROOT / HEADER).read_text()
        counts = check_manifest(manifest, header, results())
        check_source_pin(manifest)
        check_imports()
        print(
            f"coverage: {counts['declared']} public functions in {HEADER}: "
            f"{counts['done']} done, {counts['not-done']} not done; "
            f"{counts['goals']} goals named, all proved and required"
        )
        print("coverage passed")
        return 0
    except (Rejected, OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f"REJECTED: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())

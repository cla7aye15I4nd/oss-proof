#!/usr/bin/env python3
"""Coverage of the public API: the part of the checking that needs `zlib-ng/zlib.h.in`.

`ZlibNgF/Results.lean` is checked by Lean when the library is built: exact goals, allowed axioms, every
goal listed, every goal of its list `required` proved. This script checks the inventory
`tests/audit/public-api.json` against the header and against those lists:

* the inventory names every function that `zlib.h.in` declares with `Z_EXTERN` (the header of the
  `ZLIB_COMPAT` build), each exactly once, and no other;
* each function is either `done` or `not-done` (or `not-applicable`, only for the Windows-only
  `gzopen_w`); a `not-done` or `not-applicable` entry gives a reason;
* a `done` function names its own safety goal `ZlibNgF.Spec.Safety.Goal.<function>_safety`, and that goal
  and every other goal the entry names are proved and in `required` of `ZlibNgF/Results.lean` (so the
  library build fails if one of them stops being proved);
* a `not-done` function has no proved safety goal of its own (a stale entry is rejected);
* the translated entry point exists in the named source with the named Lean name;
* the source pin of the inventory is the checked-out submodule commit and the commit recorded for the
  submodule in the repository index, and the submodule has no local changes;
* every module under `ZlibNgF/` is in the import closure of `ZlibNgF.lean` and `ZlibNgF/Results.lean`.

It reads the lists as Lean evaluates them (`scripts/results-lists.lean`), so it needs the built library.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = Path("tests/audit/public-api.json")
HEADER = "zlib-ng/zlib.h.in"
SUBMODULE = "zlib-ng"
PACKAGE = "ZlibNgF"
SAFETY = PACKAGE + ".Spec.Safety.Goal."
FUNCTIONAL = PACKAGE + ".Spec.Functional.Goal."
UNDOCUMENTED_MARK = "/* undocumented functions */"
STATUSES = ("done", "not-done", "not-applicable")
API_KEYS = {"function", "status", "scope", "source", "implementation", "safety_goal", "other_goals", "reason"}


class Rejected(Exception):
    pass


def results(root: Path = ROOT) -> dict[str, list[str]]:
    """The lists `proved`, `notDone` and `required` of ZlibNgF/Results.lean as Lean evaluates them
    (comments and layout of the source play no part). Needs the built library."""
    out = subprocess.run(["lake", "env", "lean", "--run", "scripts/results-lists.lean"], cwd=root,
                         text=True, capture_output=True, check=True).stdout
    lists: dict[str, list[str]] = {"proved": [], "notDone": [], "required": []}
    for line in out.splitlines():
        kind, name = line.split(" ", 1)
        lists[kind].append(name)
    return lists


def strip_comments(header: str) -> str:
    return re.sub(r"/\*.*?\*/", "", header, flags=re.S)


def public_names(header: str) -> list[str]:
    """Every function `zlib.h.in` declares with Z_EXTERN, in order, each once (the *64 functions are
    declared twice, under Z_LARGE64 and under Z_WANT64)."""
    names = re.findall(r"Z_EXTERN\s+[^;]*?\bZ_EXPORT(?:VA)?\s+(?:@ZLIB_SYMBOL_PREFIX@)?(\w+)\s*\(",
                       strip_comments(header), re.S)
    return list(dict.fromkeys(names))


def undocumented_names(header: str) -> set[str]:
    """The functions `zlib.h.in` declares after its undocumented-functions comment."""
    at = header.find(UNDOCUMENTED_MARK)
    return set(public_names(header[at:])) if at >= 0 else set()


def windows_names(header: str) -> set[str]:
    """The functions declared only inside `#if defined(_WIN32)` blocks."""
    names: set[str] = set()
    for block in re.findall(r"#if defined\(_WIN32\)(.*?)#endif", strip_comments(header), re.S):
        names |= set(public_names(block))
    return names


def check_entry_point(root: Path, api: dict) -> None:
    source = api.get("source")
    path = Path(source) if isinstance(source, str) else None
    if path is None or path.is_absolute() or ".." in path.parts or not path.parts or path.parts[0] != PACKAGE \
            or (root / path).is_symlink() or not (root / path).is_file():
        raise Rejected(f"translated source must be an ordinary file under {PACKAGE}/: {api['function']}: {source}")
    text = (root / path).read_text()
    if not re.search(r"^def\s+«?" + re.escape(api["function"]) + r"»?(?:\s|:)", text, re.M):
        raise Rejected(f"missing translated entry: {api['function']} in {source}")
    namespace = re.search(r"^namespace\s+(\S+)", text, re.M)
    if not namespace or api.get("implementation") != namespace[1] + "." + api["function"]:
        raise Rejected(f"wrong translated entry binding: {api['function']}: {api.get('implementation')}")


def check_manifest(manifest: dict, header: str, lists: dict[str, list[str]], root: Path = ROOT) -> dict:
    """Check the inventory against the header and the lists of ZlibNgF/Results.lean; return counts."""
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
        raise Rejected(f"public API coverage differs from {HEADER}: missing={sorted(set(exports) - set(names))}, "
                       f"extra={sorted(set(names) - set(exports))}, "
                       f"duplicated={sorted({n for n in names if names.count(n) > 1})}")
    undocumented = manifest.get("undocumented")
    listed = undocumented.get("functions", []) if isinstance(undocumented, dict) else []
    if not isinstance(undocumented, dict) or undocumented.get("header_comment") != UNDOCUMENTED_MARK or \
            len(listed) != len(set(listed)) or set(listed) != undocumented_names(header):
        raise Rejected(f"undocumented functions differ from {HEADER}: listed={sorted(listed)}, "
                       f"declared={sorted(undocumented_names(header))}")
    proved, not_done, required = set(lists["proved"]), set(lists["notDone"]), set(lists["required"])
    windows = windows_names(header)
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
        counts[status] += 1
        own = SAFETY + function + "_safety"
        if status == "not-applicable":
            if function not in windows or api.get("scope") != "windows":
                raise Rejected(f"only a Windows-only function can be not-applicable: {function}")
        elif api.get("scope") != "lp64-linux" or function in windows:
            raise Rejected(f"scope of {function} must be lp64-linux (and the function not Windows-only)")
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
                    raise Rejected(f"goal named by the done function {function} is missing from `required` "
                                   f"in Results.lean: {goal}")
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
    return {"declared": len(exports), "undocumented": len(listed), "goals": len(named), **counts}


def check_source_pin(manifest: dict, root: Path = ROOT) -> None:
    pin = subprocess.check_output(["git", "-C", SUBMODULE, "rev-parse", "HEAD"], cwd=root, text=True).strip()
    if pin != manifest.get("source_pin"):
        raise Rejected(f"the checked-out submodule {SUBMODULE} is at {pin}, the manifest pins {manifest.get('source_pin')}")
    index = subprocess.check_output(["git", "ls-files", "-s", "--", SUBMODULE], cwd=root, text=True).split()
    if len(index) < 2 or index[0] != "160000":
        raise Rejected(f"{SUBMODULE} must be a submodule recorded in the repository index")
    if index[1] != pin:
        raise Rejected(f"the repository index records {SUBMODULE} at {index[1]}, not at the pinned and "
                       f"checked-out commit {pin}")
    dirty = subprocess.check_output(["git", "-C", SUBMODULE, "status", "--porcelain", "--untracked-files=all"],
                                    cwd=root, text=True)
    if dirty:
        raise Rejected(f"the pinned source submodule {SUBMODULE} has local changes")


def check_imports(root: Path = ROOT) -> None:
    """Every module under ZlibNgF/ is in the import closure of ZlibNgF.lean and ZlibNgF/Results.lean."""
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
        raise Rejected("modules outside the audited import closure: " +
                       ", ".join(str(p.relative_to(root)) for p in sorted(missing)))


def main() -> int:
    argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter).parse_args()
    try:
        manifest = json.loads((ROOT / MANIFEST).read_text())
        header = (ROOT / HEADER).read_text()
        counts = check_manifest(manifest, header, results())
        check_source_pin(manifest)
        check_imports()
        print(f"coverage: {counts['declared']} public functions in {HEADER} "
              f"({counts['undocumented']} undocumented): {counts['done']} done, {counts['not-done']} not done, "
              f"{counts['not-applicable']} not applicable; {counts['goals']} goals named, all proved and required")
        print("coverage passed")
        return 0
    except (Rejected, OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f"REJECTED: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())

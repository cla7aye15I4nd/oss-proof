#!/usr/bin/env python3
"""Coverage of the public API: every function of zlib.h has its goals, and every required goal is proved.

The goals proved and not done are read from `ZlibF/Results.lean`, which Lean checks when the library is
built (each theorem's type is exactly its goal, allowed axioms only, every goal in one of its two lists).
This script checks the rest against `tests/audit/public-api.json` and `zlib/zlib.h`.
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
RESULTS = Path("ZlibF/Results.lean")
# The functions that name their full contract as safety goal (with a safety_note): pure functions with
# no own Goal.<function>_safety. No other function may.
FULL_CONTRACT_SAFETY = ("compressBound", "compressBound_z")
# The safety goals that several functions share, each with exactly the functions that name it. Empty:
# every documented function names its own Goal.<function>_safety (or _safe), or is listed in
# FULL_CONTRACT_SAFETY.
SHARED_SAFETY_GOALS: dict[str, list[str]] = {}


class Rejected(Exception):
    pass


def run(args: list[str], *, stdout=None) -> subprocess.CompletedProcess:
    return subprocess.run(args, cwd=ROOT, text=True, stdout=stdout, check=True)


def results() -> tuple[list[str], list[str]]:
    """The goals of `proved` and of `notDone` in ZlibF/Results.lean, in order."""
    text = (ROOT / RESULTS).read_text()
    lists = {}
    for name in ("proved", "notDone"):
        block = re.search(r"^def " + name + r" : [^\n]*:= \[\n(.*?)^\]", text, re.S | re.M)
        if not block:
            raise Rejected(f"{RESULTS} has no list {name}")
        lists[name] = re.findall(r"^\s*\(?``([^\s,]+)", block[1], re.M)
    return lists["proved"], lists["notDone"]


UNDOCUMENTED_MARK = "/* undocumented functions (not part of the zlib API) */"


def public_names(header: str) -> set[str]:
    header = re.sub(r"/\*.*?\*/", "", header, flags=re.S)
    return set(re.findall(r"ZEXTERN\s+[^;]*?\bZEXPORT(?:VA)?\s+(\w+)\s*\(", header, re.S))


def undocumented_names(header: str) -> set[str]:
    """The exported functions zlib.h declares after its undocumented-functions comment."""
    at = header.find(UNDOCUMENTED_MARK)
    return public_names(header[at:]) if at >= 0 else set()


def check_api_safety_goal(api: dict, hidden: bool, safety_goals: list[str]) -> None:
    """The safety goal an api entry names. A documented function names a listed safety target, or its
    full contract with a safety_note. An undocumented function names nothing, or exactly its own
    Goal.<function>_safety when that goal is in the pinned safety_goals: it is then required through
    that list, as Scope plans for gzvprintf."""
    safety = api.get("safety_goal")
    if hidden:
        own = "ZlibF.Spec.Public.Goal." + api["function"] + "_safety"
        if safety is not None and (safety != own or own not in safety_goals):
            raise Rejected(f"undocumented function names a safety goal other than its own pinned goal: "
                           f"{api['function']}: {safety}")
    elif not isinstance(safety, str):
        raise Rejected(f"missing safety goal: {api['function']}")
    elif safety == api["functional_goal"]:
        if not api.get("safety_note"):
            raise Rejected(f"a full contract used as safety goal needs a safety_note: {api['function']}")
    elif safety not in safety_goals:
        raise Rejected(f"safety goal is not a listed safety target: {api['function']}: {safety}")


def required_public_goals(manifest: dict) -> list[str]:
    """The required targets: the safety goal of every function compiled by the target and part of
    the zlib API, the listed safety goals and the non-vacuity goals
    (docs/design/safety-functional-split.md).

    zlib.h declares some exported functions as undocumented and not part of the zlib API. They stay
    in the inventory, and their registered theorems stay audited, but their goals are not required.
    A functional goal is not required: a registered proof of it is audited in full, an unproved one
    is reported and fails nothing.
    """
    hidden = set(manifest.get("undocumented", {}).get("functions", []))
    required = [a["safety_goal"] for a in manifest["apis"]
                if a["scope"] == "lp64-linux" and a["function"] not in hidden]
    required += manifest.get("safety_goals", []) + manifest.get("nonvacuity_goals", [])
    return list(dict.fromkeys(required))


def functional_goals(manifest: dict) -> list[str]:
    """The functional goals: each function's full contract and the sequence goals. Not required."""
    goals = [a["functional_goal"] for a in manifest["apis"] if a["scope"] == "lp64-linux"]
    return list(dict.fromkeys(goals + manifest.get("sequence_goals", [])))


def open_safety(manifest: dict) -> list[str]:
    return [entry["goal"] for entry in manifest.get("open_safety", [])]


def check_not_planned(manifest: dict) -> None:
    """`not_planned` names goals that stay stated and listed as not done but are not planned, each with
    a reason. It is not a way out of the required set: an entry must be in `notDone` of
    ZlibF/Results.lean, in no manifest group and named by no api."""
    entries = manifest.get("not_planned", [])
    if not isinstance(entries, list):
        raise Rejected("not_planned must be a list")
    _, not_done = results()
    grouped = set(required_public_goals(manifest)) | set(manifest.get("sequence_goals", [])) | \
        set(manifest.get("nonvacuity_goals", [])) | set(manifest.get("safety_goals", []))
    named = {a.get(k) for a in manifest["apis"] for k in ("functional_goal", "safety_goal")}
    seen = set()
    for entry in entries:
        if not isinstance(entry, dict) or set(entry) != {"goal", "reason"} or \
                not isinstance(entry["goal"], str) or not isinstance(entry["reason"], str) or not entry["reason"].strip():
            raise Rejected(f"not_planned entries need a goal and a reason: {entry}")
        goal = entry["goal"]
        if goal in seen:
            raise Rejected(f"duplicate not_planned entry: {goal}")
        seen.add(goal)
        if goal not in not_done:
            raise Rejected(f"not_planned goal is not listed as not done in {RESULTS}: {goal}")
        if goal in grouped or goal in named:
            raise Rejected(f"not_planned goal is required, grouped or named by an api: {goal}")


def check_open_safety(manifest: dict) -> None:
    """`open_safety` names required goals that have no registered theorem yet, each with an owner."""
    entries = manifest.get("open_safety")
    if not isinstance(entries, list):
        raise Rejected("open_safety must be a list")
    required = set(required_public_goals(manifest))
    names = []
    for entry in entries:
        if not isinstance(entry, dict) or set(entry) != {"goal", "owner"} or \
                not isinstance(entry["owner"], str) or not entry["owner"].strip():
            raise Rejected(f"open_safety entries need a goal and an owner: {entry}")
        if entry["goal"] not in required:
            raise Rejected(f"open_safety names a goal that is not required: {entry['goal']}")
        names.append(entry["goal"])
    if len(names) != len(set(names)):
        raise Rejected("duplicate open_safety entry")


def check_required_proved(manifest: dict) -> None:
    """Every required goal that is not listed as open is proved, and no listed goal is proved."""
    proved, _ = results()
    opened = set(open_safety(manifest))
    missing = [g for g in required_public_goals(manifest) if g not in proved and g not in opened]
    if missing:
        raise Rejected("required goals without a theorem in ZlibF/Results.lean and not listed in open_safety: " +
                       ", ".join(missing))
    listed_proved = sorted(opened & set(proved))
    if listed_proved:
        raise Rejected("open_safety lists proved goals; remove them: " + ", ".join(listed_proved))


def check_imports() -> None:
    seen: set[Path] = set()

    def visit(path: Path):
        if path in seen:
            return
        seen.add(path)
        for line in path.read_text().splitlines():
            if not line.startswith("import "):
                continue
            # A quoted component may contain dots, as in «inflate.c».
            for name in line[7:].split("--", 1)[0].split():
                local = name == "ZlibF" or name.startswith("ZlibF.")
                standard = any(name == p or name.startswith(p + ".") for p in ("Init", "Std", "Lean"))
                if not local and not standard:
                    raise Rejected(f"unapproved external module: {name}")
                parts = re.findall(r"«[^»]+»|[^.]+", name)
                child = ROOT / ("/".join(p.strip("«»") for p in parts) + ".lean")
                if child.is_file():
                    if not local:
                        raise Rejected(f"local source shadows a pinned standard module: {name}")
                    visit(child)
                elif name == "ZlibF" or name.startswith("ZlibF."):
                    raise Rejected(f"import has no source (a stale object could hide it): {name}")

    visit(ROOT / "ZlibF.lean")
    visit(ROOT / "ZlibF/Results.lean")
    missing = set((ROOT / "ZlibF").rglob("*.lean")) - seen
    if missing:
        raise Rejected("modules outside the audited import closure: " +
                       ", ".join(str(p.relative_to(ROOT)) for p in sorted(missing)))


def coverage() -> dict:
    lake_manifest = ROOT / "lake-manifest.json"
    if lake_manifest.is_file():
        expected = {"version": "1.3.0", "packagesDir": ".lake/packages", "packages": [],
                    "name": "ZlibF", "lakeDir": ".lake", "fixedToolchain": False}
        if json.loads(lake_manifest.read_text()) != expected:
            raise Rejected("unapproved package manifest; dependencies need a reviewed policy update")
    manifest = json.loads((ROOT / MANIFEST).read_text())
    if manifest.get("version") != 1:
        raise Rejected("unknown public contract manifest version")
    expected_properties = {"documented-domain", "total-execution", "functional-result", "frame", "ownership"}
    if set(manifest.get("required_properties", [])) != expected_properties:
        raise Rejected("public contract properties are incomplete")
    apis = manifest["apis"]
    names = [a["function"] for a in apis]
    header = (ROOT / "zlib/zlib.h").read_text()
    exports = public_names(header)
    if len(names) != len(set(names)) or set(names) != exports:
        raise Rejected(f"public API coverage differs: missing={sorted(exports - set(names))}, "
                       f"extra={sorted(set(names) - exports)}")
    undocumented = manifest.get("undocumented")
    listed = undocumented.get("functions", []) if isinstance(undocumented, dict) else []
    if not isinstance(undocumented, dict) or undocumented.get("header_comment") != UNDOCUMENTED_MARK or \
            not undocumented.get("reason") or len(listed) != len(set(listed)) or \
            set(listed) != undocumented_names(header):
        raise Rejected(f"undocumented functions differ from zlib.h: listed={sorted(listed)}, "
                       f"declared={sorted(undocumented_names(header))}")
    pin = subprocess.check_output(["git", "-C", "zlib", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    index = subprocess.check_output(["git", "ls-files", "-s", "zlib"], cwd=ROOT, text=True).split()
    if len(index) < 2 or index[0] != "160000":
        raise Rejected("zlib must be a pinned submodule")
    if pin != manifest["source_pin"] or pin != index[1]:
        raise Rejected("the manifest, submodule checkout and source pin disagree")
    dirty_source = subprocess.check_output(
        ["git", "-C", "zlib", "status", "--porcelain", "--untracked-files=all"], cwd=ROOT, text=True)
    if dirty_source:
        raise Rejected("the pinned source submodule has local changes")
    goals = []
    for api in apis:
        manual, anchor = api["manual"].split("#", 1)
        for relative in (manual, api.get("source", manual)):
            path = Path(relative)
            if path.is_absolute() or ".." in path.parts or (ROOT / path).is_symlink():
                raise Rejected("public inventory paths must be ordinary repository files")
        if not re.search(r"^##\s+`?" + re.escape(api["function"]) + r"`?\s*$",
                         (ROOT / manual).read_text(), re.M) or anchor != api["function"].lower():
            raise Rejected(f"missing function contract documentation: {api['function']}")
        if api["scope"] != "lp64-linux":
            if api["function"] != "gzopen_w" or api["scope"] != "windows" or not api.get("reason"):
                raise Rejected(f"unreviewed scope exclusion: {api['function']}")
            continue
        src = (ROOT / api["source"]).read_text()
        if not re.search(r"^def\s+«?" + re.escape(api["function"]) + r"»?(?:\s|:)", src, re.M):
            raise Rejected(f"missing translated entry: {api['function']}")
        namespace = re.search(r"^namespace\s+(\S+)", src, re.M)
        if not namespace or api["implementation"] != namespace[1] + "." + api["function"]:
            raise Rejected(f"wrong translated entry binding: {api['function']}")
        if api["functional_goal"] != "ZlibF.Spec.Public.Goal." + api["function"]:
            raise Rejected(f"wrong public contract target: {api['function']}")
        goals.append(api["functional_goal"])
        check_api_safety_goal(api, api["function"] in listed, manifest.get("safety_goals", []))
    groups = {
        "sequence_goals": ["inflate_sequence", "deflate_sequence", "inflate_back_sequence", "gz_sequence"],
        "nonvacuity_goals": ["inflate_initialisation_domain", "deflate_initialisation_domain",
                              "inflate_back_initialisation_domain", "inflateBack_call_domain",
                              "gz_sequence_nonvacuity"],
        "safety_goals": ["inflate_sequence_safety", "deflate_sequence_safety", "uncompress_safe", "uncompress_z_safe", "uncompress2_safe", "uncompress2_z_safe", "compress_safety", "compress_z_safety", "compress2_safety", "compress2_z_safety",
                         "inflate_back_sequence_safety", "deflateCopy_safety",
                         "inflate_refusal", "deflate_refusal", "gz_sequence_safety", "gz_refusal",
                         "inflate_safety", "inflateSetDictionary_safety", "inflateGetDictionary_safety", "inflateSync_safety",
                         "inflateReset_safety", "inflateReset2_safety", "inflatePrime_safety", "inflateMark_safety",
                         "inflateGetHeader_safety", "deflate_safety", "deflateSetDictionary_safety", "deflateGetDictionary_safety",
                         "deflateReset_safety", "deflateParams_safety", "deflateTune_safety", "deflateBound_safety",
                         "deflateBound_z_safety", "deflatePending_safety", "deflateUsed_safety", "deflatePrime_safety",
                         "deflateSetHeader_safety", "inflateEnd_safety", "deflateEnd_safety", "inflateInit2__safety",
                         "inflateInit__safety", "deflateInit2__safety", "deflateInit__safety", "inflateCopy_safety",
                         "adler32_safety", "adler32_z_safety", "adler32_combine_safety", "adler32_combine64_safety",
                         "crc32_safety", "crc32_z_safety", "crc32_combine_gen_safety", "crc32_combine_gen64_safety",
                         "crc32_combine_op_safety", "crc32_combine_safety", "crc32_combine64_safety", "zlibVersion_safety",
                         "zlibCompileFlags_safety",
                         "gzbuffer_safety", "gzclearerr_safety", "gzclose_safety", "gzclose_r_safety",
                         "gzclose_w_safety", "gzdirect_safety", "gzdopen_safety", "gzeof_safety",
                         "gzerror_safety", "gzflush_safety", "gzfread_safety", "gzfwrite_safety",
                         "gzgetc_safety", "gzgetc__safety", "gzgets_safety", "gzoffset_safety",
                         "gzoffset64_safety", "gzopen_safety", "gzopen64_safety", "gzprintf_safety",
                         "gzputc_safety", "gzputs_safety", "gzread_safety", "gzrewind_safety",
                         "gzseek_safety", "gzseek64_safety", "gzsetparams_safety", "gztell_safety",
                         "gztell64_safety", "gzungetc_safety", "gzvprintf_safety", "gzwrite_safety", "inflateBack_safety",
                         "inflateBackEnd_safety", "inflateBackInit__safety"],
    }
    for group, suffixes in groups.items():
        expected = ["ZlibF.Spec.Public.Goal." + suffix for suffix in suffixes]
        if manifest.get(group) != expected:
            raise Rejected(f"missing {group}")
        goals.extend(manifest[group])
    if len(goals) != len(set(goals)):
        raise Rejected("public contracts must have distinct targets")
    check_safety_binding(manifest)
    check_open_safety(manifest)
    check_not_planned(manifest)
    check_imports()
    run([sys.executable, "scripts/gen_public_calls.py", "--check"])
    print(f"coverage: {len(exports)} public declarations, "
          f"{len(goals) - len(manifest['sequence_goals']) - len(manifest['nonvacuity_goals']) - len(manifest['safety_goals'])} default-build entries "
          f"({len([a for a in apis if a['scope'] == 'lp64-linux' and a['function'] not in listed])} documented, "
          f"the rest undocumented in zlib.h), "
          f"{len(manifest['sequence_goals'])} sequence targets, {len(manifest['nonvacuity_goals'])} non-vacuity targets, "
          f"{len(manifest['safety_goals'])} safety targets; "
          f"{len(required_public_goals(manifest))} required goals, {len(open_safety(manifest))} open")
    return manifest


def check_safety_binding(manifest: dict) -> None:
    """Each documented function names exactly one safety goal, fixed by the script:
    - its own Goal.<function>_safety (or _safe) when that goal is in the pinned safety_goals;
    - else its full contract, only for the functions of FULL_CONTRACT_SAFETY;
    - else a shared goal of SHARED_SAFETY_GOALS that lists it, named by exactly its pinned functions.
    So no manifest edit can move a function off its own goal."""
    hidden = set(manifest.get("undocumented", {}).get("functions", []))
    pinned = set(manifest.get("safety_goals", []))
    sharing: dict[str, list[str]] = {}
    for api in manifest["apis"]:
        if api["scope"] != "lp64-linux" or api["function"] in hidden:
            continue
        function, safety = api["function"], api.get("safety_goal")
        own = [g for g in ("ZlibF.Spec.Public.Goal." + function + suffix for suffix in ("_safety", "_safe"))
               if g in pinned]
        shared = [g for g, functions in SHARED_SAFETY_GOALS.items() if function in functions]
        if own:
            if len(own) != 1 or safety != own[0]:
                raise Rejected(f"safety goal of {function} is not its own goal {own[0]}: {safety}")
        elif function in FULL_CONTRACT_SAFETY:
            if safety != api["functional_goal"] or not api.get("safety_note"):
                raise Rejected(f"{function} must name its full contract with a safety_note: {safety}")
        elif shared:
            if safety != shared[0]:
                raise Rejected(f"safety goal of {function} is not its pinned shared goal {shared[0]}: {safety}")
            sharing.setdefault(safety, []).append(function)
        else:
            raise Rejected(f"{function} has no own safety goal, no pinned full contract and no shared goal")
    for goal, functions in SHARED_SAFETY_GOALS.items():
        if sorted(sharing.get(goal, [])) != sorted(functions):
            raise Rejected(f"shared safety goal {goal} is named by {sorted(sharing.get(goal, []))}, "
                           f"not by its pinned functions")


def main() -> int:
    argparse.ArgumentParser(description=__doc__).parse_args()
    try:
        manifest = coverage()
        check_required_proved(manifest)
        print("coverage passed")
        return 0
    except (Rejected, OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f"REJECTED: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())

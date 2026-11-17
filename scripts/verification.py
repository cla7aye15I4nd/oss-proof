#!/usr/bin/env python3
"""Check coverage, the declaration audit and final acceptance separately."""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
AUDITOR_ROOT = ROOT
MANIFEST = Path("tests/audit/public-api.json")
THEOREMS = Path("tests/audit/theorems.txt")
PROVED_GOALS = Path("tests/audit/proved-goals.txt")
REMOVALS = Path("tests/audit/registry-removals.json")
# The open list at the commit that introduced it: the floor while the base branch has no open list.
OPEN_SAFETY_FLOOR = "ec860375"
# The shrink-only checks compare every commit after these (dev at bd2afafd; main at 364790f5, whose
# squash commits have no dev ancestry). Each run needs at least one of them as an ancestor of HEAD.
CHAIN_FLOORS = ("bd2afafdc764914528953edfa148d6b18fdfada8", "364790f5f0cea98e6897be37a8aeaa0515cc1fec")
# The functions that name their full contract as safety goal (with a safety_note): pure functions with
# no own Goal.<function>_safety. No other function may.
FULL_CONTRACT_SAFETY = ("compressBound", "compressBound_z")
# The safety goals that several functions share, each with exactly the functions that name it. Empty
# since step 4 gave the gz and inflateBack functions their own goals: every documented function names
# its own Goal.<function>_safety (or _safe), or is listed in FULL_CONTRACT_SAFETY.
SHARED_SAFETY_GOALS: dict[str, list[str]] = {}


class Rejected(Exception):
    pass


def run(args: list[str], *, stdout=None) -> subprocess.CompletedProcess:
    return subprocess.run(args, cwd=ROOT, text=True, stdout=stdout, check=True)


def control_char(c: str) -> bool:
    """C0, DEL, C1 and U+2028/U+2029: the class of `isControlChar` in tests/audit/Audit.lean."""
    n = ord(c)
    return n < 32 or n == 127 or 0x80 <= n <= 0x9F or n in (0x2028, 0x2029)


# Whitespace that may not occur in a registry name: the list of `isRegistrySpace` in Audit.lean.
SPACES = {0x20, 0xA0, 0x1680, *range(0x2000, 0x200B), 0x202F, 0x205F, 0x3000, 0xFEFF}


def registry_lines(text: str, label: str) -> list[str]:
    """The registry line rule, shared with the auditor's `registryLines`: lines are separated by
    "\n" only; an empty line or a line that starts with "#" is skipped; no line holds a control
    character, and a name line holds no whitespace either. A line that breaks the rule is rejected,
    never repaired, so both readers see the same names."""
    names = []
    for line in text.split("\n"):
        if any(control_char(c) for c in line):
            raise Rejected(f"{label}: line breaks the registry rule: {line!r}")
        if line == "" or line.startswith("#"):
            continue
        if any(ord(c) in SPACES for c in line):
            raise Rejected(f"{label}: line breaks the registry rule: {line!r}")
        names.append(line)
    return names


def raw_text(path: Path) -> str:
    """The file's text with no newline translation (read_text() would turn "\r" into a line break)."""
    return path.read_bytes().decode("utf-8")


def read_names(path: Path) -> list[str]:
    if not path.is_file() or path.is_symlink():
        raise Rejected(f"missing registry: {path}")
    names = registry_lines(raw_text(path), str(path))
    if not names or len(names) != len(set(names)):
        raise Rejected(f"empty or duplicate registry: {path}")
    return names


def public_names(header: str) -> set[str]:
    header = re.sub(r"/\*.*?\*/", "", header, flags=re.S)
    return set(re.findall(r"ZEXTERN\s+[^;]*?\bZEXPORT(?:VA)?\s+(\w+)\s*\(", header, re.S))


UNDOCUMENTED_MARK = "/* undocumented functions (not part of the zlib API) */"


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
    """`not_planned` names public goals that stay defined and registered in goals.txt as open
    targets but are not planned, each with a reason. It is not a way out of the required set: the
    pinned groups of coverage() decide what is required. An entry must be a goal of goals.txt with a
    definition, in no manifest group and named by no api, and not proved (a proved entry is stale)."""
    entries = manifest.get("not_planned", [])
    if not isinstance(entries, list):
        raise Rejected("not_planned must be a list")
    goals = set(read_names(ROOT / "tests/audit/goals.txt"))
    proved = set(proved_goals())
    grouped = set(required_public_goals(manifest)) | set(manifest.get("sequence_goals", [])) | \
        set(manifest.get("nonvacuity_goals", [])) | set(manifest.get("safety_goals", []))
    named = {a.get(k) for a in manifest["apis"] for k in ("functional_goal", "safety_goal")}
    sources = [path.read_text() for path in (ROOT / "ZlibF/Spec").rglob("*.lean")]
    seen = set()
    for entry in entries:
        if not isinstance(entry, dict) or set(entry) != {"goal", "reason"} or \
                not isinstance(entry["goal"], str) or not isinstance(entry["reason"], str) or not entry["reason"].strip():
            raise Rejected(f"not_planned entries need a goal and a reason: {entry}")
        goal = entry["goal"]
        if goal in seen:
            raise Rejected(f"duplicate not_planned entry: {goal}")
        seen.add(goal)
        if goal not in goals:
            raise Rejected(f"not_planned goal is not in tests/audit/goals.txt: {goal}")
        leaf = goal.rsplit(".", 1)[-1]
        if not any(re.search(r"^def\s+Goal\." + re.escape(leaf) + r"\s*:", text, re.M) for text in sources):
            raise Rejected(f"not_planned goal has no definition under ZlibF/Spec: {goal}")
        if goal in grouped or goal in named:
            raise Rejected(f"not_planned goal is required, grouped or named by an api: {goal}")
        if goal in proved:
            raise Rejected(f"stale not_planned entry, the goal is proved: {goal}")


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


def base_revision() -> str:
    """The base branch the open list is compared with: ZLIBF_BASE_REF, else the pull request's
    base branch, else origin/main. When that is this very commit (a run on main), its first parent."""
    ref = os.environ.get("ZLIBF_BASE_REF") or \
        ("origin/" + os.environ["GITHUB_BASE_REF"] if os.environ.get("GITHUB_BASE_REF") else "origin/main")
    try:
        base = subprocess.check_output(["git", "rev-parse", "--verify", ref + "^{commit}"],
                                       cwd=ROOT, text=True, stderr=subprocess.DEVNULL).strip()
        head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        if base == head:
            base = subprocess.check_output(["git", "rev-parse", "--verify", "HEAD^"],
                                           cwd=ROOT, text=True, stderr=subprocess.DEVNULL).strip()
    except subprocess.CalledProcessError:
        raise Rejected(f"base branch {ref} is not available: fetch it, or set ZLIBF_BASE_REF")
    return base


def show(revision: str, path: Path) -> str | None:
    """A file at a revision, without newline translation; None when it is absent."""
    try:
        data = subprocess.check_output(["git", "show", f"{revision}:{path.as_posix()}"], cwd=ROOT,
                                       stderr=subprocess.DEVNULL)
    except subprocess.CalledProcessError:
        return None
    return data.decode("utf-8")


def revision_chain() -> list[str]:
    """The revisions the shrink-only checks compare with: the base, the pinned floors that are
    ancestors of HEAD, and every commit after them that HEAD contains (all parents, not only the
    first, so no merge can hide what came before it). At least one floor must be an ancestor of
    HEAD, or the check rejects: HEAD cannot drop the history these checks read. CHAIN_FLOORS moves
    forward only by an edit to this script."""
    base = base_revision()
    floors = []
    for floor in CHAIN_FLOORS:
        if subprocess.run(["git", "cat-file", "-e", floor + "^{commit}"], cwd=ROOT,
                          stderr=subprocess.DEVNULL).returncode != 0:
            raise Rejected(f"chain floor {floor[:12]} is not available: fetch the full history")
        if subprocess.run(["git", "merge-base", "--is-ancestor", floor, "HEAD"], cwd=ROOT).returncode == 0:
            floors.append(floor)
    if not floors:
        raise Rejected("no chain floor is an ancestor of HEAD: " + ", ".join(f[:12] for f in CHAIN_FLOORS))
    commits = subprocess.check_output(["git", "rev-list", "--reverse", "HEAD", "--not", *CHAIN_FLOORS],
                                      cwd=ROOT, text=True).split()
    return list(dict.fromkeys([base] + floors + commits))


def check_open_safety_shrinks(manifest: dict) -> None:
    """The open list only shrinks: a required goal that is not open at the base or at any
    first-parent commit since may not be open now. A goal new to the required set may enter it."""
    chain = revision_chain()
    closed: dict[str, str] = {}
    seen = 0
    for revision in chain:
        text = show(revision, MANIFEST)
        previous = json.loads(text) if text is not None else None
        if previous is None or "open_safety" not in previous:
            continue
        seen += 1
        for goal in set(required_public_goals(previous)) - set(open_safety(previous)):
            closed.setdefault(goal, revision)
    if not show(chain[0], MANIFEST) or "open_safety" not in json.loads(show(chain[0], MANIFEST)):
        # The base predates the open list: compare with the list where it was introduced.
        text = show(OPEN_SAFETY_FLOOR, MANIFEST)
        if text is None:
            raise Rejected(f"the open_safety floor {OPEN_SAFETY_FLOOR} is not available: fetch it")
        floor = json.loads(text)
        for goal in set(required_public_goals(floor)) - set(open_safety(floor)):
            closed.setdefault(goal, OPEN_SAFETY_FLOOR)
        print(f"open_safety: base {chain[0][:12]} predates the open list; floor {OPEN_SAFETY_FLOOR}")
    reopened = sorted(g for g in open_safety(manifest) if g in closed)
    if reopened:
        raise Rejected("open_safety grew: required goals closed before are open again: " +
                       ", ".join(f"{g} (closed at {closed[g][:12]})" for g in reopened))
    print(f"open_safety: {len(open_safety(manifest))} open; {len(chain)} revisions compared, "
          f"{seen} with an open list")


def proved_goals() -> list[str]:
    """The goals with a registered theorem of exactly their type. The auditor's `--proved` check
    rejects any difference from the PROVED set it computes, so this file can be trusted alone."""
    path = ROOT / PROVED_GOALS
    if not path.is_file() or path.is_symlink():
        raise Rejected(f"missing registry: {PROVED_GOALS}")
    names = registry_lines(raw_text(path), str(PROVED_GOALS))
    if len(names) != len(set(names)):
        raise Rejected(f"duplicate entry in {PROVED_GOALS}")
    return names


def removals() -> dict[str, set]:
    """Reviewed removals: a registered theorem or a recorded proved goal that may disappear."""
    path = ROOT / REMOVALS
    data = json.loads(raw_text(path)) if path.is_file() else {"version": 1, "theorems": [], "proved_goals": []}
    if set(data) != {"version", "theorems", "proved_goals"} or data["version"] != 1:
        raise Rejected(f"unknown {REMOVALS}")
    result: dict[str, set] = {}
    for key in ("theorems", "proved_goals"):
        names = set()
        for entry in data[key]:
            if not isinstance(entry, dict) or set(entry) != {"name", "reason"} or \
                    not isinstance(entry["name"], str) or not isinstance(entry["reason"], str) or \
                    not entry["reason"].strip() or registry_lines(entry["name"], str(REMOVALS)) != [entry["name"]]:
                raise Rejected(f"{REMOVALS} entries need one name and a reason: {entry}")
            names.add(entry["name"])
        result[key] = names
    return result


def check_registries_shrink() -> None:
    """No name registered in theorems.txt or recorded in proved-goals.txt at the base or at any
    first-parent commit since disappears, unless tests/audit/registry-removals.json names it with a
    reason. So a goal proved once cannot become open, required or not. A removal entry whose name
    was never registered on that chain, or is registered now, is stale and rejected."""
    chain = revision_chain()
    allowed = removals()
    for path, key, current in ((THEOREMS, "theorems", set(read_names(ROOT / THEOREMS))),
                               (PROVED_GOALS, "proved_goals", set(proved_goals()))):
        earlier: dict[str, str] = {}
        for revision in chain:
            text = show(revision, path)
            if text is None:
                continue
            for name in registry_lines(text, f"{revision[:12]}:{path}"):
                earlier.setdefault(name, revision)
        if show(chain[0], path) is None:
            print(f"{path}: base {chain[0][:12]} predates it; {len(chain)} revisions compared")
        stale = sorted(n for n in allowed[key] if n not in earlier or n in current)
        if stale:
            raise Rejected(f"stale entries in {REMOVALS} ({key}): " + ", ".join(stale))
        lost = sorted(set(earlier) - current - allowed[key])
        if lost:
            raise Rejected(f"names in {path} removed without a reviewed entry in {REMOVALS}: " +
                           ", ".join(f"{n} (registered at {earlier[n][:12]})" for n in lost))


def check_required_proved(manifest: dict) -> None:
    """Every required goal that is not listed as open is proved, and no listed goal is proved.
    Decided on tests/audit/proved-goals.txt, which the auditor checks to be exact."""
    proved = set(proved_goals())
    targets = set(read_names(ROOT / "tests/audit/goals.txt")) | set(required_public_goals(manifest)) | \
        set(functional_goals(manifest))
    unknown = sorted(proved - targets)
    if unknown:
        raise Rejected(f"{PROVED_GOALS} names what is not a goal: " + ", ".join(map(repr, unknown)))
    opened = set(open_safety(manifest))
    missing = [g for g in required_public_goals(manifest) if g not in proved and g not in opened]
    if missing:
        raise Rejected("required goals without a registered theorem and not listed in open_safety: " +
                       ", ".join(missing))
    listed_proved = sorted(opened & proved)
    if listed_proved:
        raise Rejected("open_safety lists proved goals; remove them: " + ", ".join(listed_proved))


def build_library() -> None:
    # Consumers must fail on a stale/missing artifact instead of silently doing
    # another full compile. Final acceptance retains its explicit clean build.
    flag = os.environ.get('ZLIBF_REQUIRE_PREBUILT', '0')
    if flag not in {'0', '1'}:
        raise Rejected('ZLIBF_REQUIRE_PREBUILT must be 0 or 1')
    run(['lake'] + (['--no-build'] if flag == '1' else []) + ['build', 'ZlibF'])


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


def build_auditor() -> Path:
    """Compile the invoking snapshot's auditor, never a candidate-supplied tool."""
    subprocess.run(["lake", "build", "zlibf-audit"], cwd=AUDITOR_ROOT, check=True)
    return AUDITOR_ROOT / ".lake/build/bin/zlibf-audit"


def audit(report: Path, *, strict: bool = False, public: bool = False) -> int:
    names = read_names(ROOT / "tests/audit/goals.txt")
    if public:
        manifest = coverage()
        listed = required_public_goals(manifest) + functional_goals(manifest)
        names += [name for name in listed if name not in names]
    with tempfile.TemporaryDirectory(prefix="verification-goals-") as directory:
        targets = Path(directory) / "goals.txt"
        targets.write_text("\n".join(names) + "\n")
        args = ["lake", "env", str(build_auditor()),
                "tests/audit/theorems.txt", str(targets)]
        if strict:
            args.append("--require-complete")
        # The auditor rejects any difference between this list and the goals it finds PROVED.
        args += ["--proved", str(ROOT / PROVED_GOALS)]
        if public:
            # The auditor itself decides that every required goal not listed as open is PROVED.
            required = Path(directory) / "required.txt"
            opened = set(open_safety(manifest))
            required.write_text("".join(g + "\n" for g in required_public_goals(manifest) if g not in opened))
            args += ["--require", str(required)]
        with report.open("w") as out:
            return subprocess.run(args, cwd=ROOT, text=True, stdout=out).returncode


def main() -> int:
    global ROOT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("coverage", "check", "specs", "final"))
    parser.add_argument("--report", type=Path)
    parser.add_argument("--root", type=Path, help="candidate checkout; the auditor remains the invoking snapshot")
    args = parser.parse_args()
    if args.root:
        ROOT = args.root.resolve()
    try:
        manifest = coverage()
        if args.mode == "coverage":
            print("coverage is not specification readiness or proof completion")
            return 0
        if args.mode == "final":
            if os.environ.get('ZLIBF_REQUIRE_PREBUILT', '0') != '0':
                raise Rejected('final acceptance requires a clean build')
            run(["lake", "clean"])
        build_library()
        # Recheck the compiled proof terms in a fresh kernel environment, not just the build trace.
        run(["lake", "env", "leanchecker", "--fresh", "ZlibF"])
        with tempfile.TemporaryDirectory(prefix="verification-report-") as directory:
            report = args.report or Path(directory) / "audit.txt"
            # The auditor's strict mode would reject every unproved goal, functional ones included.
            # Only the required goals are required: check_required_proved below.
            rc = audit(report, public=args.mode in ("specs", "final"))
            if rc:
                for line in report.read_text().splitlines():
                    if line.startswith(("goal ", "PROBLEM:")):
                        print(line)
                raise Rejected("audit rejected the requested verification stage")
            # Decided on the registries, never on the report text: the auditor has checked that
            # proved-goals.txt is exactly the set of PROVED goals.
            if args.mode in ("specs", "final"):
                check_required_proved(manifest)
                check_open_safety_shrinks(manifest)
                check_registries_shrink()
            if args.mode == "final" and open_safety(manifest):
                raise Rejected("final acceptance requires an empty open_safety: " +
                               ", ".join(open_safety(manifest)))
        if args.mode == "final":
            dirty = subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=normal"],
                                            cwd=ROOT, text=True)
            if dirty:
                raise Rejected("final acceptance requires a clean committed source tree")
            run(["bash", "scripts/check-sorry.sh"])
            run(["bash", "tests/audit/selftest.sh"])
            run(["env", f"ZLIB_SRC={ROOT / 'zlib'}", "bash", "tests/run.sh"])
            run(["env", "SAN=1", f"ZLIB_SRC={ROOT / 'zlib'}", "bash", "tests/run.sh"])
            run(["env", f"ZLIB_BUILD={ROOT / 'tests/build/zlib'}", "bash", "tests/selftest.sh"])
            commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
            print(f"final acceptance on commit: {commit}")
        print("stage passed: " + args.mode)
        if args.mode == "check":
            print("development audit only; public specification readiness and final proofs are separate gates")
        return 0
    except (Rejected, OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f"REJECTED: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())

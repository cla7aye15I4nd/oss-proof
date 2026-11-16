#!/usr/bin/env python3
"""Check coverage, the declaration audit, proof mutants and final acceptance separately."""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

import mutation_spans
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
# Proved per-function safety goals that have no function mutants of their own yet, each with its
# reason. The list may only shrink: an entry whose goal is unproved or has mutants is rejected.
MUTANT_COVERAGE_PENDING: dict[str, str] = {}
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
    that list, as Scope plans for gzvprintf, and keyed for function mutants like any own goal."""
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
    """Reviewed removals: a registered theorem, a recorded proved goal, or a mutant reference of a
    proved goal (goal, list, row name) that may disappear or change."""
    path = ROOT / REMOVALS
    data = json.loads(raw_text(path)) if path.is_file() else {"version": 1, "theorems": [], "proved_goals": []}
    if not {"version", "theorems", "proved_goals"} <= set(data) <= \
            {"version", "theorems", "proved_goals", "mutant_references", "mutant_rows"} or data["version"] != 1:
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
    references = set()
    for entry in data.get("mutant_references", []):
        if not isinstance(entry, dict) or set(entry) != {"goal", "list", "name", "reason"} or \
                not all(isinstance(entry[k], str) and entry[k].strip() for k in entry):
            raise Rejected(f"{REMOVALS} mutant_references entries need a goal, a list, a name and a reason: {entry}")
        references.add((entry["goal"], entry["list"], entry["name"]))
    result["mutant_references"] = references
    rows = set()
    for entry in data.get("mutant_rows", []):
        if not isinstance(entry, dict) or set(entry) != {"list", "name", "reason"} or \
                not all(isinstance(entry[k], str) and entry[k].strip() for k in entry):
            raise Rejected(f"{REMOVALS} mutant_rows entries need a list, a name and a reason: {entry}")
        rows.add((entry["list"], entry["name"]))
    result["mutant_rows"] = rows
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


def pending_waivers(text: str | None) -> dict | None:
    """MUTANT_COVERAGE_PENDING as written in a version of this script; None when it has none."""
    if text is None:
        return None
    for node in ast.parse(text).body:
        target = node.target if isinstance(node, ast.AnnAssign) else \
            (node.targets[0] if isinstance(node, ast.Assign) and len(node.targets) == 1 else None)
        if isinstance(target, ast.Name) and target.id == "MUTANT_COVERAGE_PENDING" and node.value is not None:
            return ast.literal_eval(node.value)
    return None


def check_waivers_shrink() -> None:
    """The mutant waivers only shrink: no entry is new against the base or any first-parent commit
    since that has the list."""
    for revision in revision_chain():
        earlier = pending_waivers(show(revision, Path("scripts/verification.py")))
        if earlier is None:
            continue
        added = sorted(set(MUTANT_COVERAGE_PENDING) - set(earlier))
        if added:
            raise Rejected(f"MUTANT_COVERAGE_PENDING grew against {revision[:12]}: " + ", ".join(added))


def mutant_identities(text_at, targets: dict, goals: set[str]) -> set[tuple]:
    """(goal, list, row name, file, old, new) of every reference of the given goals; text_at reads a list."""
    rows: dict[str, dict[str, tuple]] = {}
    found = set()
    for goal, references in targets.items():
        if goal not in goals or not isinstance(references, list):
            continue
        for reference in references:
            path = reference["list"]
            if path not in rows:
                rows[path] = {}
                for line in (text_at(path) or "").split("\n"):
                    if line and not line.startswith("#"):
                        fields = line.split("\t")
                        rows[path].setdefault(fields[0], tuple(fields[1:4]))
            found.add((goal, path, reference["name"]) + rows[path].get(reference["name"], ()))
    return found


def check_mutants_shrink() -> None:
    """While a goal is proved, its mutant references only shrink with a reviewed entry: no reference
    (list and row) of a proved goal at the base or a later commit of the chain disappears, and the
    referenced row (file, old and new text) does not change. So a committer cannot drop a goal's
    key, cut its rows to one, or swap a row for a weaker one without a reason in
    tests/audit/registry-removals.json. An entry that excuses nothing is stale and rejected."""
    proved = set(proved_goals())
    allowed = removals()["mutant_references"]
    path = Path("tests/audit/public-mutants.json")
    current = mutant_identities(lambda p: raw_text(ROOT / p) if (ROOT / p).is_file() else None,
                                json.loads(raw_text(ROOT / path))["targets"], proved)
    earlier: dict[tuple, str] = {}
    for revision in revision_chain():
        text = show(revision, path)
        if text is None:
            continue
        for identity in mutant_identities(lambda p: show(revision, Path(p)), json.loads(text)["targets"], proved):
            earlier.setdefault(identity, revision)
    missing = set(earlier) - current
    lost = sorted(i for i in missing if i[:3] not in allowed)
    if lost:
        raise Rejected("mutant references of proved goals removed or changed without a reviewed entry in "
                       f"{REMOVALS}: " + ", ".join(f"{i[0]}: {i[2]} (at {earlier[i][:12]})" for i in lost))
    stale = sorted(a for a in allowed if not any(i[:3] == a for i in missing))
    if stale:
        raise Rejected(f"stale mutant_references entries in {REMOVALS}: " + ", ".join(map(str, stale)))


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


def mutation_apis(manifest: dict) -> dict:
    """The public functions by the goal their mutants are replayed against.

    Each function is keyed by its functional goal from the public inventory, and also by its
    safety goal where that goal belongs to this function alone (not a sequence goal shared by
    several functions), so mutants of that function are checked against the proof of either.
    """
    lp64 = [a for a in manifest["apis"] if a["scope"] == "lp64-linux"]
    apis = {a["functional_goal"]: a for a in lp64}
    for a in lp64:
        if a.get("safety_goal") and a["safety_goal"] not in SHARED_SAFETY_GOALS:
            apis.setdefault(a["safety_goal"], a)
    return apis


def public_mutants(manifest: dict) -> dict:
    packet = json.loads((ROOT / "tests/audit/public-mutants.json").read_text())
    if set(packet) != {"version", "targets"} or packet["version"] != 1:
        raise Rejected("unknown public proof mutation manifest")
    apis = mutation_apis(manifest)
    targets = packet["targets"]
    if not isinstance(targets, dict) or set(targets) - set(apis):
        raise Rejected("unknown public mutation target")
    allowed = {"tests/audit/proofmut", "tests/proof-mutants", "tests/proofmut"}
    for goal, references in targets.items():
        if not isinstance(references, list) or not references:
            raise Rejected(f"no translation mutants for {goal}")
        api = apis[goal]
        source = (ROOT / api["source"]).read_text()
        start = re.search(r"^def\s+«?" + re.escape(api["function"]) + r"»?(?:\s|:)", source, re.M)
        if not start:
            raise Rejected(f"missing mutation entry: {api['function']}")
        following = re.search(r"^(?:def|theorem|abbrev|instance|structure|inductive|namespace|end)\b",
                              source[start.end():], re.M)
        end = start.end() + following.start() if following else len(source)
        body = source.find(":=", start.end(), end)
        if body < 0:
            raise Rejected(f"missing translated function body: {api['function']}")
        signature = source[start.start():body + 2]
        seen = set()
        for reference in references:
            if not isinstance(reference, dict) or set(reference) != {"list", "name"} or \
                    not isinstance(reference["name"], str) or not reference["name"]:
                raise Rejected(f"invalid mutation reference for {goal}")
            path = Path(reference["list"])
            key = (str(path), reference["name"])
            if str(path.parent) not in allowed or path.suffix != ".tsv" or key in seen:
                raise Rejected(f"invalid or duplicate mutation list for {goal}")
            seen.add(key)
            rows = [line.split("\t") for line in (ROOT / path).read_text().splitlines()
                    if line and not line.startswith("#")]
            matching = [row for row in rows if row[0] == reference["name"]]
            if len(matching) != 1 or not 5 <= len(matching[0]) <= 6:
                raise Rejected(f"missing or ambiguous mutation for {goal}: {key}")
            row = matching[0]
            old, new = row[2].replace("\\n", "\n"), row[3].replace("\\n", "\n")
            position = source.find(old)
            if row[1] != api["source"] or (len(row) == 6 and row[5]) or not row[4] or \
                    not old or old == new or source.count(old) != 1 or \
                    position < start.start() or position + len(old) > end or \
                    not source.replace(old, new).startswith(signature, start.start()):
                raise Rejected(f"mutation must change the actual function body without a gap: {goal}: {key}")
    return targets


def mutant_public_goals(manifest: dict) -> set[str]:
    """The goals of one function each: its functional goal and its own (unshared) safety goal."""
    return set(mutation_apis(manifest))


def check_public_mutant_coverage(manifest: dict, proved: set[str]) -> None:
    """Every proved goal of one public function has function mutants, except the listed pending ones."""
    targets = set(public_mutants(manifest))
    public = mutant_public_goals(manifest)
    for goal, reason in MUTANT_COVERAGE_PENDING.items():
        if not reason or goal not in public or goal not in proved or goal in targets:
            raise Rejected(f"stale mutant-coverage exemption, remove it: {goal}")
    missing = (proved & public) - targets - set(MUTANT_COVERAGE_PENDING)
    if missing:
        raise Rejected("proved public targets have no function mutants: " + ", ".join(sorted(missing)))


def source_module(path: str) -> str:
    return ".".join("«" + part + "»" for part in Path(path).with_suffix("").parts)


def check_public_mutant_spans(manifest: dict, selected: set[str] | None = None) -> None:
    """Parse both source commands without loading candidate imports or executing commands."""
    targets = public_mutants(manifest)
    apis = mutation_apis(manifest)
    for goal, references in targets.items():
        if selected is not None and goal not in selected:
            continue
        api = apis[goal]
        original = ROOT / api["source"]
        source = original.read_text()
        for reference in references:
            row = mutation_row(reference)
            with tempfile.TemporaryDirectory(prefix="public-mutation-syntax-") as directory:
                mutant = Path(directory) / "mutant.lean"
                mutant.write_text(source.replace(row[2].replace("\\n", "\n"),
                                                 row[3].replace("\\n", "\n")))
                try:
                    mutation_spans.check(original, mutant, api["function"])
                except (ValueError, subprocess.TimeoutExpired) as error:
                    raise Rejected(f"mutation is outside the parsed function body: {goal}: {error}") from error



REPLAY_RSS_LIMIT = int(os.environ.get("ZLIBF_REPLAY_RSS_MB", "12288")) * 2**20
REPLAY_WARN_RSS = 11 * 2**30


def group_rss(group: int) -> int:
    """Resident bytes of every process in a process group (Linux /proc; 0 elsewhere)."""
    total = 0
    for entry in Path("/proc").glob("[0-9]*"):
        try:
            fields = (entry / "stat").read_text().rsplit(")", 1)[1].split()
            if int(fields[2]) != group:
                continue
            for line in (entry / "status").read_text().splitlines():
                if line.startswith("VmRSS:"):
                    total += int(line.split()[1]) * 1024
        except (OSError, ValueError, IndexError):
            continue
    return total


def run_replay(args: list[str], what: str) -> subprocess.CompletedProcess:
    """Run one kernel replay in its own process group, within a resident-memory budget.

    A legitimate replay of the largest registered closure stays near 10.5 GB. A replay
    whose kernel work grows without bound is stopped at the budget and fails closed,
    so the stage stays inside the 16 GB build limit instead of meeting the
    out-of-memory killer (which may also hit unrelated processes).
    """
    process = subprocess.Popen(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, start_new_session=True)
    stdout, stderr, over, peak = "", "", False, 0
    while True:
        try:
            stdout, stderr = process.communicate(timeout=2)
            break
        except subprocess.TimeoutExpired:
            peak = max(peak, group_rss(process.pid))
            if peak > REPLAY_RSS_LIMIT:
                over = True
                os.killpg(process.pid, 9)
    if over:
        raise Rejected(f"replay over budget ({REPLAY_RSS_LIMIT >> 20} MB): {what}: move this row to a "
                       "source-level table if it edits a loop body or machine arithmetic "
                       "(docs/checking/proof-mutants.md)")
    result = subprocess.CompletedProcess(args, process.returncode, stdout, stderr)
    result.peak = peak
    return result


def report_peak(goal: str, peak: int) -> None:
    """Print the peak of a legitimate replay; warn when it nears the budget.

    The budget is not raised when closures grow: the fix is a smaller replay closure.
    """
    print(f"replay peak: {goal}: {peak >> 20} MB", flush=True)
    if peak > REPLAY_WARN_RSS:
        print(f"WARNING: legitimate replay of {goal} peaked at {peak >> 20} MB, above "
              f"{REPLAY_WARN_RSS >> 20} MB of the {REPLAY_RSS_LIMIT >> 20} MB budget", flush=True)


def mutation_row(reference: dict) -> list[str]:
    return next(line.split("\t") for line in (ROOT / reference["list"]).read_text().splitlines()
                if line and not line.startswith("#") and line.split("\t")[0] == reference["name"])


def copy_build_cache(source: Path, destination: Path) -> None:
    """Copy compiler artifacts, not unused native audit executables.

    The variant builds a translated module and replays through the original
    snapshot's absolute tool path. Copying its native tools into every variant
    adds large binaries that are never used. Keep all module traces and objects.
    """
    build = source.resolve() / 'build'
    shutil.copytree(source, destination, ignore=lambda path, names:
                    {'bin'} if Path(path).resolve() == build else set())


def replay_public_mutants(manifest: dict, selected: set[str] | None = None) -> None:
    """A failure in an unrelated or stronger theorem does not count."""
    targets = public_mutants(manifest)
    apis = mutation_apis(manifest)
    library = ROOT / ".lake/build/lib/lean"
    # Compile the unchanged replay program once. Each invocation still creates
    # a fresh kernel and checks the exact original registered proof closure.
    subprocess.run(['lake', 'build', 'zlibf-proof-replay'], cwd=AUDITOR_ROOT, check=True)
    replay = AUDITOR_ROOT / '.lake/build/bin/zlibf-proof-replay'
    registry = ROOT / "tests/audit/theorems.txt"
    for goal, references in targets.items():
        if selected is not None and goal not in selected:
            continue
        api = apis[goal]
        module = source_module(api["source"])
        command = ["lake", "env", str(replay), str(library)]
        control = run_replay(command + [str(library), module, goal, str(registry)], goal)
        sys.stdout.write(control.stdout)
        sys.stderr.write(control.stderr)
        if control.returncode != 0:
            raise Rejected(f"exact public proof does not replay: {goal}")
        report_peak(goal, control.peak)
        for reference in references:
            row = mutation_row(reference)
            with tempfile.TemporaryDirectory(prefix="public-proof-replay-") as directory:
                candidate = Path(directory)
                shutil.copytree(ROOT / "ZlibF", candidate / "ZlibF")
                for name in ("ZlibF.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"):
                    shutil.copyfile(ROOT / name, candidate / name)
                copy_build_cache(ROOT / ".lake", candidate / ".lake")
                path = candidate / api["source"]
                path.write_text(path.read_text().replace(row[2].replace("\\n", "\n"),
                                                        row[3].replace("\\n", "\n")))
                subprocess.run(["lake", "build", module], cwd=candidate, check=True,
                               text=True, stdout=subprocess.DEVNULL)
                result = run_replay(command + [str(candidate / ".lake/build/lib/lean"), module,
                                               goal, str(registry)], f"{goal}: {reference['name']}")
                if result.returncode != 2 or not result.stdout.startswith("EXACT_PROOF_REJECTED: "):
                    raise Rejected(f"original exact public proof survives or replay failed: {goal}: "
                                   f"{reference['name']}\n{result.stdout}{result.stderr}")
                print(f"exact public proof rejects: {goal}: {reference['name']}")


SAFETY_MUTANT_LISTS = ("tests/proof-mutants/deflate-header.tsv", "tests/proof-mutants/deflate-strategies.tsv",
                       "tests/proof-mutants/deflate-ops.tsv", "tests/proof-mutants/stream-refusal.tsv",
                       "tests/proof-mutants/infback-sequence.tsv", "tests/proof-mutants/gz-refusal.tsv",
                       "tests/proof-mutants/gz-sequence.tsv", "tests/proof-mutants/gz-read.tsv")


# The lists whose rows are frozen along the chain: the semantic safety lists and the API boundary list.
# They carry the only mutant evidence of the goals in PINNED_EVIDENCE. Rows may be added; a row may not
# change or go (all fields, and the sha256 of a script: row's mutator) without a reasoned mutant_rows
# entry in tests/audit/registry-removals.json.
def frozen_mutant_lists() -> tuple[str, ...]:
    return SAFETY_MUTANT_LISTS + ("tests/proof-mutants/api-boundary.tsv",)


P_GOAL = "ZlibF.Spec.Public.Goal."
# The mutant evidence of each proved required goal that has no key of its own in public-mutants.json:
# the frozen lists that carry it, each with the minimum number of rows that must be killed (rows not
# flagged same:), and the keyed goals whose replay also checks it (their proofs are corollaries of, or
# share the run lemmas of, this goal). Every pinned list must be a frozen list, so it is run in the shards.
PINNED_EVIDENCE: dict[str, dict] = {
    P_GOAL + "gz_sequence_safety": {"lists": {"tests/proof-mutants/gz-sequence.tsv": 43,
                                              "tests/proof-mutants/gz-read.tsv": 18}, "keys": []},
    P_GOAL + "inflate_back_sequence_safety": {"lists": {"tests/proof-mutants/infback-sequence.tsv": 11}, "keys": []},
    P_GOAL + "deflate_sequence_safety": {"lists": {"tests/proof-mutants/deflate-header.tsv": 5,
                                                   "tests/proof-mutants/deflate-strategies.tsv": 10,
                                                   "tests/proof-mutants/deflate-ops.tsv": 7},
                                         "keys": [P_GOAL + "deflate_safety", P_GOAL + "deflateEnd_safety"]},
    P_GOAL + "inflate_sequence_safety": {"lists": {}, "keys": [P_GOAL + "inflate_safety", P_GOAL + "inflateEnd_safety",
                                                               P_GOAL + "inflateCopy_safety"]},
    P_GOAL + "inflate_refusal": {"lists": {"tests/proof-mutants/stream-refusal.tsv": 5}, "keys": []},
    P_GOAL + "deflate_refusal": {"lists": {"tests/proof-mutants/stream-refusal.tsv": 5}, "keys": []},
    P_GOAL + "gz_refusal": {"lists": {"tests/proof-mutants/gz-refusal.tsv": 19}, "keys": []},
    P_GOAL + "inflate_initialisation_domain": {"lists": {}, "keys": [P_GOAL + "inflateInit2__safety"]},
    P_GOAL + "deflate_initialisation_domain": {"lists": {}, "keys": [P_GOAL + "deflateInit2__safety"]},
    P_GOAL + "inflate_back_initialisation_domain": {"lists": {"tests/proof-mutants/infback-sequence.tsv": 11},
                                                    "keys": [P_GOAL + "inflateBackInit_"]},
    P_GOAL + "gz_sequence_nonvacuity": {"lists": {"tests/proof-mutants/gz-sequence.tsv": 43},
                                        "keys": [P_GOAL + "gzdopen"]},
}


def killable_rows(text: str) -> list[list[str]]:
    rows = [line.split("\t") for line in text.split("\n") if line and not line.startswith("#")]
    return [row for row in rows if not (len(row) > 5 and row[5].startswith("same:"))]


def check_pinned_evidence(manifest: dict) -> None:
    """Every proved required goal has mutant evidence: its own key in public-mutants.json, or the
    pinned lists and keyed goals of PINNED_EVIDENCE, each list present with at least its pinned
    number of rows that must be killed, and each keyed goal keyed with at least one row."""
    proved = set(proved_goals())
    targets = json.loads(raw_text(ROOT / "tests/audit/public-mutants.json"))["targets"]
    frozen = set(frozen_mutant_lists())
    for goal in required_public_goals(manifest):
        if goal not in proved or targets.get(goal):
            continue
        pin = PINNED_EVIDENCE.get(goal)
        if pin is None:
            raise Rejected(f"proved required goal without a mutant key or pinned evidence: {goal}")
        if not pin["lists"] and not pin["keys"]:
            raise Rejected(f"pinned evidence of {goal} is empty")
        for path, minimum in pin["lists"].items():
            table = ROOT / path
            if path not in frozen or not table.is_file() or table.is_symlink():
                raise Rejected(f"pinned mutant list of {goal} is missing or not run in the shards: {path}")
            if len(killable_rows(raw_text(table))) < minimum:
                raise Rejected(f"pinned mutant list of {goal} has fewer than {minimum} rows to kill: {path}")
        for key in pin["keys"]:
            if not targets.get(key):
                raise Rejected(f"pinned mutant key of {goal} has no rows: {key}")


def show_bytes(revision: str, path: Path) -> bytes | None:
    try:
        return subprocess.check_output(["git", "show", f"{revision}:{path.as_posix()}"], cwd=ROOT,
                                       stderr=subprocess.DEVNULL)
    except subprocess.CalledProcessError:
        return None


def frozen_row_identities(read_text, read_bytes) -> set[tuple]:
    """(list, row name, the whole row, sha256 of the mutator of a script: row) of every frozen row."""
    found = set()
    for path in frozen_mutant_lists():
        text = read_text(path)
        if text is None:
            continue
        for line in text.split("\n"):
            if not line or line.startswith("#"):
                continue
            fields = line.split("\t")
            digest = ""
            if len(fields) > 1 and fields[1].startswith("script:"):
                data = read_bytes(fields[1][len("script:"):])
                digest = hashlib.sha256(data).hexdigest() if data is not None else "missing"
            found.add((path, fields[0], line, digest))
    return found


def check_frozen_mutant_rows() -> None:
    """No row of a frozen list at the base or a later commit of the chain disappears or changes
    (all fields, and the content of a script: row's mutator), unless registry-removals.json names
    the list and row under mutant_rows with a reason. An entry that excuses nothing is stale."""
    allowed = removals()["mutant_rows"]
    current = frozen_row_identities(lambda p: raw_text(ROOT / p) if (ROOT / p).is_file() else None,
                                    lambda p: (ROOT / p).read_bytes() if (ROOT / p).is_file() else None)
    earlier: dict[tuple, str] = {}
    for revision in revision_chain():
        for identity in frozen_row_identities(lambda p: show(revision, Path(p)),
                                              lambda p: show_bytes(revision, Path(p))):
            earlier.setdefault(identity, revision)
    missing = set(earlier) - current
    lost = sorted(i for i in missing if i[:2] not in allowed)
    if lost:
        raise Rejected("frozen mutant rows removed or changed without a reviewed entry in "
                       f"{REMOVALS}: " + ", ".join(f"{i[0]}: {i[1]} (at {earlier[i][:12]})" for i in lost))
    stale = sorted(a for a in allowed if not any(i[:2] == a for i in missing))
    if stale:
        raise Rejected(f"stale mutant_rows entries in {REMOVALS}: " + ", ".join(map(str, stale)))


def mutation_partition(manifest: dict, count: int = 1, index: int = 0) -> tuple[set[str], dict[str, list[str]]]:
    """Assign every goal bundle and every full proof-list row exactly once.

    A goal's unchanged exact-proof control travels with all its public mutants.
    Full proof lists also contain cases outside the public registry. Partition
    those rows independently so none are lost or concentrated in one worker.
    """
    if count <= 0 or not 0 <= index < count:
        raise Rejected('shard count must be positive and index must be in range')
    targets = public_mutants(manifest)
    goals = {goal for ordinal, goal in enumerate(sorted(targets)) if ordinal % count == index}
    lists = {reference["list"] for references in targets.values() for reference in references}
    lists.add("tests/proof-mutants/api-boundary.tsv")
    # The semantic mutants of the deflate safety proof: script rows that edit the translation and
    # every proof restatement of it, so they cannot key a public goal, but each must be killed in
    # its semantic lemma. The public mutants of Goal.deflate are only rejected at the phase
    # restatement, so these lists carry the semantic evidence: a missing or empty one is an error.
    for path in SAFETY_MUTANT_LISTS:
        table = ROOT / path
        if not table.is_file() or table.is_symlink() or not any(
                row and not row.startswith("#") for row in table.read_text().splitlines()):
            raise Rejected(f"missing or empty semantic mutant list: {path}")
        lists.add(path)
    selected = {}
    ordinal = 0
    for path in sorted(lists):
        # A row flagged same: (an equivalent mutant) is not evidence: proofmut.sh in strict mode needs a
        # KILLED row in every list it runs. So the killable rows are dealt round robin, and each same:
        # row goes to the shard of its list's first killable row. A list with no killable row is an error.
        all_rows = [row for row in (ROOT / path).read_text().splitlines() if row and not row.startswith('#')]
        killable = [row for row in all_rows if not (len(row.split('\t')) > 5 and row.split('\t')[5].startswith('same:'))]
        if not killable:
            raise Rejected(f"proof mutant list without a row that must be killed: {path}")
        first_shard = ordinal % count
        rows = []
        for row in all_rows:
            if row in killable:
                if ordinal % count == index:
                    rows.append(row)
                ordinal += 1
            elif first_shard == index:
                rows.append(row)
        if rows:
            selected[path] = rows
    if not goals and not selected:
        raise Rejected('empty proof mutation shard')
    return goals, selected


def run_public_mutants(manifest: dict, count: int = 1, index: int = 0) -> None:
    goals, lists = mutation_partition(manifest, count, index)
    check_public_mutant_spans(manifest, goals)
    replay_public_mutants(manifest, goals)
    with tempfile.TemporaryDirectory(prefix='proof-mutation-shard-') as directory:
        for ordinal, (path, rows) in enumerate(lists.items()):
            subset = Path(directory) / (str(ordinal) + '-' + Path(path).name)
            subset.write_text('\n'.join(rows) + '\n')
            print(f'proof mutation shard {index}/{count}: {path}: {len(rows)} cases', flush=True)
            run(["env", "PROOFMUT_STRICT=1", "bash", "tests/audit/proofmut.sh", str(subset)])


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
                              "inflate_back_initialisation_domain", "gz_sequence_nonvacuity"],
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
    public_mutants(manifest)
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
    So no manifest edit can move a function off its own goal and drop that goal from the mutant
    requirement while the goal stays required."""
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
    parser.add_argument("mode", choices=("coverage", "check", "specs", "mutants", "final"))
    parser.add_argument("--report", type=Path)
    parser.add_argument("--root", type=Path, help="candidate checkout; the auditor remains the invoking snapshot")
    parser.add_argument('--shard-count', type=int, default=1)
    parser.add_argument('--shard-index', type=int, default=0)
    args = parser.parse_args()
    if args.root:
        ROOT = args.root.resolve()
    try:
        if args.mode != 'mutants' and (args.shard_count, args.shard_index) != (1, 0):
            raise Rejected('sharding applies only to the mutants stage')
        manifest = coverage()
        if args.mode == "coverage":
            print("coverage is not specification readiness or proof completion")
            return 0
        if args.mode == "mutants":
            mutation_partition(manifest, args.shard_count, args.shard_index)
            build_library()
            run_public_mutants(manifest, args.shard_count, args.shard_index)
            print("stage passed: mutants")
            return 0
        if args.mode == "final":
            if os.environ.get('ZLIBF_REQUIRE_PREBUILT', '0') != '0':
                raise Rejected('final acceptance requires a clean build')
            run(["lake", "clean"])
        build_library()
        check_public_mutant_spans(manifest)
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
            check_public_mutant_coverage(manifest, set(proved_goals()))
            if args.mode in ("specs", "final"):
                check_required_proved(manifest)
                check_open_safety_shrinks(manifest)
                check_registries_shrink()
                check_waivers_shrink()
                check_mutants_shrink()
                check_frozen_mutant_rows()
                check_pinned_evidence(manifest)
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
            replay_public_mutants(manifest)
            run(["env", f"ZLIB_SRC={ROOT / 'zlib'}", "bash", "tests/run.sh"])
            run(["env", "SAN=1", f"ZLIB_SRC={ROOT / 'zlib'}", "bash", "tests/run.sh"])
            run(["env", f"ZLIB_BUILD={ROOT / 'tests/build/zlib'}", "bash", "tests/selftest.sh"])
            mutation_lists = sorted(path for directory in
                ("tests/audit/proofmut", "tests/proof-mutants", "tests/proofmut")
                for path in (ROOT / directory).glob("*.tsv"))
            if not mutation_lists:
                raise Rejected("final acceptance requires proof mutation lists")
            for mutations in mutation_lists:
                run(["env", "PROOFMUT_STRICT=1", "bash", "tests/audit/proofmut.sh",
                     str(mutations.relative_to(ROOT))])
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

"""Done or not done, for every goal and every public function.

A goal is done when a theorem whose type is exactly the goal is recorded for it. The records are
read here and nowhere else in the site; their file names never reach a page. They are read as text,
without Lean: the site is built without the compiled library.
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
import json
import re

REPO = Path(__file__).resolve().parents[2]
STATE = {True: ('完成', 'done'), False: ('未完成', 'not done')}
# Group of the status page, by the API manual that documents the function.
GROUPS = ('inflate-stream', 'deflate-stream', 'utility', 'checksums', 'inflate-back', 'gz-file')


@dataclass(frozen=True)
class Function:
    name: str
    group: str
    goal: str | None      # short name of the safety goal; None: no safety goal is stated
    done: bool
    documented: bool      # part of the zlib API, in the default build


@lru_cache(maxsize=1)
def manifest() -> dict:
    return json.loads((REPO / 'tests/audit/public-api.json').read_text())


class ResultsError(ValueError):
    """ZlibF/Results.lean could not be read as three lists that agree with each other."""

    def __init__(self, message: str):
        super().__init__('ZlibF/Results.lean: ' + message)


def strip_comments(text: str) -> str:
    """Lean source with its comments replaced by spaces; line breaks and string literals are kept.

    A line comment runs from `--` to the end of the line. A block comment runs from `/-` to its matching
    `-/`; block comments nest, and `/--` and `/-!` (doc comments) open one like any other. A `--` or `/-`
    inside a string literal opens nothing."""
    out, i, n = [], 0, len(text)
    while i < n:
        two = text[i:i + 2]
        if two == '--':
            end = text.find('\n', i)
            end = n if end == -1 else end
            out.append(' ' * (end - i))
            i = end
        elif two == '/-':
            depth, j = 1, i + 2
            while j < n and depth:
                if text[j:j + 2] == '/-':
                    depth, j = depth + 1, j + 2
                elif text[j:j + 2] == '-/':
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            if depth:
                raise ResultsError('a block comment is not closed')
            out.append(''.join('\n' if c == '\n' else ' ' for c in text[i:j]))
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            out.append(text[i:j + 1])
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)


@dataclass(frozen=True)
class Results:
    proved: tuple[tuple[str, str], ...]   # (goal, theorem), in the order of the module
    not_done: tuple[str, ...]
    required: tuple[str, ...]


NAME = r'``([^\s,()\[\]]+)'
LISTS = (('proved', r'List \(Name × Name\)', re.compile(r'\(\s*' + NAME + r'\s*,\s*' + NAME + r'\s*\)')),
         ('notDone', r'List Name', re.compile(NAME)),
         ('required', r'List Name', re.compile(NAME)))


def parse_results(text: str) -> Results:
    """The lists `proved`, `notDone` and `required` of the text of ZlibF/Results.lean.

    The text is read without Lean, so the reading is strict: comments are removed first, each list must be
    there once, be non-empty and hold nothing but its entries, no goal may be listed twice, and every
    required goal must be proved. Anything else raises `ResultsError`, which stops the site build."""
    code = strip_comments(text)
    found = {}
    for name, kind, entry in LISTS:
        heads = list(re.finditer(r'^def ' + name + r'\s*:\s*' + kind + r'\s*:=\s*\[', code, re.M))
        if len(heads) != 1:
            raise ResultsError(f'the list `{name}` is defined {len(heads)} times, not once')
        end = code.find(']', heads[0].end())
        if end == -1:
            raise ResultsError(f'the list `{name}` is not closed')
        body = code[heads[0].end():end]
        entries = [m.groups() if name == 'proved' else m.group(1) for m in entry.finditer(body)]
        rest = re.sub(r'[\s,]', '', entry.sub('', body))
        if rest:
            raise ResultsError(f'the list `{name}` holds text that is not an entry: {rest[:60]}')
        if not entries:
            raise ResultsError(f'the list `{name}` is empty')
        found[name] = tuple(entries)
    goals = [goal for goal, _ in found['proved']]
    listed = goals + list(found['notDone'])
    twice = sorted({goal for goal in listed if listed.count(goal) > 1})
    if twice:
        raise ResultsError('a goal is listed twice in `proved` and `notDone`: ' + ', '.join(twice))
    missing = [goal for goal in found['required'] if goal not in set(goals)]
    if missing:
        raise ResultsError('a required goal is not in `proved`: ' + ', '.join(missing))
    return Results(found['proved'], found['notDone'], found['required'])


@lru_cache(maxsize=1)
def results() -> Results:
    """The three lists of ZlibF/Results.lean, which Lean checks when the library is built. Every goal whose
    safety the public API manifest requires must be in `required` there."""
    lists = parse_results((REPO / 'ZlibF/Results.lean').read_text())
    data = manifest()
    hidden = set(data['undocumented']['functions'])
    wanted = [api['safety_goal'] for api in data['apis']
              if api.get('safety_goal') and api['scope'] == 'lp64-linux' and api['function'] not in hidden]
    wanted += data.get('safety_goals', []) + data.get('nonvacuity_goals', [])
    missing = [goal for goal in dict.fromkeys(wanted) if goal not in set(lists.required)]
    if missing:
        raise ResultsError('a safety goal of the public API is not in `required`: ' + ', '.join(missing))
    return lists


@lru_cache(maxsize=1)
def proved() -> frozenset[str]:
    """The goals of the list `proved` of ZlibF/Results.lean."""
    return frozenset(goal for goal, _ in results().proved)


def short(goal: str) -> str:
    return goal.rsplit('.', 1)[-1]


def goal_done(goal: str | None) -> bool:
    """`goal` is a full name, or the short name of a goal about a public function."""
    if not goal:
        return False
    return goal in proved() or 'ZlibF.Spec.Public.Goal.' + goal in proved()


def state(done: bool, lang: str) -> str:
    return STATE[done][lang == 'en']


def functional_state(done: bool, lang: str) -> str:
    """The state of the functional contract of one function. The only functional result, the
    round trip of the default stream, is not the contract of one function; so a functional
    contract that is not done is also not planned."""
    if done:
        return state(True, lang)
    return state(False, lang) + (', not planned' if lang == 'en' else '，不在计划内')


@lru_cache(maxsize=1)
def functions() -> tuple[Function, ...]:
    data = manifest()
    hidden = set(data['undocumented']['functions'])
    result = []
    for api in data['apis']:
        goal = api.get('safety_goal')
        result.append(Function(api['function'], Path(api['manual'].split('#')[0]).stem,
                               short(goal) if goal else None, goal_done(goal),
                               api['scope'] == 'lp64-linux' and api['function'] not in hidden))
    return tuple(result)


@lru_cache(maxsize=1)
def required_goals() -> tuple[str, ...]:
    """Short names of the goals of the three safety results: the safety goal of every documented
    function of the default build, the other safety goals, and the goals that show the premises
    can be met."""
    data = manifest()
    names = [f.goal for f in functions() if f.documented and f.goal]
    names += [short(g) for g in data.get('safety_goals', []) + data.get('nonvacuity_goals', [])]
    return tuple(dict.fromkeys(names))


@lru_cache(maxsize=1)
def roundtrip_goals() -> tuple[str, ...]:
    """Short names of the goals of the round trip of the default zlib stream, in the order of the
    status page: the goals of the list `required` of ZlibF/Results.lean that are not goals of the
    safety results, in the order of its list `proved`."""
    lists, safety = results(), set(required_goals())
    wanted = set(lists.required)
    return tuple(short(goal) for goal, _ in lists.proved if goal in wanted and short(goal) not in safety)


@lru_cache(maxsize=1)
def other_goals() -> tuple[str, ...]:
    """Required goals that are not the safety goal of one function."""
    own = {f.goal for f in functions()}
    return tuple(g for g in required_goals() if g not in own)


def page_rows(text: str) -> list[tuple[str, str, str]]:
    """The rows `| name | goal | state |` of the status page: (first cell, goal, state)."""
    rows = []
    for line in text.splitlines():
        cells = [cell.strip() for cell in line.strip().strip('|').split('|')]
        if not line.startswith('|') or len(cells) != 3:
            continue
        goal = re.fullmatch(r'`Goal\.(\w+)`', cells[1])
        if goal:
            rows.append((cells[0].strip('`'), goal[1], cells[2]))
    return rows

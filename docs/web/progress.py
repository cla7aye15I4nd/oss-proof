"""Done or not done, for every goal and every public function.

A goal is done when a theorem whose type is exactly the goal is recorded for it. The records are
read here and nowhere else in the site; their file names never reach a page.
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


@lru_cache(maxsize=1)
def proved() -> frozenset[str]:
    lines = (REPO / 'tests/audit/proved-goals.txt').read_text().splitlines()
    return frozenset(line.strip() for line in lines if line.strip() and not line.startswith('#'))


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
    """The state of the functional contract of one function. The only functional result that is
    planned, the round trip of the default stream, is not the contract of one function; so a
    functional contract that is not done is also not planned."""
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

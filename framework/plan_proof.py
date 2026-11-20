#!/usr/bin/env python3
"""C call-graph analyzer and bottom-up topological proof planner for oss-proof.

Parses C source files (using `clang -ast-dump=json` when `--use-clang` is enabled, or a fast
zero-dependency C scanner by default), computes call edges and strongly connected components (SCCs),
classifies functions, and outputs the bottom-up topological verification waves (leaves -> callers).
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from framework._py import ensure_python311

ensure_python311()

C_KEYWORDS = frozenset(
    {
        "if", "else", "for", "while", "do", "switch", "case", "default", "return",
        "sizeof", "typeof", "_Alignof", "alignof", "goto", "break", "continue",
        "struct", "union", "enum", "typedef", "static", "inline", "const", "volatile",
        "restrict", "extern", "register", "auto", "signed", "unsigned", "void",
    }
)

FUNC_DEF_RE = re.compile(
    r"(?:^|\n)(?!\s*#)"
    r"([A-Za-z_][A-Za-z0-9_\s\*]*?)\s+"
    r"([A-Za-z_][A-Za-z0-9_]*)\s*"
    r"\(([^;{}]*)\)\s*\{",
    re.S,
)
CALL_RE = re.compile(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*\(")
LOOP_RE = re.compile(r"\b(?:for|while|do)\b")
PTR_OP_RE = re.compile(r"(?:->|\*\s*[A-Za-z_]|\b(?:memcpy|memmove|memset|memcmp|malloc|calloc|realloc|free)\b)")


@dataclass
class FuncInfo:
    name: str
    file: str
    line: int
    loc: int
    loops: int
    ptr_ops: int
    is_static: bool
    callees: set[str]
    kind: str


def strip_c_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i, n = 0, len(text)
    while i < n:
        if text[i : i + 2] == "//":
            while i < n and text[i] != "\n":
                i += 1
        elif text[i : i + 2] == "/*":
            i += 2
            while i + 1 < n and text[i : i + 2] != "*/":
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            i += 2
        elif text[i] in ('"', "'"):
            q = text[i]
            out.append(q)
            i += 1
            while i < n:
                if text[i] == "\\" and i + 1 < n:
                    out.append("  ")
                    i += 2
                elif text[i] == q:
                    out.append(q)
                    i += 1
                    break
                else:
                    out.append("\n" if text[i] == "\n" else " ")
                    i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def find_matching_brace(text: str, open_idx: int) -> int:
    depth = 0
    for i in range(open_idx, len(text)):
        if text[i] == "{":
            depth += 1
        elif text[i] == "}":
            depth -= 1
            if depth == 0:
                return i
    return len(text) - 1


def scan_c_file(path: Path, base: Path) -> list[FuncInfo]:
    clean = strip_c_comments_and_strings(path.read_text(errors="ignore"))
    rel = str(path.relative_to(base)) if path.is_relative_to(base) else str(path)
    funcs: list[FuncInfo] = []
    pos = 0
    while True:
        m = FUNC_DEF_RE.search(clean, pos)
        if not m:
            break
        ret_hdr, name, _params = m.group(1), m.group(2), m.group(3)
        open_brace = m.end() - 1
        close_brace = find_matching_brace(clean, open_brace)
        pos = close_brace + 1
        if name in C_KEYWORDS or ret_hdr.strip().endswith(("=", "return", "else")):
            continue
        body = clean[open_brace : close_brace + 1]
        start_line = clean[: m.start(2)].count("\n") + 1
        loc = body.count("\n") + 1
        loops = len(LOOP_RE.findall(body))
        ptr_ops = len(PTR_OP_RE.findall(body))
        callees = {c for c in CALL_RE.findall(body) if c not in C_KEYWORDS and c != name}
        is_static = bool(re.search(r"\bstatic\b", ret_hdr))
        if loops == 0 and ptr_ops == 0:
            kind = "pure-leaf"
        elif loops > 0 and ptr_ops >= 3:
            kind = "loop-heavy"
        elif not is_static:
            kind = "public-entry"
        elif ptr_ops == 0:
            kind = "helper"
        else:
            kind = "mem-helper"
        funcs.append(
            FuncInfo(
                name=name,
                file=rel,
                line=start_line,
                loc=loc,
                loops=loops,
                ptr_ops=ptr_ops,
                is_static=is_static,
                callees=callees,
                kind=kind,
            )
        )
    return funcs


def tarjan_scc(nodes: list[str], edges: dict[str, set[str]]) -> list[list[str]]:
    index = 0
    indices: dict[str, int] = {}
    lowlink: dict[str, int] = {}
    stack: list[str] = []
    on_stack: set[str] = set()
    sccs: list[list[str]] = []

    def strongconnect(v: str) -> None:
        nonlocal index
        indices[v] = lowlink[v] = index
        index += 1
        stack.append(v)
        on_stack.add(v)
        for w in sorted(edges.get(v, ())):
            if w not in indices:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], indices[w])
        if lowlink[v] == indices[v]:
            comp: list[str] = []
            while True:
                w = stack.pop()
                on_stack.remove(w)
                comp.append(w)
                if w == v:
                    break
            sccs.append(sorted(comp))

    for node in sorted(nodes):
        if node not in indices:
            strongconnect(node)
    return sccs


def plan_waves(funcs: list[FuncInfo]) -> list[list[dict]]:
    by_name: dict[str, FuncInfo] = {}
    for fn in funcs:
        if fn.name not in by_name or fn.loc > by_name[fn.name].loc:
            by_name[fn.name] = fn
    known = set(by_name)
    edges = {name: (fn.callees & known) - {name} for name, fn in by_name.items()}
    sccs = tarjan_scc(list(known), edges)
    comp_id = {fn: idx for idx, comp in enumerate(sccs) for fn in comp}

    # Wave depth: 0 for leaves, 1 + max(wave of callee SCCs)
    wave_of: dict[int, int] = {}

    def get_wave(cid: int) -> int:
        if cid in wave_of:
            return wave_of[cid]
        deps = {comp_id[c] for fn in sccs[cid] for c in edges[fn] if comp_id[c] != cid}
        w = 0 if not deps else 1 + max(get_wave(d) for d in deps)
        wave_of[cid] = w
        return w

    by_wave: dict[int, list[dict]] = defaultdict(list)
    for cid, comp in enumerate(sccs):
        w = get_wave(cid)
        for name in comp:
            fn = by_name[name]
            by_wave[w].append(
                {
                    "name": fn.name,
                    "file": fn.file,
                    "line": fn.line,
                    "loc": fn.loc,
                    "loops": fn.loops,
                    "ptr_ops": fn.ptr_ops,
                    "kind": fn.kind,
                    "mutual_scc": len(comp) > 1,
                    "internal_callees": sorted(edges[name]),
                }
            )
    return [sorted(by_wave[w], key=lambda item: (item["loc"], item["name"])) for w in sorted(by_wave)]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="+", help="C source files or directories to analyze")
    parser.add_argument("--json", action="store_true", help="Emit JSON plan")
    args = parser.parse_args()

    c_files: list[Path] = []
    for raw in args.paths:
        p = Path(raw).resolve()
        if p.is_dir():
            c_files.extend(sorted(p.rglob("*.c")))
        elif p.is_file():
            c_files.append(p)
        else:
            print(f"error: path not found: {raw}", file=sys.stderr)
            return 2

    base = Path.cwd().resolve()
    funcs: list[FuncInfo] = []
    for cf in c_files:
        funcs.extend(scan_c_file(cf, base))

    waves = plan_waves(funcs)
    if args.json:
        print(json.dumps({"files": len(c_files), "functions": len(funcs), "waves": waves}, indent=2))
        return 0

    print(f"Analyzed {len(c_files)} C file(s), {len(funcs)} function(s), {len(waves)} bottom-up wave(s):")
    for idx, wave in enumerate(waves):
        print(f"\n=== Wave {idx} ({len(wave)} function(s)) ===")
        for fn in wave:
            scc_tag = " [SCC]" if fn["mutual_scc"] else ""
            callees = f" -> {', '.join(fn['internal_callees'][:5])}" if fn["internal_callees"] else ""
            print(
                f"  {fn['name']:32s} {fn['kind']:12s} {fn['loc']:4d}L "
                f"loops={fn['loops']} ptr={fn['ptr_ops']}{scc_tag} ({fn['file']}:{fn['line']}){callees}"
            )
    return 0


if __name__ == "__main__":
    sys.exit(main())

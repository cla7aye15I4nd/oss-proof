#!/usr/bin/env python3
"""Check specification layers for an oss-proof project.

Enforces:
1. Directly under `<Package>/Spec/` are only `Safety/`, `Functional/`, `Common/`, and optional root `.lean` files.
2. `Safety` and `Common` never import `Functional` (even transitively).
3. `Common` never imports `Safety` (even transitively).
4. `<Package>/Spec/` never imports `<Package>/Proof/` (even transitively).
5. `<Package>/Math/` never imports `<Package>/Proof/` except shrink-only `math_proof_imports`.
6. No `Goal.` definition or abbreviation lives under `<Package>/Spec/Common/`.
"""
from __future__ import annotations

import argparse
import importlib.util
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from framework.manifest import REPO, load_all_projects, load_project

LAYERS = ("Safety", "Functional", "Common")
COMPONENT = r"(?:«[^»\n]*»|[^\s.«»]+)"
MODULE = COMPONENT + r"(?:\." + COMPONENT + r")*"
IMPORT = re.compile(r"(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(" + MODULE + r")\s*(?:--.*)?$")
PLAIN = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*$")


def components(name: str) -> list[str]:
    if not re.fullmatch(MODULE, name):
        raise ValueError(f"not a module name: {name!r}")
    return [part[1:-1] if part.startswith("«") else part for part in re.findall(COMPONENT, name)]


def canonical(parts: list[str]) -> str:
    return ".".join(part if PLAIN.match(part) else f"«{part}»" for part in parts)


def plain(name: str) -> str:
    return canonical(components(name))


def header_imports(text: str) -> list[str]:
    found: list[str] = []
    depth = 0
    for line in text.splitlines():
        rest = line
        if depth == 0:
            match = IMPORT.match(line.strip())
            if match:
                found.append(match.group(1))
                continue
        code = ""
        while rest:
            if depth:
                close, open_ = rest.find("-/"), rest.find("/-")
                if open_ != -1 and (close == -1 or open_ < close):
                    depth, rest = depth + 1, rest[open_ + 2 :]
                elif close != -1:
                    depth, rest = depth - 1, rest[close + 2 :]
                else:
                    rest = ""
            else:
                open_, dash = rest.find("/-"), rest.find("--")
                if dash != -1 and (open_ == -1 or dash < open_):
                    code, rest = code + rest[:dash], ""
                elif open_ != -1:
                    code, depth, rest = code + rest[:open_], 1, rest[open_ + 2 :]
                else:
                    code, rest = code + rest, ""
        code = code.strip()
        if code and code not in ("prelude", "module"):
            break
    return found


class SpecLayerChecker:
    def __init__(self, project_root: Path, package: str, math_proof_imports: dict[str, tuple[str, ...]] | None = None):
        self.root = project_root
        self.package = package
        self.spec_dir = project_root / package / "Spec"
        self.math_dir = project_root / package / "Math"
        self.math_proof_imports = math_proof_imports or {}
        self.unresolved: set[str] = set()
        self._imports_cache: dict[str, tuple[str, ...]] = {}

    def module_path(self, name: str) -> Path:
        parts = components(name)
        return self.root.joinpath(*parts[:-1], parts[-1] + ".lean")

    def module_name(self, path: Path) -> str:
        parts = list(path.relative_to(self.root).parts)
        return canonical(parts[:-1] + [parts[-1][: -len(".lean")]])

    def imports(self, name: str) -> tuple[str, ...]:
        if name in self._imports_cache:
            return self._imports_cache[name]
        path = self.module_path(name)
        if not path.is_file():
            self.unresolved.add(name)
            self._imports_cache[name] = ()
            return ()
        found = [canonical(components(m)) for m in header_imports(path.read_text())]
        res = tuple(m for m in found if m == self.package or m.startswith(self.package + "."))
        self._imports_cache[name] = res
        return res

    def layer(self, name: str) -> str | None:
        for part in LAYERS:
            prefix = f"{self.package}.Spec.{part}"
            if name == prefix or name.startswith(prefix + "."):
                return part
        return None

    def is_proof(self, name: str) -> bool:
        return name == f"{self.package}.Proof" or name.startswith(f"{self.package}.Proof.")

    def closure(self, start: str) -> dict[str, str | None]:
        parent: dict[str, str | None] = {start: None}
        stack = [start]
        while stack:
            name = stack.pop()
            for child in self.imports(name):
                if child not in parent:
                    parent[child] = name
                    stack.append(child)
        return parent

    @staticmethod
    def chain(parent: dict[str, str | None], name: str) -> str:
        names = [name]
        while parent[names[-1]] is not None:
            names.append(parent[names[-1]])  # type: ignore[arg-type]
        return " <- ".join(names)

    def run(self) -> tuple[list[str], int, int]:
        errors: list[str] = []
        if not self.spec_dir.is_dir():
            return [f"{self.package}/Spec does not exist"], 0, 0
        allowed_entries = set(LAYERS) | {part + ".lean" for part in LAYERS}
        for entry in sorted(self.spec_dir.iterdir()):
            if entry.name not in allowed_entries or (entry.is_dir() != (entry.suffix == "")):
                errors.append(
                    f"{self.package}/Spec/{entry.name}: only the folders Safety/, Functional/ and Common/ "
                    f"and their root import files may be directly under {self.package}/Spec"
                )
        modules = sorted(self.module_name(p) for p in self.spec_dir.rglob("*.lean"))
        for mod in modules:
            mod_layer = self.layer(mod)
            if mod_layer is None:
                continue
            parent = self.closure(mod)
            reached = sorted(parent)
            if mod_layer in ("Safety", "Common"):
                bad = [n for n in reached if self.layer(n) == "Functional"]
                if bad:
                    errors.append(f"{mod} imports functional {bad[0]}: {self.chain(parent, bad[0])}")
            if mod_layer == "Common":
                bad = [n for n in reached if self.layer(n) == "Safety"]
                if bad:
                    errors.append(f"{mod} imports safety {bad[0]}: {self.chain(parent, bad[0])}")
            bad_proof = [n for n in reached if self.is_proof(plain(n))]
            if bad_proof:
                errors.append(f"{mod} imports the proof module {bad_proof[0]}: {self.chain(parent, bad_proof[0])}")

        common_dir = self.spec_dir / "Common"
        if common_dir.is_dir():
            for path in sorted(common_dir.rglob("*.lean")):
                spaces: list[str] = []
                for number, line in enumerate(path.read_text().splitlines(), 1):
                    m_ns = re.match(r"namespace\s+(\S+)", line)
                    if m_ns:
                        spaces.append(m_ns.group(1))
                    m_end = re.match(r"end\s+(\S+)\s*$", line)
                    if m_end and spaces and spaces[-1] == m_end.group(1):
                        spaces.pop()
                    m_goal = re.match(r"(?:def|abbrev)\s+(Goal\.\S+)", line)
                    if m_goal:
                        gname = ".".join(spaces + [m_goal.group(1)])
                        errors.append(
                            f"{path.relative_to(self.root)}:{number}: the goal {gname} is defined "
                            "under Spec/Common: move it to Spec/Safety or Spec/Functional"
                        )

        allowed_math = {(plain(src), plain(dst)) for src, dsts in self.math_proof_imports.items() for dst in dsts}
        found_math: set[tuple[str, str]] = set()
        if self.math_dir.is_dir():
            for path in sorted(self.math_dir.rglob("*.lean")):
                src = self.module_name(path)
                for dst in self.imports(src):
                    if self.is_proof(plain(dst)):
                        found_math.add((src, plain(dst)))
                        if (src, plain(dst)) not in allowed_math:
                            errors.append(f"{src} imports the proof module {dst}: a Math module may not")
        for src, dst in sorted(allowed_math - found_math):
            errors.append(f"listed import {src} -> {dst} no longer exists: delete it from math_proof_imports")

        for name in sorted(self.unresolved):
            errors.append(
                f"the imported module {name} has no file {self.module_path(name).relative_to(self.root)}: "
                "its imports cannot be followed"
            )
        return errors, len(modules), len(found_math)


def load_math_allowlist(project_root: Path, spec_cfg: dict) -> dict[str, tuple[str, ...]]:
    if "math_proof_imports" in spec_cfg:
        return {k: tuple(v) for k, v in spec_cfg["math_proof_imports"].items()}
    script_rel = spec_cfg.get("math_proof_imports_script")
    if script_rel:
        script_path = project_root / script_rel
        spec = importlib.util.spec_from_file_location("_proj_spec_layers", script_path)
        assert spec and spec.loader
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        return {k: tuple(v) for k, v in getattr(mod, "MATH_PROOF_IMPORTS", {}).items()}
    return {}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("projects", nargs="*", help="Optional project IDs (default: all with checks.spec_layers)")
    args = parser.parse_args()
    projects = [load_project(pid, REPO) for pid in args.projects] if args.projects else load_all_projects(REPO)
    failed = False
    for proj in projects:
        spec_cfg = proj.data.get("checks", {}).get("spec_layers")
        if not spec_cfg:
            continue
        allow = load_math_allowlist(proj.root, spec_cfg)
        checker = SpecLayerChecker(proj.root, proj.package, allow)
        errors, count, remaining = checker.run()
        if errors:
            failed = True
            print(f"[{proj.id}] Specification layer check failed:")
            for err in errors:
                print("  " + err)
        else:
            print(
                f"[{proj.id}] specification layers: {count} modules under {proj.package}/Spec; "
                f"safety and common import no functional module, common imports no safety module and defines no goal, "
                f"and none imports a proof module; {remaining} listed Math -> Proof imports remain"
            )
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())

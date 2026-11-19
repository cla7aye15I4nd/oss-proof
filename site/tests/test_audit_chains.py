"""Keep the call-chain data behind the unlisted audit page honest.

Structure is always checked. Every file path and function name is also checked against the
upstream sources whenever the corresponding submodule is checked out (CI's Pages job does not check
out submodules, so those cases are skipped there and run locally).
"""
from __future__ import annotations

from pathlib import Path
import json
import unittest

SITE_DIR = Path(__file__).resolve().parents[1]
REPO = SITE_DIR.parent
DATA = json.loads((SITE_DIR / "pages" / "data" / "audit-chains.json").read_text())
SOURCE_SUFFIXES = {".c", ".h", ".cc", ".cpp", ".mjs", ".js", ".py", ".rs"}


def walk_steps(steps):
    for step in steps:
        yield step
        for branch in step.get("branches", []):
            yield from walk_steps(branch["steps"])


def all_steps():
    for group in DATA["groups"]:
        for chain in group["chains"]:
            for step in walk_steps(chain["steps"]):
                yield chain["id"], step
            for branch in chain.get("branches", []):
                for step in walk_steps(branch["steps"]):
                    yield chain["id"], step


def repo_dir(name: str) -> Path | None:
    path = DATA["repos"].get(name, {}).get("path")
    if not path:
        return None
    root = REPO / path
    return root if root.is_dir() and any(root.iterdir()) else None


_SOURCES: dict[str, str] = {}


def repo_text(name: str, root: Path) -> str:
    if name not in _SOURCES:
        parts = []
        for p in root.rglob("*"):
            if p.suffix in SOURCE_SUFFIXES and p.is_file() and ".git" not in p.parts:
                try:
                    parts.append(p.read_text(errors="ignore"))
                except OSError:
                    pass
        _SOURCES[name] = "\n".join(parts)
    return _SOURCES[name]


class AuditChainTests(unittest.TestCase):
    def test_structure(self):
        ids = [c["id"] for g in DATA["groups"] for c in g["chains"]]
        self.assertEqual(len(ids), len(set(ids)))
        for group in DATA["groups"]:
            self.assertTrue(set(group["matrix"]) <= set(DATA["libraries"]), group["id"])
            for chain in group["chains"]:
                for key in ("title", "summary", "code"):
                    self.assertEqual(set(chain[key]), {"zh", "en"}, (chain["id"], key))
        for chain_id, step in all_steps():
            self.assertIn(step["layer"], {"js", "cpp", "vips", "py", "pyc", "rust", "lib"}, chain_id)
            if step.get("lib"):
                self.assertIn(step["lib"], DATA["libraries"], chain_id)
            if step.get("file"):
                self.assertIn(step["repo"], DATA["repos"], chain_id)

    def test_target_libraries_have_agents_md(self):
        for lib, info in DATA["libraries"].items():
            if info["status"] in {"target", "progress"}:
                self.assertTrue((REPO / "projects" / lib / "AGENTS.md").is_file(), lib)

    def test_files_and_functions_exist_upstream(self):
        checked = 0
        for chain_id, step in all_steps():
            root = repo_dir(step.get("repo", ""))
            if root is None:
                continue
            if step.get("file"):
                path = root / step["file"]
                self.assertTrue(path.is_file(), (chain_id, str(path)))
                text = path.read_text(errors="ignore")
            else:
                text = repo_text(step["repo"], root)
            for symbol in step.get("symbols", []):
                self.assertIn(symbol, text, (chain_id, step.get("file") or step["repo"], symbol))
                checked += 1
        if checked == 0:
            self.skipTest("no upstream submodules checked out")


if __name__ == "__main__":
    unittest.main()

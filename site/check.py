#!/usr/bin/env python3
"""Audit the generated oss-proof site (portal + all project subsites)."""
from __future__ import annotations

from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urlsplit
import re
import subprocess
import sys

SITE_DIR = Path(__file__).resolve().parent
REPO = SITE_DIR.parent
ROOT = SITE_DIR / "dist"

sys.path.insert(0, str(REPO))
sys.path.insert(0, str(REPO / "projects/zlib/docs/web"))

from framework.manifest import load_all_projects
from language import audit_chinese_html
import project_docs


class AuditPage(HTMLParser):
    def __init__(self, path: Path):
        super().__init__()
        self.path = path
        self.ids: set[str] = set()
        self.links: list[str] = []
        self.titles = 0
        self.global_toc = 0
        self.redirect = False
        self.uncolored_code: list[str] = []
        doc = path.read_text()
        self.feed(doc)
        parts = path.relative_to(ROOT).parts
        is_zh = "zh" in parts
        self.language_issues = audit_chinese_html(doc) if is_zh else []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        a = dict(attrs)
        if tag == "html" and ("data-book-redirect" in a or "data-root-redirect" in a):
            self.redirect = True
        if "id" in a and a["id"]:
            assert a["id"] not in self.ids, f"Duplicate id {a['id']} in {self.path}"
            self.ids.add(a["id"])
        for key in ("href", "src"):
            val = a.get(key)
            if val:
                self.links.append(val)
        if tag == "h1":
            self.titles += 1
        if "data-global-toc" in a:
            self.global_toc += 1
        if tag == "code":
            classes = (a.get("class") or "").split()
            lang = next((c[9:] for c in classes if c.startswith("language-")), "")
            if lang in {"c", "lean", "lean4", "sh", "bash", "python", "json", "toml"} and "syntax-highlight" not in classes:
                self.uncolored_code.append(lang)
            if lang == "mermaid":
                assert "syntax-highlight" not in classes, "Mermaid block must keep original markup"


def check_bilingual_dir_parity(base: Path, all_pages: dict[Path, AuditPage], check_ids: bool = True) -> None:
    en_dir = (base / "en").resolve()
    zh_dir = (base / "zh").resolve()
    en_rels = {p.relative_to(en_dir) for p in all_pages if p.is_relative_to(en_dir)}
    zh_rels = {p.relative_to(zh_dir) for p in all_pages if p.is_relative_to(zh_dir)}
    assert en_rels == zh_rels and en_rels, (base, "en/ and zh/ diverged", en_rels ^ zh_rels)
    if check_ids:
        for rel in en_rels:
            assert all_pages[(en_dir / rel).resolve()].ids == all_pages[(zh_dir / rel).resolve()].ids, (
                base,
                "Anchor IDs diverged",
                rel,
            )


def main() -> int:
    assert ROOT.is_dir(), "site/dist does not exist; run python3 site/build.py first"
    assert (ROOT / ".nojekyll").is_file(), "Missing .nojekyll in site/dist"

    for css in (ROOT / "static").glob("*.css"):
        for ref in re.findall(r"url\(['\"]?([^)'\"]+)", css.read_text()):
            if ":" not in ref:
                assert (css.parent / ref).exists(), (css.name, ref)

    all_pages = {p.resolve(): AuditPage(p) for p in ROOT.rglob("*.html")}
    root_resolved = ROOT.resolve()
    root_index = (ROOT / "index.html").resolve()
    assert root_index in all_pages and all_pages[root_index].redirect, "site/dist/index.html must be language redirect"

    # Check portal en/ and zh/ parity
    check_bilingual_dir_parity(ROOT, all_pages, check_ids=True)

    # Check every HTML file across portal + all subsites
    for path, page in all_pages.items():
        assert not path.name.endswith((".zh.html", ".en.html")), ("Language suffix forbidden", path)
        assert page.titles == 1, (path, "Expected one h1", page.titles)
        assert not page.uncolored_code, (path, "Uncolored code block", page.uncolored_code)
        assert not page.language_issues, (path, "Chinese prose issue", page.language_issues)
        if not page.redirect:
            assert page.global_toc == 1, (path, "Missing global contents")
        for link in page.links:
            url = urlsplit(link)
            if url.scheme or url.netloc:
                continue
            assert not url.path.startswith("/"), (path, "Root-relative link escapes /oss-proof/ subpath", link)
            target = (path.parent / unquote(url.path)).resolve() if url.path else path
            assert target.is_relative_to(root_resolved), (path, "Link escapes site/dist", link)
            assert target.exists(), (path, "Missing local target", link)
            if url.fragment and target in all_pages:
                assert unquote(url.fragment) in all_pages[target].ids, (path, "Missing anchor", link)

    # Run per-project site checks
    for proj in load_all_projects(REPO):
        checker = proj.data.get("site", {}).get("checker")
        if checker:
            subprocess.run([sys.executable, checker], cwd=proj.root, check=True)
        else:
            route = proj.data.get("site", {}).get("route", proj.id)
            sub_index = (ROOT / route / "index.html").resolve()
            assert sub_index in all_pages and all_pages[sub_index].redirect, (route, "Missing subsite redirect")
            check_bilingual_dir_parity(ROOT / route, all_pages, check_ids=False)
            project_docs.check_standard_docs_parity(proj.root)

    tests_dir = SITE_DIR / "tests"
    if tests_dir.is_dir():
        subprocess.run([sys.executable, "-m", "unittest", "discover", "-s", str(tests_dir), "-p", "test_*.py"], check=True)

    print(f"oss-proof site check passed: {len(all_pages)} total HTML pages across portal and registered projects")
    return 0


if __name__ == "__main__":
    sys.exit(main())

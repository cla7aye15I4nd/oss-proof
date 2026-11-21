"""Tests for the unified oss-proof portal and subsite routing."""
from __future__ import annotations

from pathlib import Path
import sys
import unittest

SITE_DIR = Path(__file__).resolve().parents[1]
REPO = SITE_DIR.parent
sys.path.insert(0, str(SITE_DIR))
sys.path.insert(0, str(REPO))

import portal
from framework.manifest import load_project


class PortalTests(unittest.TestCase):
    def test_zlib_summary_matches_verified_counts(self):
        proj = load_project("zlib", REPO)
        summary = portal.summarize_project(proj)
        self.assertTrue(summary.done)
        self.assertEqual(summary.documented_functions, 86)
        self.assertEqual(summary.proved_functions, 86)
        self.assertEqual(summary.proved_required_goals, summary.required_goals)
        self.assertEqual(summary.findings_count, 8)
        self.assertEqual(summary.patches_count, 6)

    def test_portal_and_subsite_outputs_exist(self):
        dist = SITE_DIR / "dist"
        self.assertTrue((dist / "index.html").is_file())
        for lang in ("en", "zh"):
            portal_html = (dist / lang / "index.html").read_text()
            self.assertIn(f"../zlib/{lang}/index.html", portal_html)
            self.assertIn(f"../zlib/{lang}/progress.html", portal_html)
            zlib_html = (dist / "zlib" / lang / "index.html").read_text()
            self.assertIn(f"../../{lang}/index.html", zlib_html)

    def test_unlisted_pages_exist_but_are_not_linked(self):
        dist = SITE_DIR / "dist"
        names = sorted(p.stem for p in (SITE_DIR / "pages" / "en").glob("*.md"))
        self.assertTrue(names)
        linked = "".join(p.read_text() for p in dist.rglob("*.html") if p.stem not in names)
        for name in names:
            for lang in ("en", "zh"):
                page = (dist / lang / f"{name}.html").read_text()
                self.assertIn('name="robots" content="noindex,nofollow"', page)
            self.assertNotIn(f"{name}.html", linked)


if __name__ == "__main__":
    unittest.main()

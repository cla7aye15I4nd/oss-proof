#!/usr/bin/env python3
"""Self-tests of `scripts/verification.py`: public API inventory against `mozjpeg/jpeglib.h`."""

import copy
import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
import verification as v  # noqa: E402


class CoverageTests(unittest.TestCase):
    def setUp(self):
        self.header = (ROOT / v.HEADER).read_text()
        self.manifest = json.loads((ROOT / v.MANIFEST).read_text())
        goals = []
        for api in self.manifest["apis"]:
            if api["status"] == "done":
                goals += [api["safety_goal"]] + api.get("other_goals", [])
        self.lists = {"proved": list(goals), "notDone": [], "required": list(goals)}

    def check(self, manifest=None, lists=None):
        return v.check_manifest(manifest or self.manifest, self.header, lists or self.lists, ROOT)

    def rejects(self, pattern, manifest=None, lists=None):
        with self.assertRaisesRegex(v.Rejected, pattern):
            self.check(manifest, lists)

    def api(self, manifest, function):
        return next(a for a in manifest["apis"] if a["function"] == function)

    def test_header_inventory(self):
        names = v.public_names(self.header)
        self.assertEqual(len(names), len(set(names)))
        for name in (
            "jpeg_std_error",
            "jpeg_CreateDecompress",
            "jpeg_mem_src",
            "jpeg_save_markers",
            "jpeg_read_header",
            "jpeg_core_output_dimensions",
            "jpeg_calc_output_dimensions",
            "jpeg_read_scanlines",
            "jpeg_destroy_decompress",
        ):
            self.assertIn(name, names)

    def test_manifest_passes(self):
        counts = self.check()
        self.assertEqual(counts["declared"], len(self.manifest["apis"]))
        self.assertEqual(counts["done"], 10)

    def test_missing_and_extra_functions(self):
        m = copy.deepcopy(self.manifest)
        m["apis"] = [a for a in m["apis"] if a["function"] != "jpeg_read_header"]
        self.rejects("missing=\\['jpeg_read_header'\\]", m)
        m = copy.deepcopy(self.manifest)
        m["apis"].append({"function": "jpeg_fake_api", "status": "not-done", "scope": "lp64-linux", "reason": "x"})
        self.rejects("extra=\\['jpeg_fake_api'\\]", m)
        m = copy.deepcopy(self.manifest)
        m["apis"].append(copy.deepcopy(self.api(m, "jpeg_read_header")))
        self.rejects("duplicated=\\['jpeg_read_header'\\]", m)

    def test_status_needs_reason_or_goal(self):
        m = copy.deepcopy(self.manifest)
        del self.api(m, "jpeg_read_header")["reason"]
        self.rejects("needs a reason", m)
        m = copy.deepcopy(self.manifest)
        self.api(m, "jpeg_read_header")["status"] = "skipped"
        self.rejects("status of jpeg_read_header", m)

    def test_done_goals_proved_and_required(self):
        goal = v.SAFETY + "jpeg_std_error_safety"
        lists = copy.deepcopy(self.lists)
        lists["required"].remove(goal)
        self.rejects("missing from `required`", lists=lists)
        lists = copy.deepcopy(self.lists)
        lists["proved"].remove(goal)
        self.rejects("is not proved", lists=lists)
        lists = copy.deepcopy(self.lists)
        lists["notDone"].append(goal)
        self.rejects("listed as not done", lists=lists)
        m = copy.deepcopy(self.manifest)
        self.api(m, "jpeg_abort")["safety_goal"] = v.SAFETY + "jpeg_destroy_safety"
        self.rejects("names its own safety goal", m)

    def test_not_done_with_proved_goal_is_stale(self):
        lists = copy.deepcopy(self.lists)
        lists["proved"].append(v.SAFETY + "jpeg_read_header_safety")
        self.rejects("its safety goal is proved", lists=lists)

    def test_translation_binding(self):
        m = copy.deepcopy(self.manifest)
        self.api(m, "jpeg_std_error")["implementation"] = "Mozjpeg.Jutils.jpeg_std_error"
        self.rejects("wrong translated entry binding", m)
        m = copy.deepcopy(self.manifest)
        self.api(m, "jpeg_std_error")["source"] = "MozjpegF/Mozjpeg/jutils.c.lean"
        self.rejects("missing translated entry", m)


if __name__ == "__main__":
    unittest.main()

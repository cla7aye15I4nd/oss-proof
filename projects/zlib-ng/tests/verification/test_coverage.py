#!/usr/bin/env python3
"""Self-tests of scripts/verification.py: the public API inventory against zlib-ng/zlib.h.in and the
lists of ZlibNgF/Results.lean. The lists are synthesised from the inventory here, so these tests do not
need the built library; the gate runs the script itself on the lists as Lean evaluates them."""

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
        for name in ("adler32", "crc32_combine_gen64", "gzopen64", "gzvprintf", "gzopen_w", "inflateBackInit_"):
            self.assertIn(name, names)
        self.assertEqual(v.windows_names(self.header), {"gzopen_w"})
        self.assertIn("zError", v.undocumented_names(self.header))

    def test_manifest_passes(self):
        counts = self.check()
        self.assertEqual(counts["declared"], len(self.manifest["apis"]))
        self.assertEqual(counts["not-applicable"], 1)

    def test_missing_and_extra_functions(self):
        m = copy.deepcopy(self.manifest)
        m["apis"] = [a for a in m["apis"] if a["function"] != "inflate"]
        self.rejects("missing=\\['inflate'\\]", m)
        m = copy.deepcopy(self.manifest)
        m["apis"].append({"function": "inflateFoo", "status": "not-done", "scope": "lp64-linux", "reason": "x"})
        self.rejects("extra=\\['inflateFoo'\\]", m)
        m = copy.deepcopy(self.manifest)
        m["apis"].append(copy.deepcopy(self.api(m, "compress")))
        self.rejects("duplicated=\\['compress'\\]", m)

    def test_status_needs_reason_or_goal(self):
        m = copy.deepcopy(self.manifest)
        del self.api(m, "compress")["reason"]
        self.rejects("needs a reason", m)
        m = copy.deepcopy(self.manifest)
        self.api(m, "compress")["status"] = "skipped"
        self.rejects("status of compress", m)
        m = copy.deepcopy(self.manifest)
        self.api(m, "inflate")["status"] = "not-applicable"
        self.rejects("only a Windows-only function", m)

    def test_done_goals_proved_and_required(self):
        goal = v.SAFETY + "crc32_safety"
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
        self.api(m, "crc32")["safety_goal"] = v.SAFETY + "crc32_z_safety"
        self.rejects("names its own safety goal", m)

    def test_not_done_with_proved_goal_is_stale(self):
        lists = copy.deepcopy(self.lists)
        lists["proved"].append(v.SAFETY + "compress_safety")
        self.rejects("its safety goal is proved", lists=lists)

    def test_translation_binding(self):
        m = copy.deepcopy(self.manifest)
        self.api(m, "crc32")["implementation"] = "ZlibNg.Adler32.crc32"
        self.rejects("wrong translated entry binding", m)
        m = copy.deepcopy(self.manifest)
        self.api(m, "crc32")["source"] = "ZlibNgF/ZlibNg/adler32.c.lean"
        self.rejects("missing translated entry", m)

    def test_undocumented_list(self):
        m = copy.deepcopy(self.manifest)
        m["undocumented"]["functions"].remove("zError")
        self.rejects("undocumented functions differ", m)


if __name__ == "__main__":
    unittest.main()

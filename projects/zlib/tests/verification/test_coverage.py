#!/usr/bin/env python3
"""Self-tests of scripts/verification.py: the lists of ZlibF/Results.lean and the required goals.
Needs the built library (the lists are read as Lean evaluates them)."""

import sys
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
import verification  # noqa: E402

GOAL = "ZlibF.Spec.Public.Goal."


class CoverageTests(unittest.TestCase):
    def setUp(self):
        self.manifest = verification.coverage()
        self.lists = verification.results()

    def changed(self, kind, drop):
        lists = dict(self.lists)
        lists[kind] = [g for g in lists[kind] if g != drop]
        return patch.object(verification, "results", return_value=lists)

    def test_results_lists(self):
        proved, not_done, required = self.lists["proved"], self.lists["notDone"], self.lists["required"]
        self.assertIn(GOAL + "inflate_safety", proved)
        self.assertIn(GOAL + "gz_sequence", not_done)
        self.assertFalse(set(proved) & set(not_done))
        self.assertLessEqual(set(required), set(proved))

    def test_required_goals_are_listed(self):
        verification.check_required_listed(self.manifest)
        with self.changed("required", GOAL + "inflate_safety"):
            with self.assertRaisesRegex(verification.Rejected, "inflate_safety"):
                verification.check_required_listed(self.manifest)
        with self.changed("required", GOAL + "compress_uncompress_roundtrip"):
            with self.assertRaisesRegex(verification.Rejected, "compress_uncompress_roundtrip"):
                verification.check_required_listed(self.manifest)

    def test_not_planned_is_not_done(self):
        verification.check_not_planned(self.manifest)
        with self.changed("notDone", GOAL + "gz_initialisation_domain"):
            with self.assertRaisesRegex(verification.Rejected, "not listed as not done"):
                verification.check_not_planned(self.manifest)


if __name__ == "__main__":
    unittest.main()

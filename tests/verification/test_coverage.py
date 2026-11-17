#!/usr/bin/env python3
"""Self-tests of scripts/verification.py: the lists of ZlibF/Results.lean and the required goals."""

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

    def test_results_lists(self):
        proved, not_done = verification.results()
        self.assertIn(GOAL + "inflate_safety", proved)
        self.assertIn(GOAL + "gz_sequence", not_done)
        self.assertFalse(set(proved) & set(not_done))
        self.assertEqual(len(proved), len(set(proved)))

    def test_required_goals_are_proved(self):
        verification.check_required_proved(self.manifest)
        proved, not_done = verification.results()
        without = [g for g in proved if g != GOAL + "inflate_safety"]
        with patch.object(verification, "results", return_value=(without, not_done)):
            with self.assertRaisesRegex(verification.Rejected, "inflate_safety"):
                verification.check_required_proved(self.manifest)

    def test_not_planned_is_not_done(self):
        verification.check_not_planned(self.manifest)
        proved, not_done = verification.results()
        planned = [g for g in not_done if g != GOAL + "gz_initialisation_domain"]
        with patch.object(verification, "results", return_value=(proved, planned)):
            with self.assertRaisesRegex(verification.Rejected, "not listed as not done"):
                verification.check_not_planned(self.manifest)


if __name__ == "__main__":
    unittest.main()

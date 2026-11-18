#!/usr/bin/env python3
"""Self-tests of scripts/check-options.py: the allow-lists accept the tree and reject each weakening."""

import shutil
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
check = __import__("check-options")


class OptionsCheckTests(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        (self.tmp / "ZlibF").mkdir()
        (self.tmp / "tests").mkdir()
        for f in ("lakefile.toml", "tests/lakefile.toml"):
            shutil.copy(ROOT / f, self.tmp / f)
        (self.tmp / "ZlibF.lean").write_text("import ZlibF.A\n")
        self.module = self.tmp / "ZlibF/A.lean"
        self.module.write_text("set_option autoImplicit false\nset_option maxHeartbeats 400000 in\n"
                               "set_option linter.unusedSimpArgs false\ntheorem t : True := trivial\n")

    def tearDown(self):
        shutil.rmtree(self.tmp)

    def errors(self):
        return check.option_errors(self.tmp) + check.lakefile_errors(self.tmp)

    def test_tree_passes(self):
        self.assertEqual(check.option_errors(ROOT) + check.lakefile_errors(ROOT), [])

    def test_allowed_options_pass(self):
        self.assertEqual(self.errors(), [])

    def test_options_rejected(self):
        for text in ("set_option debug.skipKernelTC true", "set_option «debug».skipKernelTC true in",
                     "set_option «debug.skipKernelTC» true", "  set_option bootstrap.genMatcherCode false in",
                     "set_option warn.sorry false"):
            with self.subTest(text=text):
                self.module.write_text(text + "\ntheorem t : True := trivial\n")
                self.assertTrue(self.errors())

    def test_lakefile_keys_rejected(self):
        base = (self.tmp / "lakefile.toml").read_text()
        for extra in ('leanOptions = {"debug.skipKernelTC" = true}', 'weakLeanArgs = ["-Ddebug.skipKernelTC=true"]',
                      'moreLeanArgs = ["-DmaxHeartbeats=0"]', 'plugins = ["x"]', 'dynlibs = ["x"]',
                      'precompileModules = true'):
            with self.subTest(extra=extra):
                (self.tmp / "lakefile.toml").write_text(base.replace('roots = ["ZlibF", "ZlibF.Results"]',
                                                                     'roots = ["ZlibF", "ZlibF.Results"]\n' + extra))
                self.assertTrue(self.errors())

    def test_lean_lakefile_rejected(self):
        (self.tmp / "lakefile.lean").write_text("import Lake\n")
        self.assertTrue(self.errors())

    def test_extra_requirement_rejected(self):
        path = self.tmp / "tests/lakefile.toml"
        path.write_text(path.read_text() + '\n[[require]]\nname = "x"\npath = "x"\n')
        self.assertTrue(self.errors())


if __name__ == "__main__":
    unittest.main()

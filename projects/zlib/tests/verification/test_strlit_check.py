"""The string literal check reads the text passed to every helper, and fails on a use it cannot read."""
import importlib.util
from pathlib import Path
import unittest

SPEC = importlib.util.spec_from_file_location('check_strlit',
    Path(__file__).resolve().parents[2] / 'scripts' / 'check-strlit.py')
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def scan(source):
    found, errors = {}, []
    MODULE.scan('X.lean', source, found, errors)
    return found, errors


class ScanTests(unittest.TestCase):
    def test_helpers_are_read(self):
        found, errors = scan('def f := do\n'
                             '  let p ← strLit "a"\n'
                             '  let q ← Zlib.Zutil.strLit "b\\n"\n'
                             '  badMode c "invalid code -- missing end-of-block"  -- strLit "in a comment"\n'
                             '  /- setMsg s "in a block comment" -/\n'
                             '  badData c\n    "next line"\n'
                             '  setMsg (f x) "d"\n')
        self.assertEqual(errors, [])
        self.assertEqual(found, {'a': ['X.lean:2'], 'b\n': ['X.lean:3'],
                                 'invalid code -- missing end-of-block': ['X.lean:4'],
                                 'next line': ['X.lean:6'], 'd': ['X.lean:8']})

    def test_unread_use_is_an_error(self):
        found, errors = scan('def f := do\n  badMode c text\n')
        self.assertEqual(found, {})
        self.assertEqual(len(errors), 1)
        self.assertIn('X.lean:2', errors[0])

    def test_new_string_definition_is_an_error(self):
        _, errors = scan('def fail (c : Ctx)\n    (msg : String) : M Unit := do\n  pure ()\n')
        self.assertEqual(len(errors), 1)
        self.assertIn('fail', errors[0])
        self.assertEqual(scan('def g (n : Nat) : Nat := n\n')[1], [])

    def test_tree(self):
        found, errors = MODULE.used()
        self.assertEqual(errors, [])
        self.assertIn('invalid code -- missing end-of-block', found)
        self.assertIn('incorrect header check', found)
        self.assertIn('stream error', found)
        self.assertLessEqual(set(found), set(MODULE.table()))


if __name__ == '__main__':
    unittest.main()

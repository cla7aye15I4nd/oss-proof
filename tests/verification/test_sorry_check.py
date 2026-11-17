"""The sorry check counts the token `sorry` in code, not the word in a comment or a string."""
import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('lean_sorry', ROOT / 'scripts' / 'lean_sorry.py')
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)

NOT_COUNTED = '''/- a block comment
   we are sorry about this
   /- nested sorry -/ still sorry
-/
/-- doc: no sorry here -/
theorem t1 : True := trivial
/-! module doc sorry -/
def s : String := "sorry \\" sorry"
def r : String := r#"sorry " sorry"#
def c : Char := '"'  -- sorry
def «sorry» := 1
def other := sorry' + mysorry + x.sorry + x'
'''

COUNTED = {
    'theorem a : True := sorry\n': [1],
    'theorem a : True := by\n  exact sorry -- note\n': [2],
    'theorem a : True := by exact sorry -- sorry for this\n': [1],
    '/- c -/ theorem a : True := sorry\n': [1],
    '-/ theorem a : True := sorry\n': [1],
    'def c := \'"\'\ntheorem a : True := sorry\ndef d := "x"\n': [2],
    'def m := s!"a {sorry} b"\n': [1],
    'theorem a : False := sorryAx _\n': [1],
    'theorem a : True ∧ True := ⟨sorry, sorry⟩\n': [1, 1],
}


class SorryTests(unittest.TestCase):
    def test_comments_and_literals_are_not_counted(self):
        self.assertEqual(MODULE.occurrences(NOT_COUNTED), [])

    def test_code_is_counted(self):
        for text, lines in COUNTED.items():
            self.assertEqual(MODULE.occurrences(text), lines, text)

    def test_script_output_and_exit_code(self):
        script = ['bash', str(ROOT / 'scripts' / 'check-sorry.sh')]
        with tempfile.TemporaryDirectory() as directory:
            clean = Path(directory) / 'clean'
            clean.mkdir()
            (clean / 'a.lean').write_text(NOT_COUNTED)
            result = subprocess.run(script + [str(clean)], capture_output=True, text=True)
            self.assertEqual((result.returncode, result.stdout), (0, 'sorry count: 0\n'))
            (clean / 'b.lean').write_text(''.join(COUNTED))
            result = subprocess.run(script + [str(clean)], capture_output=True, text=True)
            self.assertEqual(result.returncode, 1)
            self.assertEqual(result.stdout.splitlines()[-1], 'sorry count: 10')
            self.assertIn('sorry is not allowed', result.stderr)


if __name__ == '__main__':
    unittest.main()

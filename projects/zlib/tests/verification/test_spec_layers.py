"""Module names of the specification layer check: a dot inside «…» is part of the component."""
import importlib.util
from pathlib import Path
import unittest

SPEC = importlib.util.spec_from_file_location('check_spec_layers',
    Path(__file__).resolve().parents[2] / 'scripts' / 'check-spec-layers.py')
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ModuleNameTests(unittest.TestCase):
    def test_quoted_component_keeps_its_dots(self):
        self.assertEqual(MODULE.components('ZlibF.Proof.«trees.c.runs»'), ['ZlibF', 'Proof', 'trees.c.runs'])
        self.assertEqual(MODULE.module_path('ZlibF.Proof.«trees.c.runs»'),
                         MODULE.ROOT / 'ZlibF/Proof/trees.c.runs.lean')
        self.assertEqual(MODULE.module_path('ZlibF.Spec.Safety'), MODULE.ROOT / 'ZlibF/Spec/Safety.lean')

    def test_path_and_name_round_trip(self):
        for name in ('ZlibF.Proof.«trees.c.runs»', 'ZlibF.Math.«code-length-prefix»', 'ZlibF.Spec.Safety.Stream'):
            self.assertEqual(MODULE.module_name(MODULE.module_path(name)), name)
        self.assertEqual(MODULE.plain('ZlibF.Math.code-length-prefix'), 'ZlibF.Math.«code-length-prefix»')

    def test_header_imports(self):
        text = ('/- a comment with\nimport Not.This\n-/\n-- note\nimport ZlibF.Zlib.«inflate.c» -- why\n'
                'public import ZlibF.Spec.Common\n\ndef x := 1\nimport Too.Late\n')
        self.assertEqual(MODULE.header_imports(text), ['ZlibF.Zlib.«inflate.c»', 'ZlibF.Spec.Common'])

    def test_missing_module_is_recorded(self):
        MODULE.imports.cache_clear()
        MODULE.UNRESOLVED.clear()
        self.assertEqual(MODULE.imports('ZlibF.Proof.«no.such.module»'), ())
        self.assertEqual(MODULE.UNRESOLVED, {'ZlibF.Proof.«no.such.module»'})
        MODULE.UNRESOLVED.clear()
        MODULE.imports.cache_clear()

    def test_every_import_of_the_tree_resolves(self):
        for path in sorted((MODULE.ROOT / 'ZlibF').rglob('*.lean')):
            for name in MODULE.imports(MODULE.module_name(path)):
                self.assertTrue(MODULE.module_path(name).is_file(), f'{path}: {name}')


if __name__ == '__main__':
    unittest.main()

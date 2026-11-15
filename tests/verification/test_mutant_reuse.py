#!/usr/bin/env python3
"""Verdict reuse of the proof-mutant stage: one test per way to reuse a verdict that no longer holds.

None of these tests needs Lean. The keys and the store are exercised on a small fixture
workspace; the runner and the replay are replaced by recorders that count what was executed.
"""
from collections import Counter
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import types
import unittest
from contextlib import redirect_stdout
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
import mutant_reuse
import verification

LIST = 'tests/proof-mutants/fixture.tsv'
TEXT_ROW = 'drop-check\tZlibF/Zlib/f.c.lean\tx + 1\tx + 2\ta'
SAME_ROW = 'same-shape\tZlibF/Zlib/f.c.lean\tx + 1\t1 + x\ta\tsame:commutes'
SCRIPT_ROW = 'paired\tscript:tests/proof-mutants/m.py\t-\t-\ta,sub/c'
GOAL = 'Fixture.Goal.f'
API = {'function': 'f', 'source': 'ZlibF/Zlib/f.c.lean', 'functional_goal': GOAL, 'scope': 'lp64-linux'}
MUTATOR = '''import sys, pathlib
w = pathlib.Path(sys.argv[1])
for f in ('ZlibF/Zlib/f.c.lean', 'ZlibF/Proof/b.lean'):
    p = w / f; p.write_text(p.read_text().replace('x + 1', 'x + 3'))
'''


class Fixture(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='mutant-reuse-test-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / 'w'
        files = {
            'lean-toolchain': 'leanprover/lean4:v0\n',
            'lakefile.toml': 'name = "ZlibF"\n',
            'ZlibF.lean': 'import ZlibF.Proof.a\nimport ZlibF.Proof.other\nimport ZlibF.Proof.sub.c\n',
            'ZlibF/Zlib/f.c.lean': 'namespace Fixture\ndef f (x : Nat) : Nat := x + 1\nend Fixture\n',
            'ZlibF/Proof/a.lean': '/- the proof -/\nimport ZlibF.Zlib.«f.c»\nimport ZlibF.Proof.b -- helper\n'
                                  'theorem a : Fixture.f 0 = 1 := rfl\n',
            'ZlibF/Proof/b.lean': 'import Std\ntheorem b : 0 + 1 = 1 := rfl -- x + 1\n',
            'ZlibF/Proof/sub/c.lean': 'import ZlibF.Proof.b\n',
            'ZlibF/Proof/other.lean': 'theorem other : True := trivial\n',
            'tests/audit/theorems.txt': 'Fixture.exact\n',
            'tests/proof-mutants/m.py': MUTATOR,
            LIST: '\n'.join([TEXT_ROW, SAME_ROW, SCRIPT_ROW]) + '\n',
        }
        for path in mutant_reuse.TOOLS:
            files[path] = '# stand-in for ' + path + '\n'
        for path, text in files.items():
            (self.root / path).parent.mkdir(parents=True, exist_ok=True)
            (self.root / path).write_text(text)
        self.store = Path(self.temp.name) / 'store.json'
        self.out = Path(self.temp.name) / 'out.json'
        environment = patch.dict(os.environ, {'GITHUB_REPOSITORY': 'owner/repository', 'GITHUB_RUN_ID': '7',
                                              'GITHUB_RUN_ATTEMPT': '1'})
        environment.start()
        self.addCleanup(environment.stop)

    def edit(self, path, old, new):
        p = self.root / path
        text = p.read_text()
        self.assertIn(old, text)
        p.write_text(text.replace(old, new))

    def keys(self):
        """The key of every kind of unit, computed from a fresh reading of the fixture."""
        tree = mutant_reuse.Tree(self.root)
        base = mutant_reuse.base_digest(tree, self.root)
        return {'text': mutant_reuse.row_key(tree, base, LIST, TEXT_ROW),
                'same': mutant_reuse.row_key(tree, base, LIST, SAME_ROW),
                'script': mutant_reuse.row_key(tree, base, LIST, SCRIPT_ROW),
                'control': mutant_reuse.control_key(tree, base, GOAL, API),
                'replay': mutant_reuse.replay_key(tree, base, GOAL, API, LIST, TEXT_ROW)}

    def session(self, reuse=True, record=True):
        with redirect_stdout(io.StringIO()):
            return mutant_reuse.Session(self.root, self.root, self.store if reuse else None,
                                        self.out if record else None)


class Keys(Fixture):
    def test_keys_are_stable_and_distinct(self):
        first, second = self.keys(), self.keys()
        self.assertEqual(first, second)
        self.assertEqual(len(set(first.values())), len(first))

    def test_editing_a_proof_module_of_the_closure_changes_the_key(self):
        before = self.keys()
        # b.lean is imported by a.lean, the row's proof module: weakening it must not keep a verdict.
        self.edit('ZlibF/Proof/b.lean', '0 + 1 = 1', '0 + 1 = 1 ∨ True')
        after = self.keys()
        for unit in before:
            self.assertNotEqual(before[unit], after[unit], unit)

    def test_editing_the_expected_proof_module_changes_the_key(self):
        before = self.keys()
        self.edit('ZlibF/Proof/a.lean', 'Fixture.f 0 = 1', 'Fixture.f 0 = Fixture.f 0')
        after = self.keys()
        for unit in before:
            self.assertNotEqual(before[unit], after[unit], unit)

    def test_a_module_outside_the_closure_changes_only_the_replays(self):
        before = self.keys()
        self.edit('ZlibF/Proof/other.lean', 'trivial', 'True.intro')
        after = self.keys()
        for unit in ('text', 'same', 'script'):
            self.assertEqual(before[unit], after[unit], unit)
        # A replay picks its proof from the whole compiled library, so it is keyed by all of it.
        for unit in ('control', 'replay'):
            self.assertNotEqual(before[unit], after[unit], unit)

    def test_a_new_import_extends_the_closure(self):
        before = self.keys()
        self.edit('ZlibF/Proof/b.lean', 'import Std\n', 'import Std\nimport ZlibF.Proof.other\n')
        middle = self.keys()
        self.assertNotEqual(before['text'], middle['text'])
        self.edit('ZlibF/Proof/other.lean', 'trivial', 'True.intro')
        self.assertNotEqual(middle['text'], self.keys()['text'])

    def test_editing_the_mutated_file_changes_the_key(self):
        before = self.keys()
        self.edit('ZlibF/Zlib/f.c.lean', 'namespace Fixture\n', 'namespace Fixture\n-- note\n')
        after = self.keys()
        for unit in before:
            self.assertNotEqual(before[unit], after[unit], unit)

    def test_every_field_of_the_row_is_in_the_key(self):
        tree = mutant_reuse.Tree(self.root)
        base = mutant_reuse.base_digest(tree, self.root)
        original = mutant_reuse.row_key(tree, base, LIST, TEXT_ROW)
        fields = TEXT_ROW.split('\t')
        variants = [
            ['renamed'] + fields[1:],
            fields[:2] + ['x + 1', 'x + 5'] + fields[4:],
            fields[:2] + ['f (x', 'f (y'] + fields[4:],
            fields[:4] + ['a,sub/c'],
            fields[:4] + ['sub/c'],
            fields + ['same:claimed equivalent'],
        ]
        keys = {mutant_reuse.row_key(tree, base, LIST, '\t'.join(v)) for v in variants}
        self.assertEqual(len(keys), len(variants))
        self.assertNotIn(original, keys)
        self.assertNotEqual(original, mutant_reuse.row_key(tree, base, 'tests/proof-mutants/other.tsv', TEXT_ROW))
        self.assertNotEqual(mutant_reuse.replay_key(tree, base, GOAL, API, LIST, TEXT_ROW),
                            mutant_reuse.replay_key(tree, base, GOAL, API, LIST, '\t'.join(variants[1])))
        self.assertNotEqual(mutant_reuse.replay_key(tree, base, GOAL, API, LIST, TEXT_ROW),
                            mutant_reuse.replay_key(tree, base, GOAL + '_safety', API, LIST, TEXT_ROW))

    def test_editing_the_mutator_changes_the_key_even_when_its_effect_is_the_same(self):
        before = self.keys()
        self.edit('tests/proof-mutants/m.py', 'import sys, pathlib\n', 'import sys, pathlib  # same effect\n')
        after = self.keys()
        self.assertNotEqual(before['script'], after['script'])
        self.assertEqual(before['text'], after['text'])

    def test_what_the_mutator_writes_is_in_the_key(self):
        before = self.keys()
        # The mutator's own bytes stay; a file it reads decides a different edit of a closure module.
        self.edit('tests/proof-mutants/m.py', "'x + 3'", "(w / 'knob').read_text() if (w / 'knob').exists() else 'x + 3'")
        middle = self.keys()
        (self.root / 'knob').write_text('x + 4')
        after = self.keys()
        self.assertNotEqual(before['script'], middle['script'])
        self.assertNotEqual(middle['script'], after['script'])

    def test_editing_a_tool_or_the_build_configuration_changes_every_key(self):
        for path in mutant_reuse.TOOLS + ('lean-toolchain', 'lakefile.toml'):
            with self.subTest(path=path):
                before = self.keys()
                with (self.root / path).open('a') as handle:
                    handle.write('# edited\n')
                after = self.keys()
                for unit in before:
                    self.assertNotEqual(before[unit], after[unit], unit)
        before = self.keys()
        (self.root / 'lake-manifest.json').write_text('{}\n')
        after = self.keys()
        for unit in before:
            self.assertNotEqual(before[unit], after[unit], unit)

    def test_the_real_tools_are_the_ones_hashed(self):
        for path in ('scripts/verification.py', 'scripts/mutant_reuse.py', 'scripts/mutation_spans.py',
                     'tests/audit/proofmut.sh', 'tests/audit/ReplayPublicProof.lean'):
            self.assertIn(path, mutant_reuse.TOOLS)
            self.assertTrue((ROOT / path).is_file(), path)
        for path in mutant_reuse.TOOLS:
            self.assertTrue((ROOT / path).is_file(), path)

    def test_the_runner_environment_and_the_registry_are_in_the_key(self):
        before = self.keys()
        with patch.dict(os.environ, {'PROOFMUT_TIMEOUT': '7200'}):
            after = self.keys()
        for unit in before:
            self.assertNotEqual(before[unit], after[unit], unit)
        with patch.dict(os.environ, {'ZLIBF_REPLAY_RSS_MB': '99999'}):
            self.assertNotEqual(before['control'], self.keys()['control'])
        self.edit('tests/audit/theorems.txt', 'Fixture.exact\n', 'Fixture.weaker\nFixture.exact\n')
        after = self.keys()
        self.assertNotEqual(before['control'], after['control'])
        self.assertNotEqual(before['replay'], after['replay'])

    def test_units_that_cannot_pass_or_cannot_be_read_have_no_key(self):
        tree = mutant_reuse.Tree(self.root)
        base = mutant_reuse.base_digest(tree, self.root)
        fields = TEXT_ROW.split('\t')
        for row in ['\t'.join(fields + ['gap:known hole']),            # a flagged gap fails strict mode
                    '\t'.join(fields[:2] + ['absent', 'x'] + fields[4:]),  # NOT APPLIED
                    '\t'.join(fields[:2] + ['x', 'y'] + fields[4:]),       # occurs more than once
                    '\t'.join(fields[:3] + ['x + 1'] + fields[4:]),        # old equals new
                    '\t'.join(fields[:3] + ['sorry'] + fields[4:]),        # SORRY
                    '\t'.join(fields[:4] + ['missing']),                   # no such proof module
                    '\t'.join(fields[:4] + ['a,,b']),
                    '\t'.join(fields[:4]),
                    'x\tscript:tests/proof-mutants/absent.py\t-\t-\ta']:
            with self.subTest(row=row), self.assertRaises(mutant_reuse.Unkeyable):
                mutant_reuse.row_key(tree, base, LIST, row)
        self.edit('tests/proof-mutants/m.py', 'import sys, pathlib\n', 'import sys, pathlib\nsys.exit(1)\n')
        with self.assertRaises(mutant_reuse.Unkeyable):
            mutant_reuse.row_key(mutant_reuse.Tree(self.root), base, LIST, SCRIPT_ROW)
        self.edit('tests/proof-mutants/m.py', 'sys.exit(1)\n', "(w / 'ZlibF/Proof/other.lean').write_text('sorry')\n")
        with self.assertRaises(mutant_reuse.Unkeyable):
            mutant_reuse.row_key(mutant_reuse.Tree(self.root), base, LIST, SCRIPT_ROW)

    def test_symlinked_or_missing_inputs_have_no_key(self):
        target = self.root / 'ZlibF/Proof/b.lean'
        real = self.root / 'elsewhere.lean'
        shutil.move(target, real)
        target.symlink_to(real)
        tree = mutant_reuse.Tree(self.root)
        base = mutant_reuse.base_digest(tree, self.root)
        with self.assertRaises(mutant_reuse.Unkeyable):
            mutant_reuse.row_key(tree, base, LIST, TEXT_ROW)
        target.unlink()
        with self.assertRaisesRegex(mutant_reuse.Unkeyable, 'no source'):
            mutant_reuse.row_key(mutant_reuse.Tree(self.root), base, LIST, TEXT_ROW)
        (self.root / 'scripts/verification.py').unlink()
        with self.assertRaises(mutant_reuse.Unkeyable):
            mutant_reuse.base_digest(mutant_reuse.Tree(self.root), self.root)

    def test_the_mutator_sees_the_workspace_the_runner_gives_it(self):
        for path in ('.git/config', '.lake/build/x.olean', 'zlib/zlib.h', 'tests/build/zlib/x', 'tests/.lake/y',
                     'docs/page.md'):
            (self.root / path).parent.mkdir(parents=True, exist_ok=True)
            (self.root / path).write_text('x')
        copy = Path(self.temp.name) / 'copy'
        mutant_reuse.copy_workspace(self.root, copy)
        self.assertTrue((copy / 'docs/page.md').is_file())
        self.assertTrue((copy / 'ZlibF/Zlib/f.c.lean').is_file())
        for path in ('.git', '.lake', 'zlib', 'tests/build', 'tests/.lake'):
            self.assertFalse((copy / path).exists(), path)
        # The same exclusions as mkcopy in tests/audit/proofmut.sh.
        runner = (ROOT / 'tests/audit/proofmut.sh').read_text()
        self.assertIn('tar --exclude=.git --exclude=.lake --exclude=tests/build --exclude=zlib -cf - .', runner)


class Headers(unittest.TestCase):
    def test_import_forms(self):
        read = mutant_reuse.header_imports
        self.assertEqual(read('import A\nimport B.«c.d».E -- note\n\n/- text\nimport Hidden -/\nimport F\ndef x := 1\n'
                              'import NotAnImport\n'), ['A', 'B.«c.d».E', 'F'])
        self.assertEqual(read('module\nprelude\npublic import A\nmeta import B\nimport all C\npublic meta import D\n'),
                         ['A', 'B', 'C', 'D'])
        self.assertEqual(read('/- a /- nested -/ -/ import A import B\n'), ['A', 'B'])
        self.assertEqual(read('-- import Commented\nnamespace X\n'), [])
        self.assertEqual(read(''), [])

    def test_forms_that_could_hide_an_import_are_refused(self):
        for text in ('import A B\n', 'import A def x := 1\n', 'import\n', 'public def x := 1\n',
                     'import A /- c -/ B\n', '/- open', 'import «open\n', 'import A..B\n', 'import all\n'):
            with self.subTest(text=text), self.assertRaises(mutant_reuse.Unkeyable):
                mutant_reuse.header_imports(text)

    def test_agrees_with_the_audited_import_reading_on_the_library(self):
        tree = mutant_reuse.Tree(ROOT)
        sources = tree.lean_sources()
        self.assertGreater(len(sources), 1000)
        for path in sources:
            text = tree.read(path).decode('utf-8')
            # The reading of check_imports in scripts/verification.py.
            expected = [name for line in text.splitlines() if line.startswith('import ')
                        for name in line[7:].split('--', 1)[0].split()]
            self.assertEqual(mutant_reuse.header_imports(text, path), expected, path)

    def test_closure_of_the_root_is_the_library(self):
        tree = mutant_reuse.Tree(ROOT)
        closure = [path for path, digest in mutant_reuse.import_closure(tree, ['ZlibF.lean']) if digest]
        self.assertEqual(closure, tree.lean_sources())


class Stores(Fixture):
    def record(self, key, kind, **changes):
        record = {'schema': mutant_reuse.SCHEMA, 'key': key, 'kind': kind, 'unit': 'u',
                  'verdict': mutant_reuse.PASSING[kind], 'detail': '', 'peak_mb': 0, 'seconds': 1,
                  'commit': 'c' * 40, 'run': '7/1', 'repository': 'owner/repository', 'time': mutant_reuse.now()}
        record.update(changes)
        return record

    def write(self, *records):
        self.store.write_text(json.dumps({'version': mutant_reuse.SCHEMA, 'records': list(records)}))

    def reused(self, key, kind):
        session = self.session()
        with redirect_stdout(io.StringIO()):
            return session.lookup(key, kind, 'unit')

    def test_a_passing_record_of_the_same_key_and_kind_is_reused(self):
        keys = self.keys()
        self.write(self.record(keys['text'], 'row'))
        self.assertTrue(self.reused(keys['text'], 'row'))

    def test_a_failing_verdict_is_never_reused(self):
        keys = self.keys()
        for verdict in ('SURVIVED', 'BAD MUTANT', 'WRONG PLACE', 'NO ERROR', 'GAP (known)', 'SAME ok',
                        'KILLED (stale gap flag)', 'UNEXPECTED (marked same, build failed)', '', 'killed'):
            with self.subTest(verdict=verdict):
                self.write(self.record(keys['text'], 'row', verdict=verdict))
                self.assertFalse(self.reused(keys['text'], 'row'))
        for kind, verdict in (('control', 'REJECTED'), ('replay', 'REPLAYED'), ('replay', 'KILLED'),
                              ('row-same', 'KILLED')):
            with self.subTest(kind=kind, verdict=verdict):
                self.write(self.record(keys['replay'], kind, verdict=verdict))
                self.assertFalse(self.reused(keys['replay'], kind))

    def test_a_verdict_of_another_kind_of_unit_is_not_reused(self):
        keys = self.keys()
        self.write(self.record(keys['text'], 'row-same'), self.record(keys['control'], 'replay'))
        self.assertFalse(self.reused(keys['text'], 'row'))
        self.assertFalse(self.reused(keys['control'], 'control'))

    def test_a_hand_written_record_for_changed_inputs_is_not_used(self):
        stale = self.keys()
        self.write(*(self.record(stale[unit], kind) for unit, kind in
                     (('text', 'row'), ('same', 'row-same'), ('script', 'row'), ('control', 'control'),
                      ('replay', 'replay'))))
        self.edit('ZlibF/Proof/b.lean', '0 + 1 = 1', '0 + 1 = 1 ∨ True')
        current = self.keys()
        for unit, kind in (('text', 'row'), ('same', 'row-same'), ('script', 'row'), ('control', 'control'),
                           ('replay', 'replay')):
            self.assertFalse(self.reused(current[unit], kind), unit)
            self.assertTrue(self.reused(stale[unit], kind), unit)  # the record itself is well formed

    def test_malformed_records_and_stores_are_dropped(self):
        key = self.keys()['text']
        good = self.record(key, 'row')
        for bad in ({**good, 'extra': 1}, {k: v for k, v in good.items() if k != 'commit'}, {**good, 'schema': 0},
                    {**good, 'key': key[:12]}, {**good, 'kind': 'list'}, {**good, 'seconds': 'fast'},
                    {**good, 'repository': 'other/repository'}, {**good, 'repository': ''}, [good], 'KILLED', None):
            with self.subTest(bad=bad):
                self.write(bad)
                self.assertFalse(self.reused(key, 'row'))
        for text in ('', 'not json', '[]', json.dumps({'version': 0, 'records': [good]}),
                     json.dumps({'version': mutant_reuse.SCHEMA, 'records': {key: good}})):
            with self.subTest(text=text):
                self.store.write_text(text)
                self.assertFalse(self.reused(key, 'row'))
        self.store.unlink()
        self.assertFalse(self.reused(key, 'row'))

    def test_a_record_made_outside_the_workflow_is_not_used_in_it(self):
        key = self.keys()['text']
        with patch.dict(os.environ):
            del os.environ['GITHUB_REPOSITORY'], os.environ['GITHUB_RUN_ID']
            local = self.session(reuse=False)
            with redirect_stdout(io.StringIO()):
                local.passed(key, 'row', 'unit')
        shutil.copyfile(self.out, self.store)
        self.assertEqual(json.loads(self.store.read_text())['records'][0]['run'], 'local')
        self.assertFalse(self.reused(key, 'row'))

    def test_a_missing_key_is_never_reused_or_recorded(self):
        self.write(self.record('0' * 64, 'row'))
        session = self.session()
        with redirect_stdout(io.StringIO()):
            self.assertFalse(session.lookup(None, 'row', 'unit'))
            session.passed(None, 'row', 'unit')
        self.assertEqual((session.ran, session.reused, session.out), (1, 0, {}))

    def test_merge_keeps_valid_fresh_records_and_the_newest_of_a_key(self):
        key, other = self.keys()['text'], self.keys()['same']
        old = self.record(key, 'row', time='2026-11-01T00:00:00Z', commit='a' * 40)
        new = self.record(key, 'row', time=mutant_reuse.now(), commit='b' * 40)
        ancient = self.record(other, 'row-same', time='2020-01-01T00:00:00Z')
        first, second = Path(self.temp.name) / 'one.json', Path(self.temp.name) / 'two.json'
        first.write_text(json.dumps({'version': mutant_reuse.SCHEMA, 'records': [new, ancient, {'key': 'bad'}]}))
        second.write_text(json.dumps({'version': mutant_reuse.SCHEMA, 'records': [old]}))
        merged = mutant_reuse.merge([first, second, Path(self.temp.name) / 'absent.json'])
        self.assertEqual(list(merged), [key])
        self.assertEqual(merged[key]['commit'], 'b' * 40)
        result = subprocess.run([sys.executable, str(ROOT / 'scripts/mutant_reuse.py'), 'merge', '--out',
                                 str(self.out), str(first), str(second)], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(list(mutant_reuse.load_store(self.out)), [key])


class Runs(Fixture):
    """The stage itself, with the list runner and the replay replaced by recorders."""

    def setUp(self):
        super().setUp()
        (self.root / '.lake/build').mkdir(parents=True)
        (self.root / 'lake-manifest.json').write_text('{}\n')
        self.executed = []
        self.failing = set()
        self.manifest = {'apis': [API]}
        self.partition = ({GOAL}, {LIST: [TEXT_ROW, SAME_ROW, SCRIPT_ROW]})
        for patcher in (
                patch.object(verification, 'ROOT', self.root), patch.object(verification, 'AUDITOR_ROOT', self.root),
                patch.object(verification, 'mutation_partition', lambda manifest, count=1, index=0: self.partition),
                patch.object(verification, 'check_public_mutant_spans', lambda manifest, goals=None: None),
                patch.object(verification, 'public_mutants',
                             lambda manifest: {GOAL: [{'list': LIST, 'name': 'drop-check'}]}),
                patch.object(verification, 'mutation_apis', lambda manifest: {GOAL: API}),
                patch.object(verification, 'run', self.fake_runner),
                patch.object(verification, 'run_replay', self.fake_replay),
                patch.object(verification, 'subprocess', types.SimpleNamespace(
                    **{**vars(subprocess), 'run': lambda *a, **k: subprocess.CompletedProcess(a, 0)}))):
            patcher.start()
            self.addCleanup(patcher.stop)

    def fake_runner(self, args, **_):
        """Stands in for tests/audit/proofmut.sh in strict mode."""
        self.assertIn('PROOFMUT_STRICT=1', args)
        rows = [line for line in Path(args[-1]).read_text().split('\n') if line]
        verdicts = next((a.split('=', 1)[1] for a in args if a.startswith('PROOFMUT_VERDICTS=')), None)
        killed = 0
        for row in rows:
            fields = row.split('\t')
            self.executed.append('row ' + fields[0])
            if fields[0] in self.failing:
                verdict = 'SURVIVED'
            elif len(fields) > 5:
                verdict = 'SAME ok'
            else:
                verdict, killed = 'KILLED', killed + 1
            if verdicts:
                with open(verdicts, 'a') as handle:
                    handle.write(f'{fields[0]}\t{verdict}\t3\terror: ZlibF/Proof/a.lean:1:1: mismatch\n')
        if killed == 0 or any(row.split('\t')[0] in self.failing for row in rows):
            raise subprocess.CalledProcessError(1, args)

    def fake_replay(self, args, what):
        control = args[3] == args[4]
        self.executed.append(('control ' if control else 'replay ') + what)
        if what in self.failing:
            result = subprocess.CompletedProcess(args, 1 if control else 0, 'exact proof replayed: x\n', '')
        elif control:
            result = subprocess.CompletedProcess(args, 0, 'exact proof replayed: Fixture.exact; 3 dependencies\n', '')
        else:
            result = subprocess.CompletedProcess(args, 2, 'EXACT_PROOF_REJECTED: Fixture.exact: mismatch\n', '')
        result.peak = 5 << 20
        return result

    def stage(self, reuse, record=True):
        self.executed = []
        output = io.StringIO()
        session = None
        with redirect_stdout(output):
            if reuse or record:
                session = mutant_reuse.Session(self.root, self.root, self.store if reuse else None,
                                               self.out if record else None)
            try:
                verification.run_public_mutants(self.manifest, 1, 0, session)
            finally:
                self.printed = output.getvalue() + (session.summary() if session else '')
        return session

    ALL = ['control ' + GOAL, f'replay {GOAL}: drop-check', 'row drop-check', 'row same-shape', 'row paired']

    def seed(self):
        session = self.stage(reuse=False)
        self.assertEqual(self.executed, self.ALL)
        self.assertEqual((session.ran, session.reused), (5, 0))
        shutil.copyfile(self.out, self.store)
        return session

    def test_a_full_run_executes_everything_and_ignores_the_store(self):
        self.seed()
        # The store now holds a passing verdict for every unit; a full run reads none of them.
        for record in (True, False):
            session = self.stage(reuse=False, record=record)
            self.assertEqual(self.executed, self.ALL)
            self.assertNotIn('REUSED', self.printed)
            if session:
                self.assertIn('5 ran, 0 reused (full run)', self.printed)
        self.assertEqual(len(mutant_reuse.load_store(self.out)), 5)

    def test_without_a_session_the_runner_is_called_as_before(self):
        calls = []
        with patch.object(verification, 'run', lambda args, **k: calls.append(args)), redirect_stdout(io.StringIO()):
            verification.run_public_mutants(self.manifest, 1, 0)
        self.assertEqual([c[:-1] for c in calls], [['env', 'PROOFMUT_STRICT=1', 'bash', 'tests/audit/proofmut.sh']])

    def test_a_pre_check_reuses_every_unchanged_unit_and_says_so(self):
        self.seed()
        session = self.stage(reuse=True)
        self.assertEqual(self.executed, [])
        self.assertEqual((session.ran, session.reused), (0, 5))
        self.assertEqual(self.printed.count('\nREUSED '), 5)
        self.assertIn('0 ran, 5 reused (pre-check with reused verdicts; an accepted result needs a full run)',
                      self.printed)
        # The reused records travel on, with the commit and run that produced them.
        self.assertEqual(mutant_reuse.load_store(self.out), mutant_reuse.load_store(self.store))

    def test_an_empty_store_makes_a_pre_check_run_everything(self):
        session = self.stage(reuse=True)
        self.assertEqual(self.executed, self.ALL)
        self.assertEqual((session.ran, session.reused), (5, 0))

    def test_a_weakened_proof_module_runs_its_units_again(self):
        self.seed()
        self.edit('ZlibF/Proof/sub/c.lean', 'import ZlibF.Proof.b\n', 'import ZlibF.Proof.b\n-- weaker\n')
        self.stage(reuse=True)
        # Only the script row names sub/c; the replays are keyed by the whole library.
        self.assertEqual(self.executed, ['control ' + GOAL, f'replay {GOAL}: drop-check', 'row paired'])
        self.assertIn('REUSED', self.printed)

    def test_an_edited_row_runs_again(self):
        self.seed()
        self.partition = ({GOAL}, {LIST: [TEXT_ROW.replace('x + 2', 'x + 7'), SAME_ROW, SCRIPT_ROW]})
        with patch.object(verification, 'mutation_row', lambda reference: TEXT_ROW.replace('x + 2', 'x + 7').split('\t')):
            self.stage(reuse=True)
        self.assertEqual(self.executed, [f'replay {GOAL}: drop-check', 'row drop-check'])

    def test_a_unit_that_failed_is_not_recorded_and_runs_again(self):
        self.failing = {'paired'}
        with self.assertRaises(subprocess.CalledProcessError):
            self.stage(reuse=False)
        shutil.copyfile(self.out, self.store)
        self.assertEqual(sorted(r['kind'] for r in mutant_reuse.load_store(self.store).values()), ['control', 'replay'])
        self.failing = set()
        session = self.stage(reuse=True)
        # The list failed as a whole, so none of its rows was recorded: all three run again.
        self.assertEqual(self.executed, ['row drop-check', 'row same-shape', 'row paired'])
        self.assertEqual((session.ran, session.reused), (3, 2))

    def test_a_failing_replay_stops_the_stage_and_is_not_recorded(self):
        self.failing = {f'{GOAL}: drop-check'}
        with self.assertRaises(verification.Rejected):
            self.stage(reuse=False)
        self.assertEqual([r['kind'] for r in mutant_reuse.load_store(self.out).values()], ['control'])
        self.failing = {GOAL}
        with self.assertRaises(verification.Rejected):
            self.stage(reuse=False)
        self.assertEqual(mutant_reuse.load_store(self.out), {})

    def test_a_same_row_never_runs_without_a_killed_row_beside_it(self):
        self.seed()
        self.partition = ({GOAL}, {LIST: [TEXT_ROW, SAME_ROW.replace('commutes', 'new reason'), SCRIPT_ROW]})
        session = self.stage(reuse=True)
        self.assertEqual(self.executed, ['row drop-check', 'row same-shape'])
        self.assertEqual((session.ran, session.reused), (2, 3))
        self.assertIn('runs again beside the same: rows', self.printed)

    def test_verdicts_that_do_not_match_the_rows_asked_for_are_not_recorded(self):
        original = self.fake_runner

        def shuffled(args, **k):
            original(args, **k)
            for a in args:
                if a.startswith('PROOFMUT_VERDICTS='):
                    path = Path(a.split('=', 1)[1])
                    path.write_text(''.join(reversed(path.read_text().splitlines(keepends=True))))
        with patch.object(verification, 'run', shuffled):
            self.stage(reuse=False)
        self.assertEqual(sorted(r['kind'] for r in mutant_reuse.load_store(self.out).values()), ['control', 'replay'])

    def test_sorry_in_the_tree_disables_row_reuse(self):
        self.seed()
        self.edit('ZlibF/Proof/other.lean', 'trivial', 'trivial -- no sorry here')
        self.stage(reuse=True)
        self.assertEqual(self.executed, self.ALL)  # the replays: the library changed


class Partition(unittest.TestCase):
    def test_every_unit_is_keyed_once_across_shards(self):
        """Sharding with reuse: each unit of the real partition is one shard's, ran or reused."""
        manifest = json.loads((ROOT / 'tests/audit/public-api.json').read_text())
        whole_goals, whole_lists = verification.mutation_partition(manifest)
        shards = [verification.mutation_partition(manifest, 20, index) for index in range(20)]
        self.assertEqual(Counter(g for goals, _ in shards for g in goals), Counter({g: 1 for g in whole_goals}))
        self.assertEqual(Counter((p, r) for _, lists in shards for p, rows in lists.items() for r in rows),
                         Counter({(p, r): 1 for p, rows in whole_lists.items() for r in rows}))
        tree = mutant_reuse.Tree(ROOT)
        base = mutant_reuse.base_digest(tree, ROOT)
        keys = [mutant_reuse.row_key(tree, base, path, row) for path, rows in whole_lists.items() for row in rows
                if '\tscript:' not in row]
        script = next((path, row) for path, rows in whole_lists.items() for row in rows if '\tscript:' in row)
        keys.append(mutant_reuse.row_key(tree, base, *script))
        apis, targets = verification.mutation_apis(manifest), verification.public_mutants(manifest)
        for goal, references in targets.items():
            keys.append(mutant_reuse.control_key(tree, base, goal, apis[goal]))
            keys += [mutant_reuse.replay_key(tree, base, goal, apis[goal], r['list'],
                                             '\t'.join(verification.mutation_row(r))) for r in references]
        self.assertEqual(len(keys), len(set(keys)))
        self.assertGreater(len(keys), 500)

    def test_packing_by_duration_keeps_every_unit_once_and_balances(self):
        manifest = json.loads((ROOT / 'tests/audit/public-api.json').read_text())
        whole_goals, whole_lists = verification.mutation_partition(manifest)
        expected = Counter({(p, r): 1 for p, rows in whole_lists.items() for r in rows})
        for seconds in (None, {}, {'row tests/proof-mutants/gz-sequence.tsv: gzputs-mode-check-dropped': 80000},
                        {'control ZlibF.Spec.Public.Goal.deflateCopy': 0}):
            with self.subTest(seconds=seconds):
                context = patch.object(verification, 'unit_seconds', lambda: seconds) if seconds is not None \
                    else patch.object(verification, 'DEFAULT_SECONDS', 60.0)
                with context:
                    for count in (1, 3, 20):
                        shards = [verification.mutation_partition(manifest, count, i) for i in range(count)]
                        self.assertEqual(Counter(g for goals, _ in shards for g in goals),
                                         Counter({g: 1 for g in whole_goals}))
                        self.assertEqual(Counter((p, r) for _, lists in shards for p, rows in lists.items()
                                                 for r in rows), expected)
                        for _, lists in shards:
                            for path, rows in lists.items():
                                # Strict mode needs a row to kill in every list a shard runs.
                                self.assertTrue(any('\tsame:' not in row for row in rows), path)
        # With the recorded durations no shard is predicted far above the mean.
        loads = verification.predicted_loads(manifest, 20)
        largest = max(verification.unit_seconds().values(), default=verification.DEFAULT_SECONDS)
        self.assertLessEqual(max(loads), sum(loads) / 20 + 2 * max(largest, 1800))

    def test_durations_cannot_drop_a_unit_and_a_malformed_file_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'tests/proof-mutants').mkdir(parents=True)
            (root / 'tests/proof-mutants/api-boundary.tsv').write_text('k\tZ.lean\ta\tb\tM\n')
            (root / 'tests/proof-mutants/mixed.tsv').write_text(
                'equivalent\tZ.lean\ta\tb\tM\tsame:unused\n' + ''.join(f'k{i}\tZ.lean\ta\tb{i}\tM\n' for i in range(5)))
            durations = root / verification.DURATIONS
            with patch.object(verification, 'ROOT', root), patch.object(verification, 'public_mutants', lambda m: {}), \
                    patch.object(verification, 'SAFETY_MUTANT_LISTS', ('tests/proof-mutants/mixed.tsv',)):
                for text in (None, '{"version": 1, "seconds": {}}',
                             '{"version": 1, "seconds": {"row tests/proof-mutants/mixed.tsv: k3": 5000, "stale": 1}}'):
                    if text is not None:
                        durations.write_text(text)
                    shards = [verification.mutation_partition({}, 4, i)[1] for i in range(4)]
                    self.assertEqual(sum(len(s.get('tests/proof-mutants/mixed.tsv', [])) for s in shards), 6)
                    self.assertEqual(sum(len(s.get('tests/proof-mutants/api-boundary.tsv', [])) for s in shards), 1)
                    for shard in shards:
                        rows = shard.get('tests/proof-mutants/mixed.tsv', [])
                        self.assertTrue(not rows or any('same:' not in row for row in rows))
                for text in ('[]', '{"version": 2, "seconds": {}}', '{"version": 1, "seconds": {"u": -1}}',
                             '{"version": 1, "seconds": {"u": "long"}}', '{"version": 1, "seconds": {"u": true}}',
                             '{"version": 1, "seconds": {}, "skip": ["u"]}'):
                    durations.write_text(text)
                    with self.subTest(text=text), self.assertRaises(verification.Rejected):
                        verification.mutation_partition({}, 4, 0)

    def test_durations_are_read_from_stores(self):
        record = {'schema': mutant_reuse.SCHEMA, 'key': 'a' * 64, 'kind': 'row', 'unit': 'row l: n', 'verdict': 'KILLED',
                  'detail': '', 'peak_mb': 0, 'seconds': 12, 'commit': 'c', 'run': '1/1', 'repository': 'o/r',
                  'time': '2026-11-15T00:00:00Z'}
        newer = {**record, 'key': 'b' * 64, 'seconds': 40, 'time': '2026-11-16T00:00:00Z'}
        with tempfile.TemporaryDirectory() as directory:
            store = Path(directory) / 's.json'
            store.write_text(json.dumps({'version': mutant_reuse.SCHEMA, 'records': [record, newer]}))
            self.assertEqual(mutant_reuse.durations([store]), {'row l: n': 40})
            out = Path(directory) / 'd.json'
            subprocess.run([sys.executable, str(ROOT / 'scripts/mutant_reuse.py'), 'durations', '--out', str(out),
                            str(store)], check=True, capture_output=True)
            with patch.object(verification, 'ROOT', Path(directory)), \
                    patch.object(verification, 'DURATIONS', Path('d.json')):
                self.assertEqual(verification.unit_seconds(), {'row l: n': 40})


if __name__ == '__main__':
    unittest.main()

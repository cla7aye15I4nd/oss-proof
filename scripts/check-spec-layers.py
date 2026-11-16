#!/usr/bin/env python3
"""Check the layers of the specification (docs/design/safety-functional-split.md).

Layout. Directly under ZlibF/Spec/ there are only the folders Safety/, Functional/ and Common/, and at
most the three root import files Safety.lean, Functional.lean and Common.lean.

1. A safety or common module does not import, even transitively, a functional module. The safety
   modules are ZlibF/Spec/Safety.lean and those under ZlibF/Spec/Safety/; the common modules are
   ZlibF/Spec/Common.lean and those under ZlibF/Spec/Common/; the functional modules are
   ZlibF/Spec/Functional.lean and those under ZlibF/Spec/Functional/. Then reading Spec/Safety and
   what it imports tells a reader the safety target. The planned target also includes the two full
   contracts Goal.compressBound and Goal.compressBound_z, which live under Spec/Functional by design.

2. A common module does not import, even transitively, a safety module. Common lies below both.

3. No module under ZlibF/Spec/ imports a module under ZlibF/Proof/, even transitively: the walk
   follows every import (Spec, Math, Runtime, translation), so an edge hidden behind a Math module
   or another Spec module is found. Then the statement of a goal is read in ZlibF/Spec/ (and in the
   translation, the runtime and the mathematics it names), not in a proof module.

4. No module under ZlibF/Math/ imports a module under ZlibF/Proof/, except the imports listed in
   MATH_PROOF_IMPORTS. The list may only shrink: a listed import that no longer exists is an error, so it
   is deleted when its import goes. Rule 3 still holds for every Spec module, also through these Math
   modules.

5. No goal is defined under ZlibF/Spec/Common/: every goal, public or internal, is defined under
   Safety/ or Functional/. The check reads each line of a Common module that starts with `def Goal.`
   or `abbrev Goal.`, and qualifies the name with the enclosing namespaces for the message.

There is no other allowlist.
"""
import functools
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPEC = ROOT / 'ZlibF/Spec'
LAYERS = ('Safety', 'Functional', 'Common')

# Math -> Proof imports that remain (shrink-only). These Math modules import proof lemmas, not definitions;
# moving those lemmas is later work.
MATH_PROOF_IMPORTS = {
    'ZlibF.Math.DeflateDynamicBlock': (
        'ZlibF.Proof.«trees.c.dynamic-header»',
    ),
    'ZlibF.Math.DeflateFixedPayload': (
        'ZlibF.Proof.«trees.c.compress-match»',
    ),
    'ZlibF.Math.DeflateFlushMarkers': (
        'ZlibF.Proof.«trees.c.stored-header»',
    ),
    'ZlibF.Math.DeflateForest': (
        'ZlibF.Proof.«trees.c.heap.gbtree»',
    ),
    'ZlibF.Math.DeflateHeader': (
        'ZlibF.Proof.«trees.c.runs»',
    ),
    'ZlibF.Math.DeflateHeap': (
        'ZlibF.Proof.«trees.c.heap.ord»',
        'ZlibF.Proof.«trees.c.heap.gbmath»',
    ),
    'ZlibF.Math.DeflateHeapRemove': (
        'ZlibF.Proof.«trees.c.heap.pqrun»',
    ),
    'ZlibF.Math.DeflateHuffmanChain': (
        'ZlibF.Proof.«trees.c.heap.gbclk»',
    ),
    'ZlibF.Math.DeflateKraft': (
        'ZlibF.Proof.«trees.c.heap.gbsym»',
        'ZlibF.Proof.«inftrees.c.link»',
    ),
    'ZlibF.Math.DeflateLeafRank': (
        'ZlibF.Proof.«trees.c.heap.gbmath»',
    ),
    'ZlibF.Math.DeflatePayload': (
        'ZlibF.Proof.«trees.c.tally»',
        'ZlibF.Proof.«trees.c.runs»',
    ),
    'ZlibF.Math.DeflateRankedLengths': (
        'ZlibF.Proof.«trees.c.heap.gbclk»',
    ),
    'ZlibF.Math.DeflateRunDecode': (
        'ZlibF.Proof.«inffast.c.sig»',
    ),
    'ZlibF.Math.DeflateRunSupport': (
        'ZlibF.Proof.«trees.c.runs»',
    ),
    'ZlibF.Math.DeflateZlibEncoding': (
        'ZlibF.Proof.Format.Deflate',
    ),
    'ZlibF.Math.HuffmanCost': (
        'ZlibF.Proof.«trees.c.heap.gbmath»',
    ),
    'ZlibF.Math.HuffmanReference': (
        'ZlibF.Proof.«trees.c.heap.gbmath»',
    ),
    'ZlibF.Math.InflateCanonicalDecode': (
        'ZlibF.Proof.Format.Huffman',
    ),
    'ZlibF.Math.InflateDecodeBits': (
        'ZlibF.Proof.«inftrees.c.geom»',
        'ZlibF.Proof.«inffast.c.sig»',
    ),
    'ZlibF.Math.InflateFastMatchHistory': (
        'ZlibF.Proof.«inflate.c.ring»',
        'ZlibF.Proof.«inffast.c.match»',
        'ZlibF.Proof.«deflate.c.base»',
    ),
    'ZlibF.Math.InflateHeldBits': (
        'ZlibF.Proof.«inffast.c.sig»',
    ),
    'ZlibF.Math.InflatePrefixes': (
        'ZlibF.Proof.Format.Wrapper',
        'ZlibF.Proof.«inffast.c.sig»',
    ),
    'ZlibF.Math.InflateTableCoverage': (
        'ZlibF.Proof.«inftrees.c.cover.group»',
    ),
    'ZlibF.Math.InflateTableGeometry': (
        'ZlibF.Proof.«inftrees.c.step»',
        'ZlibF.Proof.«inftrees.c.cover.root»',
    ),
    'ZlibF.Math.code-length-prefix': (
        'ZlibF.Proof.«inftrees.c.decode.semantics»',
    ),
    'ZlibF.Math.inflate-dictionary-window-token': (
        'ZlibF.Proof.Format.Huffman',
    ),
    'ZlibF.Math.inflate-header-alphabet': (
        'ZlibF.Proof.«inflate.c.main.table6»',
    ),
    'ZlibF.Math.inflate-meaning-wrap': (
        'ZlibF.Proof.Format.Wrapper',
    ),
}


def module_path(name):
    return ROOT / (name.replace('.', '/').replace('«', '').replace('»', '') + '.lean')


def module_name(path):
    return '.'.join(path.relative_to(ROOT).with_suffix('').parts)


@functools.lru_cache(maxsize=None)
def imports(name):
    path = module_path(name)
    if not path.is_file():
        return []
    found = []
    for line in path.read_text().splitlines():
        match = re.match(r'import\s+(\S+)', line)
        if match:
            found.append(match.group(1))
        elif line.strip() and not line.startswith('--') and not line.startswith('prelude'):
            break
    return tuple(m for m in found if m.startswith('ZlibF.'))


def plain(name):
    return name.replace('«', '').replace('»', '')


def layer(name):
    """The layer of a Spec module (Safety, Functional, Common), else None."""
    for part in LAYERS:
        prefix = 'ZlibF.Spec.' + part
        if name == prefix or name.startswith(prefix + '.'):
            return part
    return None


def proof(name):
    return name.startswith('ZlibF.Proof.') or name == 'ZlibF.Proof'


def spec_modules():
    return sorted(module_name(p) for p in SPEC.rglob('*.lean'))


def closure(root):
    """Every module the root imports, even transitively, with the importer that reached it first."""
    parent = {root: None}
    stack = [root]
    while stack:
        name = stack.pop()
        for child in imports(name):
            if child not in parent:
                parent[child] = name
                stack.append(child)
    return parent


def chain(parent, name):
    names = [name]
    while parent[names[-1]] is not None:
        names.append(parent[names[-1]])
    return ' <- '.join(names)


def check_layout(errors):
    allowed = set(LAYERS) | {part + '.lean' for part in LAYERS}
    for entry in sorted(SPEC.iterdir()):
        if entry.name not in allowed or (entry.is_dir() != (entry.suffix == '')):
            errors.append(f'ZlibF/Spec/{entry.name}: only the folders Safety/, Functional/ and Common/ '
                          'and their root import files may be directly under ZlibF/Spec')


def check_modules(errors):
    modules = spec_modules()
    for root in modules:
        if layer(root) is None:
            continue
        parent = closure(root)
        reached = sorted(parent)
        if layer(root) in ('Safety', 'Common'):
            bad = [n for n in reached if layer(n) == 'Functional']
            if bad:
                errors.append(f'{root} imports functional {bad[0]}: ' + chain(parent, bad[0]))
        if layer(root) == 'Common':
            bad = [n for n in reached if layer(n) == 'Safety']
            if bad:
                errors.append(f'{root} imports safety {bad[0]}: ' + chain(parent, bad[0]))
        bad = [n for n in reached if proof(plain(n))]
        if bad:
            errors.append(f'{root} imports the proof module {bad[0]}: ' + chain(parent, bad[0]))
    return len(modules)


def check_common_goals(errors):
    for path in sorted((SPEC / 'Common').rglob('*.lean')):
        spaces = []
        for number, line in enumerate(path.read_text().splitlines(), 1):
            match = re.match(r'namespace\s+(\S+)', line)
            if match:
                spaces.append(match.group(1))
            match = re.match(r'end\s+(\S+)\s*$', line)
            if match and spaces and spaces[-1] == match.group(1):
                spaces.pop()
            match = re.match(r'(?:def|abbrev)\s+(Goal\.\S+)', line)
            if match:
                name = '.'.join(spaces + [match.group(1)])
                errors.append(f'{path.relative_to(ROOT)}:{number}: the goal {name} is defined '
                              'under Spec/Common: move it to Spec/Safety or Spec/Functional')


def check_math(errors):
    allowed = {(src, plain(dst)) for src, dsts in MATH_PROOF_IMPORTS.items() for dst in dsts}
    found = set()
    for path in sorted((ROOT / 'ZlibF/Math').rglob('*.lean')):
        src = module_name(path)
        for dst in imports(src):
            if proof(plain(dst)):
                found.add((src, plain(dst)))
                if (src, plain(dst)) not in allowed:
                    errors.append(f'{src} imports the proof module {dst}: a Math module may not')
    for src, dst in sorted(allowed - found):
        errors.append(f'listed import {src} -> {dst} no longer exists: delete it from MATH_PROOF_IMPORTS')
    return len(found)


def main():
    errors = []
    check_layout(errors)
    count = check_modules(errors)
    remaining = check_math(errors)
    check_common_goals(errors)
    if errors:
        print('Specification layer check failed (docs/design/safety-functional-split.md):')
        for error in errors:
            print('  ' + error)
        return 1
    print(f'specification layers: {count} modules under ZlibF/Spec; safety and common import no functional '
          'module, common imports no safety module and defines no goal, and none imports a proof module; '
          f'{remaining} listed Math -> Proof imports remain ({len(MATH_PROOF_IMPORTS)} modules)')
    return 0


if __name__ == '__main__':
    sys.exit(main())

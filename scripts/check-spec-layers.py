#!/usr/bin/env python3
"""Check the layers of the specification (docs/design/safety-functional-split.md).

Two rules.

1. A safety or common module must not import, even transitively, a functional module. The safety and
   common modules are those under ZlibF/Spec/Safety/ and ZlibF/Spec/Common/, and the common modules
   COMMON at the top of ZlibF/Spec/. The functional modules are those under ZlibF/Spec/Functional/.
   Then reading Spec/Safety and what it imports tells a reader the whole current target.

2. No module under ZlibF/Spec/ imports a module under ZlibF/Proof/. Then the statement of a goal is
   read in ZlibF/Spec/ (and in the translation and the runtime it names), not in a proof module.

PROOF_IMPORTS lists the Spec -> Proof imports that are still to be removed, each with its reason. The
list may only shrink: an entry whose import no longer exists is an error, so it is deleted when its
import goes.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

# Common modules at the top of ZlibF/Spec/, checked like Spec/Safety and Spec/Common.
COMMON = ('ZlibF.Spec.Common',)

# importer -> (the Proof modules it still imports, reason). Each import is removed by a later batch.
PROOF_IMPORTS = {}


def module_path(name):
    return ROOT / (name.replace('.', '/').replace('«', '').replace('»', '') + '.lean')


def module_name(path):
    return '.'.join(path.relative_to(ROOT).with_suffix('').parts)


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
    return [m for m in found if m.startswith('ZlibF.')]


def plain(name):
    return name.replace('«', '').replace('»', '')


def functional(name):
    return name.startswith('ZlibF.Spec.Functional.') or name == 'ZlibF.Spec.Functional'


def proof(name):
    return name.startswith('ZlibF.Proof.') or name == 'ZlibF.Proof'


def spec_modules():
    return sorted(module_name(p) for p in (ROOT / 'ZlibF/Spec').rglob('*.lean'))


def check_layers(errors):
    roots = sorted(module_name(p) for d in ('Safety', 'Common')
                   for p in (ROOT / 'ZlibF/Spec' / d).rglob('*.lean'))
    roots += [m for m in COMMON if module_path(m).is_file()]
    for name in COMMON:
        if not module_path(name).is_file():
            errors.append(f'common module {name} does not exist: delete it from COMMON')
    for root in roots:
        parent = {root: None}
        stack = [root]
        while stack:
            name = stack.pop()
            for child in imports(name):
                if child in parent:
                    continue
                parent[child] = name
                stack.append(child)
        for name in sorted(n for n in parent if functional(n)):
            chain = [name]
            while parent[chain[-1]] is not None:
                chain.append(parent[chain[-1]])
            errors.append(f'{root} imports functional {name}: ' + ' <- '.join(chain))
            break
    return len(roots)


def check_proof_imports(errors):
    allowed = {(plain(src), plain(dst)) for src, (dsts, _) in PROOF_IMPORTS.items() for dst in dsts}
    found = set()
    for src in spec_modules():
        for dst in imports(src):
            if proof(dst):
                found.add((plain(src), plain(dst)))
                if (plain(src), plain(dst)) not in allowed:
                    errors.append(f'{src} imports the proof module {dst}: a specification module may not')
    for src, (dsts, reason) in PROOF_IMPORTS.items():
        for dst in dsts:
            if (plain(src), plain(dst)) not in found:
                errors.append(f'listed import {src} -> {dst} no longer exists: delete it ({reason})')
    return len(found)


def main():
    errors = []
    roots = check_layers(errors)
    remaining = check_proof_imports(errors)
    if errors:
        print('Specification layer check failed (docs/design/safety-functional-split.md):')
        for error in errors:
            print('  ' + error)
        return 1
    print(f'specification layers: {roots} safety and common modules import no functional module; '
          f'{remaining} listed Spec -> Proof imports remain ({len(PROOF_IMPORTS)} modules)')
    return 0


if __name__ == '__main__':
    sys.exit(main())

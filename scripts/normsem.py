#!/usr/bin/env python3
"""Compare two audit reports of tests/audit/Audit.lean across a move of definitions between modules.

Usage: python3 scripts/normsem.py <base report> <head report>

What it compares:
- `trusted`, `target` and `statement` lines: exactly, unnormalised. They hold the type and value hash of every
  definition in the audited closure, every goal and the exact type of every listed theorem; they must be
  identical, as multisets of lines.
- `semantic` lines (the full kernel syntax of a definition), one per declaration name: exactly, or else after one
  normalisation. The normalisation strips the defining-module part of macro-scoped binder names: in a name
  that contains the component `_@` (a hygienic name, such as `x._@.ZlibF.Spec.Public.GzState.1664183659._hyg.3`),
  each run of string components that starts with `ZlibF` and ends before the next numeric component (the module
  name) is removed. Lean writes the module that elaborated a binder into these names, so moving a definition to
  another module changes them. Binder names do not change what a kernel term means.

Why this cannot hide a statement change: the normalisation touches only binder names inside `semantic` lines.
The hashes of the `trusted` lines, and the `target` and `statement` lines, are compared without it and must be
identical; a changed type or value changes them. Every other part of a `semantic` line (constants, universe
levels, literals, the structure of the term, the numbers in the hygienic names) must also be identical.

Exit code 0 when the reports agree, 1 otherwise.
"""
import hashlib
import json
import sys

KINDS = ('trusted ', 'target ', 'statement ')


def name_parts(value):
    """The components of a Name in the report's encoding, or None if `value` is not a Name."""
    parts = []
    while value != 0:
        if not (isinstance(value, list) and len(value) == 3 and value[0] in (1, 2)):
            return None
        if value[0] == 1 and not isinstance(value[2], str) or value[0] == 2 and not isinstance(value[2], int):
            return None
        parts.append(value[2])
        value = value[1]
    return parts[::-1]


def encode(parts):
    value = 0
    for part in parts:
        value = [1 if isinstance(part, str) else 2, value, part]
    return value


def strip_modules(parts):
    out, i = [], 0
    while i < len(parts):
        if parts[i] == 'ZlibF':
            while i < len(parts) and isinstance(parts[i], str):
                i += 1
            out.append('<module>')
        else:
            out.append(parts[i])
            i += 1
    return out


def normalise(value):
    if isinstance(value, list):
        parts = name_parts(value) if value and value[0] in (1, 2) else None
        if parts is not None and '_@' in parts:
            return encode(strip_modules(parts))
        return [normalise(item) for item in value]
    if isinstance(value, dict):
        return {key: normalise(item) for key, item in value.items()}
    return value


def digest(text):
    return hashlib.sha256(text.encode('utf-8')).hexdigest()


def read(path, keys=None):
    """Exact lines of the three kinds as a digest multiset, and semantic lines by name (digest of the line,
    or of its normal form for the names in `keys`)."""
    exact, semantic = {}, {}
    with open(path, encoding='utf-8') as report:
        for line in report:
            line = line.rstrip('\n')
            if line.startswith(KINDS):
                key = digest(line)
                exact[key] = exact.get(key, 0) + 1
            elif line.startswith('semantic '):
                record = json.loads(line[len('semantic '):])
                name = record['name']
                if name in semantic:
                    raise SystemExit(f'{path}: two semantic lines for {name}')
                if keys is not None and name in keys:
                    semantic[name] = digest(json.dumps(normalise(record), sort_keys=True))
                else:
                    semantic[name] = digest(line)
    return exact, semantic


def main(base_path, head_path):
    base_exact, base_sem = read(base_path)
    head_exact, head_sem = read(head_path)
    ok = True
    if base_exact != head_exact:
        ok = False
        print('trusted, target or statement lines differ')
    exact_lines = sum(base_exact.values())
    if set(base_sem) != set(head_sem):
        ok = False
        print('semantic lines differ in their names:', sorted(set(base_sem) ^ set(head_sem))[:20])
    differing = {name for name in base_sem if name in head_sem and base_sem[name] != head_sem[name]}
    still = set()
    if differing:
        _, base_norm = read(base_path, differing)
        _, head_norm = read(head_path, differing)
        still = {name for name in differing if base_norm[name] != head_norm[name]}
    if still:
        ok = False
        print('semantic lines that differ after normalisation:', sorted(still)[:20])
    print(f'trusted, target and statement lines: {exact_lines} base, {sum(head_exact.values())} head, '
          f'{"identical" if base_exact == head_exact else "DIFFERENT"}')
    print(f'semantic lines: {len(base_sem)} base, {len(head_sem)} head; '
          f'{len(base_sem) - len(differing)} identical, {len(differing) - len(still)} identical after '
          f'normalisation, {len(still)} different')
    return 0 if ok else 1


if __name__ == '__main__':
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    sys.exit(main(sys.argv[1], sys.argv[2]))

#!/usr/bin/env python3
"""No option and no build setting that weakens checking.

A declaration added without the kernel check (`debug.skipKernelTC`) or elaborated under a weakened
option looks like any other in the compiled environment, so the sources are checked by allow-list,
not by a list of known bad spellings:

1. Every `set_option` in the library (`ZlibF.lean`, `ZlibF/`) and in the Lean files CI runs
   (`scripts/*.lean`, `tests/audit/`, `tests/lean/`, `tests/results-check/`) names an option of
   ALLOWED_OPTIONS, or one under `linter.`. The name is read with `«»` quotes removed, so
   `«debug».skipKernelTC` is `debug.skipKernelTC` and is rejected.
2. The two Lake configurations are `lakefile.toml` files with only the keys of LAKEFILE_KEYS and
   TESTS_LAKEFILE_KEYS (so no `leanOptions`, `moreLeanArgs`, `weakLeanArgs`, `plugins`, `dynlibs`,
   `precompileModules`); no `lakefile.lean` exists beside either; the test project requires only the
   library, by path `..`.

Exit 0 when both hold, 1 with the offending places otherwise.
    python3 scripts/check-options.py [root]
"""

import re
import sys
import tomllib
from pathlib import Path

ALLOWED_OPTIONS = {"autoImplicit", "maxHeartbeats", "maxRecDepth", "hygiene"}
ALLOWED_PREFIXES = ("linter.",)

LAKEFILE_KEYS = {"": {"name", "version", "defaultTargets", "lean_lib"}, "lean_lib": {"name", "roots"}}
TESTS_LAKEFILE_KEYS = {"": {"name", "version", "require", "lean_lib", "lean_exe"},
                       "require": {"name", "path"}, "lean_lib": {"name", "srcDir"},
                       "lean_exe": {"name", "root", "srcDir"}}

SET_OPTION = re.compile(r"\bset_option\s+(\S+)")


def lean_files(root: Path) -> list[Path]:
    files = [root / "ZlibF.lean"] + sorted((root / "ZlibF").rglob("*.lean"))
    files += sorted((root / "scripts").glob("*.lean"))
    for sub in ("tests/audit", "tests/lean", "tests/results-check"):
        files += sorted((root / sub).rglob("*.lean"))
    return [f for f in files if f.is_file()]


def option_errors(root: Path) -> list[str]:
    errors = []
    for f in lean_files(root):
        for number, line in enumerate(f.read_text().splitlines(), 1):
            for match in SET_OPTION.finditer(line):
                name = match.group(1).replace("«", "").replace("»", "")
                if name not in ALLOWED_OPTIONS and not name.startswith(ALLOWED_PREFIXES):
                    errors.append(f"{f.relative_to(root)}:{number}: option {name} is not allowed")
    return errors


def table_errors(path: str, data: dict, allowed: dict) -> list[str]:
    errors = [f"{path}: key {k} is not allowed" for k in data if k not in allowed[""]]
    for table, keys in allowed.items():
        if not table:
            continue
        entries = data.get(table, [])
        for entry in entries if isinstance(entries, list) else [entries]:
            if not isinstance(entry, dict):
                errors.append(f"{path}: {table} is not a table")
                continue
            errors += [f"{path}: [[{table}]] key {k} is not allowed" for k in entry if k not in keys]
    return errors


def lakefile_errors(root: Path) -> list[str]:
    errors = []
    for lean_config in (root / "lakefile.lean", root / "tests/lakefile.lean"):
        if lean_config.exists():
            errors.append(f"{lean_config.relative_to(root)}: a Lean Lake configuration is not allowed")
    for path, allowed in (("lakefile.toml", LAKEFILE_KEYS), ("tests/lakefile.toml", TESTS_LAKEFILE_KEYS)):
        data = tomllib.loads((root / path).read_text())
        errors += table_errors(path, data, allowed)
        if path.startswith("tests/") and data.get("require", []) != [{"name": "ZlibF", "path": ".."}]:
            errors.append(f"{path}: the test project may require only the library, by path ..")
    return errors


def main() -> int:
    root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parents[1]
    errors = option_errors(root) + lakefile_errors(root)
    for e in errors:
        print(e)
    if errors:
        print("option or build setting that may weaken checking found")
        return 1
    print("options: " + ", ".join(sorted(ALLOWED_OPTIONS)) + " and linter.* only; "
          "Lake configurations: allowed keys only")
    return 0


if __name__ == "__main__":
    sys.exit(main())

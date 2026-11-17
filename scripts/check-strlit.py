#!/usr/bin/env python3
"""Every C string literal of the translations is in the runtime table `strTable`.

`strLitRef s` is a fault when `s` is not in `strTable` (`ZlibF/Runtime/Schema.lean`), so a missing literal turns a
C path that returns into a model path that faults. This check reads `ZlibF/Zlib/*.lean`, comments removed, and
fails on any literal not in the table. It reads:

* the quoted literal passed to a helper of `HELPERS`: `strLit` and `strLitRef`, and the helpers that pass their
  text on to them (`setMsg`, `badMode`, `badData`: `strm->msg = "..."`);
* the texts of the table `z_errmsg`, which `zError` passes to `strLit`;
* `ZLIB_VERSION`.

The check is closed in two ways, so that a literal cannot go unread:

* a use of a helper with an argument that is not a quoted literal must be listed in `PASS_THROUGH` (a helper that
  forwards its own parameter, `ZLIB_VERSION`, an entry of `z_errmsg`);
* a definition of `ZlibF/Zlib/*.lean` with a `String` in its signature must be a helper of `HELPERS` or be listed
  in `NOT_C_LITERALS` (its text is not a C string literal).
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from lean_sorry import strip  # noqa: E402

STRING = r'"((?:[^"\\]|\\.)*)"'
ARGUMENT = r"(?:[\w.«»']+|\([^()\n]*\))"

# Helper -> the number of arguments before the text.
HELPERS = {"strLit": 0, "strLitRef": 0, "setMsg": 1, "badMode": 1, "badData": 1}

# Reviewed uses of a helper whose text argument is not a quoted literal: (file, line with spaces normalised).
PASS_THROUGH = {
    ("ZlibF/Zlib/zutil.c.lean", "strLit ZLIB_VERSION"),
    ("ZlibF/Zlib/zutil.c.lean", "| some s => strLit s"),  # an entry of z_errmsg
    ("ZlibF/Zlib/gzread.c.lean", "let ver ← strLit ZLIB_VERSION"),
    ("ZlibF/Zlib/gzwrite.c.lean", "let ver ← strLit ZLIB_VERSION"),
    ("ZlibF/Zlib/uncompr.c.lean", "let ver ← Zlib.GzFs.strLit ZLIB_VERSION"),
    ("ZlibF/Zlib/inflate.c.lean", "let p ← Zlib.Zutil.strLit s"),  # setMsg
    ("ZlibF/Zlib/inflate.c.lean", "setMsg c.strm msg"),  # badMode
    ("ZlibF/Zlib/infback.c.lean", "setMsg c.strm msg"),  # badMode
    ("ZlibF/Zlib/inffast.c.lean", "let p ← Zlib.Zutil.strLit msg"),  # badData
}

# Definitions with a `String` in the signature whose text is not a C string literal.
NOT_C_LITERALS = {
    "gub",  # the description of a fault
    "strerrorText",  # the text of strerror(), made by the C library
    "z_errmsg",  # the table itself: its texts are read below
    "formatGo",  # returns the description of a format the model does not cover
}

DEFINITION = re.compile(r"^[ \t]*(?:(?:private|protected|noncomputable)\s+|@\[[^\]]*\]\s*)*(?:def|abbrev)\s+(\S+)"
                        r"((?:[^:\n]|:(?!=)|\n(?![ \t]*\n))*?):=", re.M)


def unescape(s: str) -> str:
    return bytes(s, "utf-8").decode("unicode_escape")


def table() -> list[str]:
    text = (ROOT / "ZlibF/Runtime/Schema.lean").read_text()
    start = text.index("def strTable : Array String := #[")
    end = text.index("\n]", start)
    return [unescape(m) for m in re.findall(STRING, text[start:end])]


def line_of(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def scan(rel: str, source: str, found: dict[str, list[str]], errors: list[str]) -> None:
    """Read one translation: its literals go to `found`, what cannot be read goes to `errors`."""
    code = strip(source, keep_literals=True)
    # An `open M (a b c)` names helpers and passes nothing: blank it, keeping the line breaks.
    code = re.sub(r"^open\b[^\n(]*\([^)]*\)", lambda m: re.sub(r"[^\n]", " ", m.group(0)), code, flags=re.M)
    lines = code.split("\n")
    read = set()  # (line, column) of each helper use whose literal was read
    for name, before in HELPERS.items():
        call = re.compile(r"(?<![\w.'])(?:[\w«»]+\.)*" + name + r"(?![\w'])" + (r"\s+" + ARGUMENT) * before
                          + r"\s+" + STRING)
        for m in call.finditer(code):
            number = line_of(code, m.start())
            found.setdefault(unescape(m.group(1)), []).append(f"{rel}:{number}")
            read.add((number, m.start() - (code.rfind("\n", 0, m.start()) + 1)))
    use = re.compile(r"(?<![\w.'])(?:[\w«»]+\.)*(?:" + "|".join(HELPERS) + r")(?![\w'])")
    for number, line in enumerate(lines, 1):
        text = " ".join(line.split())
        if re.match(r"(?:(?:private|protected|noncomputable) )*(?:def|abbrev) ", text):
            continue
        if (rel, text) in PASS_THROUGH:
            continue
        for m in use.finditer(line):
            if (number, m.start()) not in read:
                errors.append(f"{rel}:{number}: the text passed to {m.group(0)} is not a quoted literal and the "
                              f"use is not listed in PASS_THROUGH: {text}")
    for m in DEFINITION.finditer(code):
        name = m.group(1).split(".")[-1]
        if re.search(r"\bString\b", m.group(2)) and name not in HELPERS and name not in NOT_C_LITERALS:
            errors.append(f"{rel}:{line_of(code, m.start())}: the definition {m.group(1)} takes or returns a "
                          "String: add it to HELPERS if the text is a C string literal, else to NOT_C_LITERALS")
    errmsg = re.search(r"def z_errmsg : Array String :=\s*#\[(.*?)\]", code, re.S)
    if errmsg:
        for m in re.finditer(STRING, errmsg.group(1)):
            number = line_of(code, errmsg.start(1) + m.start())
            found.setdefault(unescape(m.group(1)), []).append(f"{rel}:{number}")


def used() -> tuple[dict[str, list[str]], list[str]]:
    found: dict[str, list[str]] = {}
    errors: list[str] = []
    for path in sorted((ROOT / "ZlibF/Zlib").glob("*.lean")):
        scan(str(path.relative_to(ROOT)), path.read_text(), found, errors)
    version = re.search(r"def ZLIB_VERSION\b[^\n]*?" + STRING, (ROOT / "ZlibF/Runtime/Schema.lean").read_text())
    if version:
        found.setdefault(unescape(version.group(1)), []).append("ZLIB_VERSION")
    else:
        errors.append("ZlibF/Runtime/Schema.lean: the definition of ZLIB_VERSION was not found")
    return found, errors


def main() -> int:
    tab = set(table())
    found, errors = used()
    for s, where in sorted(found.items()):
        if s not in tab:
            errors.append(f"string literal not in strTable: {s!r} (used at {', '.join(where)})")
    for error in errors:
        print(error)
    if errors:
        return 1
    sites = sum(len(where) for where in found.values())
    print(f"check-strlit: {len(found)} literals used at {sites} places, all in strTable ({len(tab)} entries)")
    return 0


if __name__ == "__main__":
    sys.exit(main())

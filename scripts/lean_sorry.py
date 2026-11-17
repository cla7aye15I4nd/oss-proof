#!/usr/bin/env python3
"""List every `sorry` token in Lean sources, outside comments and string literals.

Usage: lean_sorry.py PATH... (a file, or a directory searched for *.lean). Prints one
`file:line: text` for each occurrence and returns their number through `count`.

Removed before the search: line comments `--`, block comments `/- -/` with nesting (also the doc
comments `/-- -/` and `/-! -/`), string literals (also raw strings `r"…"`, `r#"…"#`), character
literals and quoted identifiers `«…»`. The text inside the `{…}` holes of an interpolated string
(`s!"…{e}…"`) is code and is kept. The tokens are `sorry` and `sorryAx`.
"""
import pathlib
import re
import sys

TOKEN = re.compile(r"(?<![\w.'!?«])(?:sorry|sorryAx)(?![\w'!?»])")
CHAR = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\'\n])'")
RAW = re.compile(r'r(#*)"')
IDENT_END = re.compile(r"[\w'!?]")


def strip(text, keep_literals=False):
    """The text with comments and literals replaced by spaces. Line breaks are kept.

    With `keep_literals`, only comments are replaced: string and character literals stay as written."""
    out = []
    i, n = 0, len(text)

    def blank(chunk):
        out.append(''.join('\n' if c == '\n' else ' ' for c in chunk))

    def literal(chunk):
        if keep_literals:
            out.append(chunk)
        else:
            blank(chunk)

    while i < n:
        c = text[i]
        two = text[i:i + 2]
        if two == '--':
            end = text.find('\n', i)
            end = n if end == -1 else end
            blank(text[i:end])
            i = end
        elif two == '/-':
            depth, j = 1, i + 2
            while j < n and depth:
                if text[j:j + 2] == '/-':
                    depth, j = depth + 1, j + 2
                elif text[j:j + 2] == '-/':
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            blank(text[i:j])
            i = j
        elif c == '«':
            end = text.find('»', i)
            end = n if end == -1 else end + 1
            blank(text[i:end])
            i = end
        elif c == 'r' and RAW.match(text, i) and not (i and IDENT_END.match(text[i - 1])):
            match = RAW.match(text, i)
            close = '"' + match.group(1)
            end = text.find(close, match.end())
            end = n if end == -1 else end + len(close)
            literal(text[i:end])
            i = end
        elif c == '"' and keep_literals:
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            out.append(text[i:j + 1])
            i = j + 1
        elif c == '"':
            interpolated = i > 0 and text[i - 1] == '!'
            j = i + 1
            blank('"')
            while j < n and text[j] != '"':
                if text[j] == '\\':
                    blank(text[j:j + 2])
                    j += 2
                elif interpolated and text[j] == '{':
                    # A hole holds code. Holes with nested braces or strings are kept whole up to the
                    # matching brace: keeping too much can only report more, never less.
                    depth, k = 1, j + 1
                    while k < n and depth:
                        depth += {'{': 1, '}': -1}.get(text[k], 0)
                        k += 1
                    out.append(' ' + strip(text[j + 1:k - 1]) + ' ')
                    j = k
                else:
                    blank(text[j])
                    j += 1
            blank(text[j:j + 1])
            i = j + 1
        elif c == "'" and not (i and IDENT_END.match(text[i - 1])) and CHAR.match(text, i):
            end = CHAR.match(text, i).end()
            literal(text[i:end])
            i = end
        else:
            out.append(c)
            i += 1
    return ''.join(out)


def occurrences(text):
    """The 1-based line numbers of the tokens, one entry for each token."""
    return [number for number, line in enumerate(strip(text).split('\n'), 1) for _ in TOKEN.finditer(line)]


def files(paths):
    for raw in paths:
        path = pathlib.Path(raw)
        if path.is_dir():
            yield from sorted(path.rglob('*.lean'))
        elif path.is_file():
            yield path
        else:
            raise SystemExit(f'error: no such file or directory: {raw}')


def main(paths):
    count = 0
    for path in files(paths):
        text = path.read_text(encoding='utf-8')
        if 'sorry' not in text:
            continue
        lines = text.split('\n')
        for number in occurrences(text):
            count += 1
            print(f'{path}:{number}: {lines[number - 1].strip()}')
    print(f'sorry count: {count}')
    return 1 if count else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))

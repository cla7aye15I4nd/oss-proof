"""Facts and fragments shared by every page: footer, top navigation, description."""
from __future__ import annotations

from pathlib import Path
import html
import os
import re
import subprocess

SITE = Path(__file__).resolve().parent
REPO = SITE.parents[1]
GIT_ROOT = REPO.parents[1]
SUITE_OUT = GIT_ROOT / 'site/dist'
OUT = SUITE_OUT / 'zlib'
REPO_URL = 'https://github.com/cla7aye15I4nd/oss-proof'


def _git(*args: str) -> str:
    return subprocess.check_output(['git', *args], cwd=GIT_ROOT, text=True).strip()


# Lean sources are linked at the revision the site was built from. It is never shown as text.
COMMIT = _git('rev-parse', 'HEAD')


def route_href(route: str, current: Path, lang: str, anchor: str = '') -> str:
    target = OUT / lang / (route + '.html')
    return os.path.relpath(target, current.parent).replace(os.sep, '/') + ('#' + anchor if anchor else '')


def suite_href(current: Path, lang: str) -> str:
    target = SUITE_OUT / lang / 'index.html'
    return os.path.relpath(target, current.parent).replace(os.sep, '/')


def top_links(current: Path, lang: str) -> str:
    """The one fixed set of top-level entries, on every page."""
    zh = lang == 'zh'
    entries = [
        ('index', 'articles', '文章', 'Articles'),
        ('progress', '', '状态', 'Status'),
        ('specifications', '', '规格', 'Specifications'),
        ('proofs', '', '证明', 'Proofs'),
    ]
    relative = current.relative_to(OUT / lang).as_posix()
    links = [f'<a href="{suite_href(current, lang)}">{"全部库" if zh else "All libraries"}</a>']
    for route, anchor, cn, en in entries:
        mark = ' aria-current="page"' if relative == route + '.html' and not anchor else ''
        links.append(f'<a href="{route_href(route, current, lang, anchor)}"{mark}>{cn if zh else en}</a>')
    return '<span class="site-links">' + ''.join(links) + '</span>'


def stamp(current: Path, lang: str) -> str:
    zh = lang == 'zh'
    status = route_href('progress', current, lang)
    suite = suite_href(current, lang)
    return (f'<footer class="site-stamp"><a href="{suite}">oss-proof</a> · <a href="{status}">'
            f'{"结论的状态" if zh else "Status of the results"}</a></footer>')


def describe(body: str, title: str) -> str:
    """A one-sentence meta description: the first paragraph with text, else the title."""
    for paragraph in re.findall(r'<p\b[^>]*>(.*?)</p>', body, re.S):
        text = html.unescape(re.sub(r'<[^>]+>', '', paragraph))
        text = ' '.join(text.split())
        if len(text) >= 40:
            return text if len(text) <= 180 else text[:177].rsplit(' ', 1)[0] + '…'
    return title

"""Render unlisted bilingual pages from site/pages/{en,zh}/*.md.

These pages are reachable by URL only: the portal, the global contents and the project subsites
never link to them, and each page asks search engines not to index it.
"""
from __future__ import annotations

from pathlib import Path
import html
import re

import markdown

import portal

OUT = portal.OUT
PAGES_DIR = Path(__file__).resolve().parent / "pages"


def page_names() -> list[str]:
    en = {p.stem for p in (PAGES_DIR / "en").glob("*.md")}
    zh = {p.stem for p in (PAGES_DIR / "zh").glob("*.md")}
    if en != zh:
        raise ValueError(f"site/pages/en and site/pages/zh diverged: {sorted(en ^ zh)}")
    return sorted(en)


def split_title(md_text: str) -> tuple[str, str]:
    lines = md_text.strip().splitlines()
    if not lines or not lines[0].startswith("# "):
        raise ValueError("an unlisted page must start with a level-1 `# Title` heading")
    title = re.sub(r"`([^`]+)`", r"\1", lines[0][2:].strip())
    body = markdown.markdown("\n".join(lines[1:]), extensions=["tables", "fenced_code", "attr_list"])
    return title, body


def render_page(name: str, lang: str, summaries: list[portal.ProjectSummary]) -> None:
    zh = lang == "zh"
    t = lambda cn, en: cn if zh else en
    title, body = split_title((PAGES_DIR / lang / f"{name}.md").read_text())
    current = OUT / lang / f"{name}.html"
    other = OUT / ("en" if zh else "zh") / f"{name}.html"
    home = OUT / lang / "index.html"
    asset = lambda n: portal.href(OUT / "static" / n, current)
    revision = portal.asset_revision()
    styles = "".join(
        f'<link rel="stylesheet" href="{asset(n)}?v={revision}">'
        for n in ("base.css", "reference.css", "book.css", "navigation.css", "syntax.css", "portal.css", "select.css")
    )
    doc = (
        f'<!doctype html><html lang="{lang}"><head>'
        f'<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">'
        f'<meta name="robots" content="noindex,nofollow">'
        f'<title>{html.escape(title)} · oss-proof</title>'
        f'<link rel="icon" href="{asset("favicon.svg")}" type="image/svg+xml">{styles}'
        f'<script defer src="{asset("navigation.js")}?v={revision}"></script>'
        f'<script defer src="{asset("reference.js")}?v={revision}"></script>'
        f'<script type="module" src="{asset("select.js")}?v={revision}"></script>'
        f'</head><body>'
        f'<a class="zl-skip" href="#content">{t("跳到正文", "Skip to content")}</a>'
        f'<main class="rf-page"><nav class="article-topbar">'
        f'<a class="article-brand" href="{portal.href(home, current)}">oss-proof</a>'
        f'<div><a data-language href="{portal.href(other, current)}" hreflang="{t("en", "zh")}">{t("EN", "中文")}</a></div></nav>'
        f'<div class="rf-layout"><article class="rf-body" id="content">'
        f'<header class="rf-hero"><div class="rf-eyebrow">{t("验证目标", "VERIFICATION TARGETS")}</div>'
        f'<h1 id="page-top">{html.escape(title)}</h1></header>'
        f'{body}</article></div>'
        f'<footer class="site-stamp"><a href="{portal.href(home, current)}">oss-proof</a> · '
        f'<a href="https://github.com/cla7aye15I4nd/oss-proof">GitHub</a></footer></main>'
        f'{portal.global_toc(current, lang, title, summaries)}</body></html>'
    )
    portal.write_html(current, doc)


def build_unlisted_pages(summaries: list[portal.ProjectSummary]) -> None:
    names = page_names()
    for name in names:
        for lang in ("en", "zh"):
            render_page(name, lang, summaries)
    print(f"Built {len(names)} unlisted page(s)")

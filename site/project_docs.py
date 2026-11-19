"""Render bilingual project subsites from projects/<id>/docs/{en,zh}/ markdown files."""
from __future__ import annotations

from hashlib import sha256
from pathlib import Path
import html
import re

import markdown

import portal

OUT = portal.OUT


def strip_stamp(text: str) -> tuple[str | None, str]:
    m = re.match(r"^\s*<!--\s*source-sha256:\s*([0-9a-f]{64})\s*-->\s*\n", text)
    if m:
        return m.group(1), text[m.end():]
    return None, text


def extract_h1_and_body(md_text: str) -> tuple[str, str]:
    _, body = strip_stamp(md_text)
    lines = body.strip().splitlines()
    if not lines or not lines[0].startswith("# "):
        raise ValueError("Markdown doc must start with a level-1 `# Title` heading")
    title = re.sub(r"`([^`]+)`", r"\1", lines[0][2:].strip())
    rest = "\n".join(lines[1:]).strip()
    rendered = markdown.markdown(rest, extensions=["tables", "fenced_code", "toc"])
    return title, rendered


def render_subsite_redirect(route: str, brand: str) -> None:
    doc = (
        '<!doctype html><html lang="en" data-book-redirect><head><meta charset="utf-8">'
        '<meta name="viewport" content="width=device-width,initial-scale=1">'
        f'<title>{html.escape(brand)}</title><link rel="canonical" href="en/index.html">'
        '<script>(function(){var p=(navigator.language||"").toLowerCase().startsWith("zh")?"zh":"en";'
        'location.replace("./"+p+"/index.html"+location.search+location.hash);})();</script>'
        f'</head><body><h1>{html.escape(brand)}</h1>'
        '<p><a href="en/index.html">English</a> · <a href="zh/index.html">中文</a></p></body></html>'
    )
    portal.write_html(OUT / route / "index.html", doc)


def render_doc_page(
    summary: portal.ProjectSummary,
    summaries: list[portal.ProjectSummary],
    lang: str,
    md_rel: str,
    out_name: str,
) -> None:
    zh = lang == "zh"
    t = lambda cn, en: cn if zh else en
    md_path = summary.project.root / "docs" / lang / md_rel
    h1_title, html_body = extract_h1_and_body(md_path.read_text())
    if zh and not re.search(r"[\u3400-\u9fff]", h1_title):
        h1_title = f"{h1_title} 验证总览"

    current = OUT / summary.route / lang / out_name
    other = OUT / summary.route / ("en" if zh else "zh") / out_name
    portal_home = OUT / lang / "index.html"
    asset = lambda name: portal.href(OUT / "static" / name, current)
    revision = portal.asset_revision()

    full_title = f"{h1_title} · {summary.brand}"
    eyebrow = t("形式化验证子站", "VERIFICATION SUBSITE")

    en_root = summary.project.root / "docs" / "en"
    extra_links = ""
    if (en_root / "findings.md").is_file():
        extra_links += f'<a href="findings.html">{t("发现的问题", "Findings")}</a>'
    if (en_root / "deviations.md").is_file():
        extra_links += f'<a href="deviations.html">{t("前提与偏差", "Deviations")}</a>'
    if (en_root / "trusted-base.md").is_file():
        extra_links += f'<a href="trusted-base.html">{t("可信基", "Trusted Base")}</a>'

    top_nav = (
        f'<span class="site-links">'
        f'<a href="{portal.href(portal_home, current)}">oss-proof</a>'
        f'<a href="index.html">{t("总览", "Overview")}</a>'
        f'<a href="progress.html">{t("结论的状态", "Status")}</a>'
        f'{extra_links}'
        f'</span>'
    )
    footer = (
        f'<footer class="site-stamp">'
        f'<a href="{portal.href(portal_home, current)}">oss-proof</a> · '
        f'<a href="https://github.com/cla7aye15I4nd/oss-proof">GitHub</a>'
        f'</footer>'
    )

    doc = (
        f'<!doctype html><html lang="{lang}"><head>'
        f'<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">'
        f'<title>{html.escape(full_title)}</title>'
        f'<link rel="icon" href="{asset("favicon.svg")}" type="image/svg+xml">'
        f'<link rel="stylesheet" href="{asset("base.css")}?v={revision}">'
        f'<link rel="stylesheet" href="{asset("reference.css")}?v={revision}">'
        f'<link rel="stylesheet" href="{asset("book.css")}?v={revision}">'
        f'<link rel="stylesheet" href="{asset("navigation.css")}?v={revision}">'
        f'<link rel="stylesheet" href="{asset("syntax.css")}?v={revision}">'
        f'<link rel="stylesheet" href="{asset("portal.css")}?v={revision}">'
        f'<link rel="stylesheet" href="{asset("select.css")}?v={revision}">'
        f'<script defer src="{asset("navigation.js")}?v={revision}"></script>'
        f'<script defer src="{asset("reference.js")}?v={revision}"></script>'
        f'<script type="module" src="{asset("select.js")}?v={revision}"></script>'
        f'</head><body>'
        f'<a class="zl-skip" href="#content">{t("跳到正文", "Skip to content")}</a>'
        f'<main class="rf-page"><nav class="article-topbar">'
        f'<a class="article-brand" href="index.html">{html.escape(summary.brand)}</a>'
        f'<div>{top_nav}<a data-language href="{portal.href(other, current)}" hreflang="{t("en", "zh")}">{t("EN", "中文")}</a></div></nav>'
        f'<div class="rf-layout"><article class="rf-body" id="content">'
        f'<header class="rf-hero"><div class="rf-eyebrow">{eyebrow} · {portal.badge(summary.done, lang)}</div>'
        f'<h1 id="page-top">{html.escape(h1_title)}</h1>'
        f'<p>{html.escape(summary.summary_zh if zh else summary.summary_en)}</p></header>'
        f'{html_body}</article></div>{footer}</main>'
        f'{portal.global_toc(current, lang, full_title, summaries)}</body></html>'
    )
    portal.write_html(current, doc)


def build_standard_subsite(summary: portal.ProjectSummary, summaries: list[portal.ProjectSummary]) -> None:
    render_subsite_redirect(summary.route, summary.brand)
    en_dir = summary.project.root / "docs" / "en"
    for md_file in sorted(en_dir.glob("*.md")):
        md_rel = md_file.name
        out_name = "index.html" if md_rel == "overview.md" else f"{md_file.stem}.html"
        for lang in ("en", "zh"):
            render_doc_page(summary, summaries, lang, md_rel, out_name)


def check_standard_docs_parity(proj_root: Path) -> None:
    en_dir = proj_root / "docs/en"
    zh_dir = proj_root / "docs/zh"
    en_files = {p.relative_to(en_dir) for p in en_dir.rglob("*.md")}
    zh_files = {p.relative_to(zh_dir) for p in zh_dir.rglob("*.md")}
    assert en_files == zh_files and en_files, (proj_root, "docs/en and docs/zh diverged", en_files ^ zh_files)
    for rel in sorted(en_files):
        en_bytes = (en_dir / rel).read_bytes()
        expected_sha = sha256(en_bytes).hexdigest()
        stamp, _ = strip_stamp((zh_dir / rel).read_text())
        assert stamp == expected_sha, (proj_root, rel, "Chinese translation source-sha256 mismatch", stamp, expected_sha)

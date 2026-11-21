"""Render unlisted bilingual pages from site/pages/{en,zh}/*.md.

These pages are reachable by URL only: the portal, the global contents and the project subsites
never link to them, and each page asks search engines not to index it.

A paragraph containing only ``[[audit-explorer]]`` is replaced by the call-chain explorer rendered
from ``site/pages/data/audit-chains.json``. The explorer is plain HTML; ``audit-explorer.js`` only
adds tabs, selection and highlighting on top of it.
"""
from __future__ import annotations

from hashlib import sha256
from pathlib import Path
import html
import json
import re
import shutil

import markdown

import portal

OUT = portal.OUT
PAGES_DIR = Path(__file__).resolve().parent / "pages"
ASSETS_DIR = PAGES_DIR / "assets"
CHAINS_FILE = PAGES_DIR / "data" / "audit-chains.json"
REPO_BLOB = "https://github.com/cla7aye15I4nd/oss-proof/blob/main/projects/"
MARKER = "<p>[[audit-explorer]]</p>"

LAYERS = {
    "js": ("Sharp · JavaScript", "Sharp · JavaScript"),
    "cpp": ("Sharp · C++", "Sharp · C++"),
    "vips": ("libvips", "libvips"),
    "py": ("Pillow · Python", "Pillow · Python"),
    "pyc": ("Pillow · C", "Pillow · C"),
    "rust": ("librsvg · Rust", "librsvg · Rust"),
    "lib": ("C 库", "C library"),
}
STATUS = {
    "target": ("Tier 0 目标", "Tier 0 target"),
    "progress": ("已有进度", "has progress"),
    "outside": ("不在计划内", "not planned"),
}


def page_names() -> list[str]:
    en = {p.stem for p in (PAGES_DIR / "en").glob("*.md")}
    zh = {p.stem for p in (PAGES_DIR / "zh").glob("*.md")}
    if en != zh:
        raise ValueError(f"site/pages/en and site/pages/zh diverged: {sorted(en ^ zh)}")
    return sorted(en)


def load_chains() -> dict:
    return json.loads(CHAINS_FILE.read_text())


def inline(text: str) -> str:
    """Escape text and turn `backticks` into <code>."""
    parts = re.split(r"`([^`]+)`", text)
    return "".join(f"<code>{html.escape(p)}</code>" if i % 2 else html.escape(p) for i, p in enumerate(parts))


class Explorer:
    def __init__(self, data: dict, lang: str, current: Path):
        self.data = data
        self.zh = lang == "zh"
        self.lang = lang
        self.current = current

    def t(self, pair) -> str:
        if isinstance(pair, dict):
            return pair["zh" if self.zh else "en"]
        return pair[0] if self.zh else pair[1]

    def lib_name(self, lib: str) -> str:
        return self.data["libraries"].get(lib, {}).get("name", lib)

    def lib_link(self, lib: str) -> str | None:
        status = self.data["libraries"][lib]["status"]
        if status == "progress":
            return portal.href(OUT / lib / self.lang / "progress.html", self.current)
        if status == "target":
            return f"{REPO_BLOB}{lib}/AGENTS.md"
        repo = self.data["repos"].get(lib)
        return repo["url"].split("/-/blob/")[0].split("/blob/")[0] if repo else None

    def step(self, s: dict, index: int) -> str:
        layer = s["layer"]
        lib = s.get("lib")
        status = self.data["libraries"][lib]["status"] if lib else "glue"
        classes = f"ax-step ax-layer-{layer} ax-status-{status}"
        head = f'<span class="ax-tag">{html.escape(self.t(LAYERS[layer]))}</span>'
        if lib and layer == "lib":
            link = self.lib_link(lib)
            name = f"<code>{html.escape(self.lib_name(lib))}</code>"
            head += f'<a class="ax-lib" href="{link}">{name}</a>' if link else f'<span class="ax-lib">{name}</span>'
            head += f'<span class="ax-chip">{html.escape(self.t(STATUS[status]))}</span>'
        if s.get("file"):
            url = self.data["repos"][s["repo"]]["url"] + s["file"]
            head += f'<a class="ax-file" href="{url}"><code>{html.escape(s["file"])}</code></a>'
        syms = "".join(f"<code>{html.escape(x)}</code>" for x in s.get("symbols", []))
        body = f'<div class="ax-syms">{syms}</div>' if syms else ""
        if s.get("note"):
            body += f'<p class="ax-note">{inline(self.t(s["note"]))}</p>'
        branches = self.branches(s.get("branches", []))
        data_lib = f' data-lib="{html.escape(lib)}"' if lib else ""
        return (
            f'<li class="{classes}"{data_lib} style="--i:{index}">'
            f'<div class="ax-box"><div class="ax-head">{head}</div>{body}</div>{branches}</li>'
        )

    def flow(self, steps: list[dict], sub: bool = False) -> str:
        items = "".join(self.step(s, i) for i, s in enumerate(steps))
        return f'<ol class="ax-flow{" ax-sub" if sub else ""}">{items}</ol>'

    def branches(self, branches: list[dict]) -> str:
        if not branches:
            return ""
        inner = "".join(
            f'<div class="ax-branch"><p class="ax-branch-label">{inline(self.t(b["label"]))}</p>{self.flow(b["steps"], True)}</div>'
            for b in branches
        )
        return f'<div class="ax-branches">{inner}</div>'

    def libs_of(self, steps: list[dict]) -> set[str]:
        found: set[str] = set()
        for s in steps:
            if s.get("lib"):
                found.add(s["lib"])
            for b in s.get("branches", []):
                found |= self.libs_of(b["steps"])
        return found

    def chain(self, group: dict, c: dict) -> str:
        libs = self.libs_of(c["steps"]) | self.libs_of([{"branches": c.get("branches", [])}])
        out = f'<p class="ax-out">{inline(self.t(c["out"]))}</p>' if c.get("out") else ""
        chain_branches = ""
        if c.get("branches"):
            chain_branches = f'<div class="ax-chain-branches">{self.branches(c["branches"])}</div>'
        return (
            f'<article class="ax-chain" id="chain-{c["id"]}" data-chain="{c["id"]}" data-libs="{" ".join(sorted(libs))}">'
            f'<header class="ax-chain-head"><h4>{html.escape(self.t(c["title"]))}</h4>'
            f'<p>{inline(self.t(c["summary"]))}</p></header>'
            f'<div class="ax-chain-body">'
            f'<div class="ax-code"><p class="ax-caption">{html.escape(self.t(("示例代码", "Example")))}</p>'
            f'<pre><code class="language-{group["lang"]}">{html.escape(self.t(c["code"]))}</code></pre></div>'
            f'<div class="ax-diagram"><p class="ax-caption">{html.escape(self.t(("调用链", "Call chain")))}</p>'
            f'{self.flow(c["steps"])}{chain_branches}{out}</div>'
            f'</div></article>'
        )

    def matrix(self, group: dict) -> str:
        head = "".join(
            f'<th scope="col" data-lib="{lib}"><code>{html.escape(self.lib_name(lib))}</code></th>' for lib in group["matrix"]
        )
        rows = ""
        for c in group["chains"]:
            libs = self.libs_of(c["steps"]) | self.libs_of([{"branches": c.get("branches", [])}])
            cells = "".join(
                f'<td data-lib="{lib}">{"●" if lib in libs else ""}</td>' for lib in group["matrix"]
            )
            rows += (
                f'<tr data-chain="{c["id"]}"><th scope="row"><a href="#chain-{c["id"]}">'
                f'{html.escape(self.t(c["title"]))}</a></th>{cells}</tr>'
            )
        caption = self.t(("每条调用链触达的 C 库", "C libraries each chain reaches"))
        return (
            f'<div class="ax-matrix-wrap"><table class="ax-matrix"><caption>{html.escape(caption)}</caption>'
            f'<thead><tr><th scope="col">{html.escape(self.t(("调用链", "Chain")))}</th>{head}</tr></thead>'
            f'<tbody>{rows}</tbody></table></div>'
        )

    def render(self) -> str:
        legend = "".join(
            f'<span class="ax-legend-item ax-status-{k}">{html.escape(self.t(v))}</span>' for k, v in STATUS.items()
        )
        legend += f'<span class="ax-legend-item ax-status-glue">{html.escape(self.t(("调用方与衔接代码", "caller and glue code")))}</span>'
        groups = ""
        for g in self.data["groups"]:
            chains = "".join(self.chain(g, c) for c in g["chains"])
            groups += (
                f'<section class="ax-group" id="ax-{g["id"]}" data-group="{g["id"]}">'
                f'<h3>{html.escape(self.t(g["title"]))}</h3>{self.matrix(g)}'
                f'<div class="ax-chains">{chains}</div></section>'
            )
        return f'<div class="ax" data-audit-explorer><div class="ax-legend">{legend}</div>{groups}</div>'


def asset_tag(current: Path) -> str:
    tags = ""
    for name in sorted(p.name for p in ASSETS_DIR.glob("*")):
        rev = sha256((ASSETS_DIR / name).read_bytes()).hexdigest()[:12]
        url = portal.href(OUT / "static" / "pages" / name, current) + f"?v={rev}"
        if name.endswith(".css"):
            tags += f'<link rel="stylesheet" href="{url}">'
        elif name.endswith(".js"):
            tags += f'<script defer src="{url}"></script>'
    return tags


def split_title(md_text: str) -> tuple[str, str]:
    lines = md_text.strip().splitlines()
    if not lines or not lines[0].startswith("# "):
        raise ValueError("an unlisted page must start with a level-1 `# Title` heading")
    title = re.sub(r"`([^`]+)`", r"\1", lines[0][2:].strip())
    body = markdown.markdown("\n".join(lines[1:]), extensions=["tables", "fenced_code", "attr_list"])
    return title, body


def render_page(name: str, lang: str, summaries: list[portal.ProjectSummary], chains: dict) -> None:
    zh = lang == "zh"
    t = lambda cn, en: cn if zh else en
    title, body = split_title((PAGES_DIR / lang / f"{name}.md").read_text())
    current = OUT / lang / f"{name}.html"
    if MARKER in body:
        body = body.replace(MARKER, Explorer(chains, lang, current).render())
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
        f'<link rel="icon" href="{asset("favicon.svg")}" type="image/svg+xml">{styles}{asset_tag(current)}'
        f'<script defer src="{asset("navigation.js")}?v={revision}"></script>'
        f'<script defer src="{asset("reference.js")}?v={revision}"></script>'
        f'<script type="module" src="{asset("select.js")}?v={revision}"></script>'
        f'</head><body>'
        f'<a class="zl-skip" href="#content">{t("跳到正文", "Skip to content")}</a>'
        f'<main class="rf-page"><nav class="article-topbar">'
        f'<a class="article-brand" href="{portal.href(home, current)}">oss-proof</a>'
        f'<div><a data-language href="{portal.href(other, current)}" hreflang="{t("en", "zh")}">{t("EN", "中文")}</a></div></nav>'
        f'<div class="rf-layout"><article class="rf-body ax-page" id="content">'
        f'<header class="rf-hero"><div class="rf-eyebrow">{t("验证目标", "VERIFICATION TARGETS")}</div>'
        f'<h1 id="page-top">{html.escape(title)}</h1></header>'
        f'{body}</article></div>'
        f'<footer class="site-stamp"><a href="{portal.href(home, current)}">oss-proof</a> · '
        f'<a href="https://github.com/cla7aye15I4nd/oss-proof">GitHub</a></footer></main>'
        f'{portal.global_toc(current, lang, title, summaries)}</body></html>'
    )
    portal.write_html(current, doc)


def build_unlisted_pages(summaries: list[portal.ProjectSummary]) -> None:
    dst = OUT / "static" / "pages"
    dst.mkdir(parents=True, exist_ok=True)
    for asset in ASSETS_DIR.glob("*"):
        shutil.copyfile(asset, dst / asset.name)
    chains = load_chains()
    names = page_names()
    for name in names:
        for lang in ("en", "zh"):
            render_page(name, lang, summaries, chains)
    print(f"Built {len(names)} unlisted page(s)")

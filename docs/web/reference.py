"""Render existing documentation and public targets without changing their statements."""
from __future__ import annotations

from pathlib import Path
from navigation import global_contents
from pagekit import COMMIT, top_links, stamp, describe
from syntax import color_blocks, color_code
from progress import functional_state, functions, goal_done, other_goals, state
from api_returns import parse_role, validate_sources, enhance_contract, enhance_manual
from functools import lru_cache
from hashlib import sha256
from urllib.parse import urlsplit, unquote
import html
import json
import os
import re
import shutil

from markdown import Markdown

SITE = Path(__file__).resolve().parent
REPO = SITE.parents[1]
OUT = SITE / "dist"
GITHUB = "https://github.com/cla7aye15I4nd/zlib-f/blob/"+COMMIT+"/"
# Anchors of the earlier, longer status page that published pages still link to. They resolve to the top of the page.
PROGRESS_ANCHORS = ['proof-progress-graph','target-evidence','remaining-work','core-proof-skeletons','ordered-next-work',
                    'public-api-proof-readiness','no-fault-coverage-of-zlibh-functions','observations']
GROUPS = {
    "deflate-stream": ("压缩流", "Compression streams"),
    "inflate-stream": ("解压流", "Decompression streams"),
    "inflate-back": ("回调解码", "Callback decoding"),
    "utility": ("缓冲区与库信息", "Buffers and library information"),
    "checksums": ("校验和", "Checksums"),
    "gz-file": ("gzip 文件", "Gzip files"),
}


def href(target: Path, current: Path) -> str:
    return os.path.relpath(target, current.parent).replace(os.sep, "/")


def resolve_doc(source: Path) -> Path:
    # An article has no unsuffixed file: its two language files are `<key>.en.md` and `<key>.zh.md`.
    if source.is_relative_to(REPO/'docs/articles') and source.exists():
        return source
    if source.name.endswith('.zh.md'):
        source=source.with_name(source.name.removesuffix('.zh.md')+'.md')
    if source.exists():
        return source
    relative=source.relative_to(REPO).as_posix()
    aliases={'docs/design/internal-contracts.md':'docs/spec/internal-contracts.md',
             'docs/safety.md':'docs/spec/safety.md'}
    candidate=aliases.get(relative,relative.replace('docs/api/','docs/spec/api/').replace('docs/format/','docs/spec/format/'))
    target=REPO/candidate
    return target if target.exists() else source


def documents() -> list[Path]:
    root=REPO/'docs'
    result=[]
    for folder, directories, files in os.walk(root):
        if Path(folder)==root:
            directories[:]=[name for name in directories if name not in {'web','articles'}]
        result.extend(Path(folder)/name for name in files
                      if name.endswith('.md') and not name.endswith('.zh.md'))
    return sorted(result)


def doc_path(source: Path, lang: str) -> Path:
    if source.is_relative_to(REPO/'docs/articles'):
        from book import BY_KEY
        key=source.name.split('.')[0]
        if key in BY_KEY:return OUT/(BY_KEY[key]['route']+('.zh.html' if lang=='zh' else '.html'))
    source=resolve_doc(source)
    # Older source snapshots predate the separate composition guide. Their
    # function-method guide contains the corresponding composition discussion.
    if not source.exists() and source == REPO/'docs/proof/stream-composition.md':
        source=REPO/'docs/proof/method.md'
    stem = source.relative_to(REPO).with_suffix("")
    return OUT / "reference" / (str(stem) + (".zh.html" if lang == "zh" else ".html"))


def md(text: str, *, baselevel: int = 1) -> tuple[str, str, list[dict]]:
    parser = Markdown(extensions=["fenced_code", "tables", "attr_list", "toc", "md_in_html"],
                      extension_configs={"toc": {"baselevel": baselevel, "toc_depth": 6}})
    return parser.convert(text), parser.toc, parser.toc_tokens


def flatten(tokens: list[dict]) -> list[dict]:
    return [item for token in tokens for item in [token, *flatten(token.get("children", []))]]


STALE: list[str] = []
MISSING: list[str] = []
NOTICE = '<p class="rf-stale-note" role="note"><strong>本页的英文原文已更新。</strong>中文译文可能落后；请以英文页为准。</p>'


def translated(source: Path) -> tuple[str, bool]:
    if source.is_relative_to(REPO/'docs'):
        target=source.with_name(source.stem+'.zh.md')
    else:
        relative=source.relative_to(REPO)
        target=SITE/'content/repository'/relative.parent/(relative.stem+'.zh.md')
    if not target.exists():
        raise ValueError('Missing Chinese document: '+str(target.relative_to(REPO)))
    text = target.read_text()
    stamp = re.search(r"source-sha256:\s*([0-9a-f]{64})", text)
    if not stamp or stamp.group(1) != sha256(source.read_bytes()).hexdigest():
        # A stale twin is a warning, not a build failure. The page shows a notice.
        name = str(target.relative_to(REPO))
        if name not in STALE:
            STALE.append(name)
            print('WARNING: Chinese document is older than its English source: '+name)
        return text, False
    return text, True


def direct_status(text: str) -> str:
    """Use direct status wording in the reading view; leave code untouched."""
    lines=[]
    fence=None
    for line in text.splitlines(keepends=True):
        marker=re.match(r'^\s*(`{3,}|~{3,})',line)
        if marker:
            if fence is None:fence=marker[1][0]
            elif fence==marker[1][0]:fence=None
        elif fence is None:
            line=re.sub(r'\bto confirm\b','not yet confirmed',line,flags=re.I)
        lines.append(line)
    return ''.join(lines)


def document_title(source: Path, lang: str) -> str:
    text=translated(source)[0] if lang=='zh' else source.read_text()
    title=re.search(r'^#\s+(.+)$',text,re.M)
    return re.sub(r'\s*\{#[^}]+\}\s*$','',title[1]) if title else source.stem


def paired_anchors(original: str, text: str) -> str:
    # Keep the source's heading IDs even when the visible heading is translated.
    # Fenced source is left byte-for-byte intact.
    _, _, tokens = md(original)
    ids = iter(item["id"] for item in flatten(tokens))
    lines = []
    fence = None
    for line in text.splitlines():
        marker = re.match(r"^\s*(`{3,}|~{3,})", line)
        if marker:
            if fence is None:
                fence = marker.group(1)[0]
            elif fence == marker.group(1)[0]:
                fence = None
        if fence is None and re.match(r"^#{1,6}\s+", line):
            key = next(ids, None)
            if key is None:
                raise ValueError("Translation has extra headings")
            line = re.sub(r"\s*\{#[^}]+\}\s*$", "", line) + " {#" + key + "}"
        lines.append(line)
    if next(ids, None) is not None:
        raise ValueError("Translation omits source headings")
    return "\n".join(lines)


def rewrite(body: str, source: Path, current: Path, lang: str) -> str:
    def replace(match):
        attr, raw = match.group(1), html.unescape(match.group(2))
        url = urlsplit(raw)
        if url.netloc in {'www.dataisland.org','dataisland.org'} and url.path.startswith('/zlib-f/'):
            route=url.path.removeprefix('/zlib-f/')
            if not route or route.endswith('/'):route+='index'
            route=route.removesuffix('.zh.html').removesuffix('.html')
            if url.path.endswith(('.html','/')):
                result=href(OUT/(route+('.zh.html' if lang=='zh' else '.html')),current)
                return f'{attr}="{html.escape(result+("?"+url.query if url.query else "")+("#"+url.fragment if url.fragment else ""),quote=True)}"'
        project=re.match(r'^/cla7aye15I4nd/zlib-f/blob/[^/]+/(docs/.+\.md)$',url.path) if url.netloc=='github.com' else None
        if project:
            destination=REPO/unquote(project[1])
        elif url.scheme or url.netloc or raw.startswith("mailto:"):
            return match.group(0)
        else:
            destination = (source.parent / unquote(url.path)).resolve() if url.path else source
        if destination.suffix=='.md' and destination.is_relative_to(REPO):
            destination=resolve_doc(destination)
        extras={REPO/'README.md',REPO/'patches/README.md'}
        if destination.suffix=='.md' and destination.is_relative_to(REPO/'docs') and not destination.exists():
            # The link would leave the site for a file that does not exist.
            note=source.relative_to(REPO).as_posix()+' -> '+destination.relative_to(REPO).as_posix()
            if note not in MISSING:
                MISSING.append(note)
                print('WARNING: link to a page that does not exist: '+note)
        if destination.suffix == ".md" and (destination.is_relative_to(REPO / "docs") or destination in extras) and destination.exists():
            result = href(doc_path(destination, lang), current)
        elif destination.suffix == '.lean' and destination.is_relative_to(REPO) and destination.exists():
            result = source_path(destination, lang)
        elif destination.is_file() and destination.is_relative_to(REPO/'docs'):
            chinese=destination.with_name(destination.stem+'.zh'+destination.suffix)
            if lang=='zh' and not destination.stem.endswith('.zh') and chinese.exists():
                destination=chinese
            asset=OUT/'reference/assets'/destination.relative_to(REPO/'docs')
            asset.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(destination,asset)
            result=href(asset,current)
        elif destination.is_relative_to(REPO):
            result = GITHUB + destination.relative_to(REPO).as_posix()
        else:
            return match.group(0)
        if url.fragment:
            fragment=url.fragment
            if destination.suffix == '.lean' and re.fullmatch(r'L\d+-L\d+',fragment):
                fragment=fragment.split('-')[0]
            result += "#" + fragment
        return f'{attr}="{html.escape(result, quote=True)}"'
    return re.sub(r'\b(href|src)="([^"]+)"', replace, body)


def shell(title: str, body: str, current: Path, lang: str, *, toc: str = "",
          other: Path | None = None, intro: str = "", title_id: str = "", eyebrow: str = "",
          description: str = "") -> str:
    zh = lang == "zh"
    t = lambda a, b: a if zh else b
    asset = lambda name: href(OUT / "static" / name, current)
    root = href(OUT / ("index.zh.html" if zh else "index.html"), current)
    home = href(OUT / "reference" / ("index.zh.html" if zh else "index.html"), current)
    api = href(OUT / "reference" / ("api.zh.html" if zh else "api.html"), current)
    proof = href(OUT / "reference" / ("proofs.zh.html" if zh else "proofs.html"), current)
    sources = href(OUT / "reference" / ("sources.zh.html" if zh else "sources.html"), current)
    language = f'<a data-language href="{href(other, current)}" hreflang="{t("en", "zh")}">{t("EN", "中文")}</a>' if other else ""
    revision = sha256(b''.join((SITE/'static'/name).read_bytes() for name in ['reference.js','reference.css','api-returns.css','diagram-view.mjs','navigation.js','navigation.css','syntax.css'])).hexdigest()[:12]
    return_assets=f'<link rel="stylesheet" href="{asset("api-returns.css")}?v={revision}">' if 'data-return-guide=' in body or 'ar-index-role' in body else ''
    return f'''<!doctype html><html lang="{lang}"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>{html.escape(title)}{"" if title=="zlib × Lean" else " · zlib × Lean"}</title>
<meta name="description" content="{html.escape(description or describe(intro+body,title),quote=True)}">
<link rel="icon" href="{asset('favicon.svg')}" type="image/svg+xml">
<link rel="stylesheet" href="{asset('base.css')}?v={revision}"><link rel="stylesheet" href="{asset('reference.css')}?v={revision}"><link rel="stylesheet" href="{asset('book.css')}?v={revision}">
<link rel="stylesheet" href="{asset('navigation.css')}?v={revision}"><script defer src="{asset('navigation.js')}?v={revision}"></script>
<link rel="stylesheet" href="{asset('syntax.css')}?v={revision}">
{return_assets}
<script defer src="{asset('reference.js')}?v={revision}"></script></head><body>
<a class="zl-skip" href="#content">{t('跳到正文','Skip to content')}</a>
<main class="rf-page"><nav class="article-topbar"><a class="article-brand" href="{root}">zlib × Lean</a><div>{top_links(current,lang)}{language}</div></nav>

<div class="rf-layout"><article class="rf-body" id="content"><header class="rf-hero"><div class="rf-eyebrow">{eyebrow or t('参考文档','REFERENCE')+' / ZLIB × LEAN'}</div><h1{(' id="'+html.escape(title_id,quote=True)+'"') if title_id else ''}>{html.escape(title)}</h1>{intro}</header>{body}</article>
</div>
{stamp(current,lang)}</main>{global_contents(current,lang,title,toc)}</body></html>'''


def write(path: Path, content: str) -> None:
    content = color_blocks(content)
    if 'data-global-toc' in content:
        select_revision = sha256(b''.join((SITE/'static'/name).read_bytes() for name in ['select.css','select.js','select-model.mjs'])).hexdigest()[:12]
        select_assets = f'<link rel="stylesheet" href="{href(OUT/"static/select.css",path)}?v={select_revision}"><script type="module" src="{href(OUT/"static/select.js",path)}?v={select_revision}"></script>'
        content = content.replace('</head>', select_assets+'</head>', 1)
    # Old generated documentation contains a few duplicate HTML anchors. Preserve
    # the first destination and disambiguate later IDs in the rendered view only.
    seen = {}
    def unique(match):
        key = match.group(2)
        seen[key] = seen.get(key, 0) + 1
        value=key if seen[key]==1 else f'{key}--{seen[key]}'
        return match.group(1)+value+match.group(3)
    content = re.sub(r'(<[A-Za-z][^<>]*?\s+id=")([^"]+)(")', unique, content)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content)


def goal_excerpts() -> dict[str, tuple[Path, int, str]]:
    result = {}
    # Goals live in Spec/Safety and Spec/Functional; Spec/Common holds no goal.
    layers = ("Common", "Safety", "Functional")
    for source in sorted(s for layer in layers for s in (REPO / "ZlibF/Spec" / layer).glob("*.lean")):
        text = source.read_text()
        for match in re.finditer(r"^def Goal\.(\w+)\b", text, re.M):
            start = match.start()
            tail = text[match.end():]
            end_match = re.search(r"\n(?:def |theorem |abbrev |structure |inductive |end\b|/--)", tail)
            end = match.end() + end_match.start() if end_match else len(text)
            previous = text.rfind("/--", 0, start)
            if previous >= 0:
                close = text.find("-/", previous)
                if close < start and not text[close+2:start].strip():
                    start = previous
            result[match.group(1)] = (source, text[:start].count("\n")+1, text[start:end].strip())
    return result


def render_docs() -> None:
    sources=documents()+[REPO/'README.md',REPO/'patches/README.md']
    for source in sources:
        original = source.read_text()
        for lang in ("en", "zh"):
            text, available = translated(source) if lang == "zh" else (original, True)
            stale_note = ''
            body_lang = lang
            try:
                body, toc, tokens = md(paired_anchors(original, direct_status(text)))
            except ValueError:
                if available:
                    raise
                # Headings differ: show the English source under the notice.
                available = False
                body_lang = 'en'
                body, toc, tokens = md(paired_anchors(original, direct_status(original)))
                body = '<div lang="en">' + body + '</div>'
            if not available:
                stale_note = NOTICE
            headings = flatten(tokens)
            title = re.sub(r"<[^>]+>", "", headings[0]["name"]) if headings else source.stem
            if lang == 'zh' and body_lang == 'en':
                zh_title = re.search(r'^#\s+(.+?)\s*(?:\{#[^}]+\})?\s*$', text, re.M)
                title = zh_title[1] if zh_title else title
            # The source title is already represented in the page header.
            body = re.sub(r"<h1\b[^>]*>.*?</h1>\s*", "", body, count=1, flags=re.S)
            body = stale_note + body
            current = doc_path(source, lang)
            if source==REPO/'docs/progress.md':
                present=set(re.findall(r'\bid="([^"]+)"',body))
                body=''.join(f'<span id="{anchor}" hidden></span>' for anchor in PROGRESS_ANCHORS if anchor not in present)+body
            body = rewrite(body, source, current, lang)
            if source.parent==REPO/'docs/spec/api' and source.stem in GROUPS:
                body=enhance_manual(body,body_lang)
            toc = rewrite(toc, source, current, lang) if body_lang == lang else ''
            other = doc_path(source, "en" if lang == "zh" else "zh")
            write(current, shell(title, body, current, lang, toc=toc,
                                 other=other,
                                 title_id=headings[0]['id'] if headings else ''))


def section(text: str, name: str) -> str:
    match = re.search(r"^## " + re.escape(name) + r"\s*$", text, re.M)
    if not match:
        raise ValueError(f"Missing documentary contract: {name}")
    tail = text[match.end():]
    end = re.search(r"\n## ", tail)
    return tail[:end.start()] if end else tail


def common_prefix(text: str, names: list[str]) -> str:
    starts = [m.start() for name in names if (m := re.search(r"^## " + re.escape(name) + r"\s*$", text, re.M))]
    return text[:min(starts)]


def render_api(manifest: dict) -> None:
    excerpts = goal_excerpts()
    all_entries = manifest["apis"]
    for lang in ("en", "zh"):
        zh = lang == "zh"
        t = lambda a, b: a if zh else b
        current = OUT / "reference" / ("api.zh.html" if zh else "api.html")
        other = OUT / "reference" / ("api.html" if zh else "api.zh.html")
        cards = []
        for entry in all_entries:
            name = entry["function"]
            source = REPO / entry["manual"].split("#")[0]
            original = source.read_text()
            text, fresh = translated(source) if zh else (original, True)
            stale_api = zh and not fresh
            if stale_api:
                text = original
            contract = section(text, name)
            group = source.stem
            index = 0 if zh else 1
            target = OUT / "reference/functions" / (name + (".zh.html" if zh else ".html"))
            opposite = target.with_name(name + (".html" if zh else ".zh.html"))
            without_code = re.sub(r"```[\s\S]*?```", "", contract).strip()
            summary = re.split(r"\n\s*\n", without_code)[0].replace("\n", " ")
            summary = re.sub(r"\[([^\]]+)\]\([^)]+\)", r"\1", summary)
            summary = re.sub(r"[*`]", "", summary)
            keywords = " ".join((name, GROUPS[group][index], re.sub(r"\s+", " ", contract)))
            scope = entry["scope"]
            _,result_role=parse_role(contract)
            keywords+=' '+result_role
            cards.append(f'<a class="rf-api-row" data-group="{group}" data-scope="{scope}" data-search="{html.escape(keywords,quote=True)}" href="{href(target,current)}"><code>{name}</code><span{' lang="en"' if stale_api else ''}><span class="ar-index-role">{html.escape(result_role)}</span>{html.escape(summary)}</span><small>{html.escape(GROUPS[group][index])}{" · Windows" if scope != "lp64-linux" else ""}</small><b aria-hidden="true">↗</b></a>')
            body, _, _ = md(paired_anchors(section(original,name),contract))
            body=re.sub(r'<(/?)h([3-6])(\b[^>]*>)',lambda match:'<'+match[1]+'h'+str(int(match[2])-1)+match[3],body)
            body = rewrite(body, source, target, lang)
            labels={'Domain':'定义域','Pre':'前置条件','Post':'返回与保证','Effects':'内存与状态效果','Errors':'错误路径','Edges':'边界情况','Results':'返回码','Accounting':'计数记账','Ownership':'所有权'}
            aliases={'Domain':('定义域',),'Pre':('前置条件','前提'),'Post':('后置条件','返回与保证','后置保证'),'Effects':('效果','影响','内存与状态效果'),'Errors':('错误路径','错误'),'Edges':('边界情况','边缘情况','边缘情形'),'Results':('结果','返回结果','返回码'),'Accounting':('计数记账','记账'),'Ownership':('所有权',)}
            source_keys=set(re.findall(r'\*\*(Domain|Pre|Post|Effects|Errors|Edges|Results|Accounting|Ownership)[.:]?\*\*',section(original,name)))
            seen_labels=set()
            def clause(match):
                raw=match.group(1)
                key=next((key for key in source_keys if raw.rstrip('.:。：')==key or any(re.match('^'+alias+r'(?:[。:：.]|[（(]|$)',raw) for alias in aliases[key])),None)
                if key is None:return match[0]
                identifier=f' id="{key.lower()}"' if key not in seen_labels else ''
                seen_labels.add(key)
                label=labels[key] if zh else key
                return f'<strong class="rf-contract-label"{identifier}>{label}</strong>'
            body=re.sub(r'<strong>([^<]+)</strong>',clause,body)
            body=enhance_contract(body,name,'en' if stale_api else lang)
            names = [item["function"] for item in all_entries if item["manual"].split("#")[0] == entry["manual"].split("#")[0]]
            common, _, _ = md(paired_anchors(common_prefix(original,names),common_prefix(text,names)), baselevel=2)
            common = re.sub(r"<h2\b[^>]*>.*?</h2>\s*", "", common, count=1, flags=re.S)
            common = rewrite(common, source, target, lang)
            body += f'<details class="rf-common"><summary>{t("本组共同前提与范围","Shared conditions and scope")}</summary>{common}</details>'
            safety = entry.get("safety_goal")
            status_page = href(doc_path(REPO/'docs/progress.md',lang),target)
            if safety and safety != entry.get("functional_goal"):
                short = safety.rsplit(".", 1)[-1]
                if short not in excerpts:
                    raise ValueError(f"Safety target not found: {safety}")
                goal_source, line, code = excerpts[short]
                body += f'<section class="rf-formal" id="safety-target"><h2>{t("安全目标","Safety goal")}</h2><p><code>{html.escape(safety)}</code></p><p class="rf-proof-status">{t("状态：","State: ")}{state(goal_done(safety),lang)} · <a href="{status_page}">{t("结论的状态","Status of the results")}</a></p><pre><code class="language-lean">{html.escape(code)}</code></pre><a href="{source_path(goal_source, lang)}#L{line}">{t("相关定义与源码","Related definitions and source")} ↗</a></section>'
            goal = entry.get("functional_goal")
            if goal:
                short = goal.rsplit(".", 1)[-1]
                if short not in excerpts:
                    raise ValueError(f"Public target not found: {goal}")
                goal_source, line, code = excerpts[short]
                context = source_path(goal_source, lang)
                body += f'<section class="rf-formal" id="formal-target"><h2>{t("形式化契约","Formal contract") if safety == goal else t("功能契约（安全之外）","Functional contract (beyond safety)")}</h2><p><code>{html.escape(goal)}</code></p><p class="rf-proof-status">{t("状态：","State: ")}{functional_state(goal_done(goal),lang)} · <a href="{status_page}">{t("结论的状态","Status of the results")}</a></p><pre><code class="language-lean">{html.escape(code)}</code></pre><a href="{context}#L{line}">{t("相关定义与源码","Related definitions and source")} ↗</a></section>'
            else:
                body += f'<p class="rf-language-note">{t("此平台专用条目没有默认 LP64 构建目标。","This platform-specific entry has no default LP64 target.")}</p>'
            category = doc_path(source, lang)
            related = ''.join(f'<li><a href="{href(OUT/"reference/functions"/(n+(".zh.html" if zh else ".html")),target)}">{n}</a></li>' for n in names)
            sidebar = f'<h3>{GROUPS[group][index]}</h3><ul>{related}</ul>'
            intro = (NOTICE if stale_api else '') + f'<p{" lang=" + chr(34) + "en" + chr(34) if stale_api else ""}>{html.escape(summary)}</p><a class="rf-category" href="{href(category,target)}">{t("完整章节与共同规则","Full chapter and shared rules")} ↗</a>'
            if stale_api:
                body = '<div lang="en">' + body + '</div>'
            write(target, shell(name, body, target, lang, toc=sidebar,
                                other=opposite, intro=intro))
        default_count = sum(item["scope"] == "lp64-linux" for item in all_entries)
        controls = f'<div class="rf-search"><label for="api-search">{t("查找函数或约定","Find a function or contract")}</label><input id="api-search" type="search" autocomplete="off" placeholder="{t("函数名、Z_MEM_ERROR、字典、所有权…","Function, Z_MEM_ERROR, dictionary, ownership…")}"><div class="rf-filters"><label>{t("分组","Group")}<select id="api-group" aria-label="{t('分组','Group')}"><option value="">{t("全部分组","All groups")}</option>'+''.join(f'<option value="{key}">{value[0 if zh else 1]}</option>' for key,value in GROUPS.items())+f'</select></label><label>{t("配置","Build")}<select id="api-scope" aria-label="{t('配置','Build')}"><option value="">{t("全部条目","All entries")}</option><option value="lp64-linux">LP64 Linux</option><option value="windows">Windows</option></select></label><output id="api-count" aria-live="polite">{len(all_entries)} {t("个条目","entries")}</output></div></div>'
        banner = f'<p class="rf-scope-note">{default_count} {t("个默认构建入口，另含 Windows gzopen_w。各条完整保留签名、定义域、前置条件、结果、内存效果和错误路径。文档中的契约与 Lean 目标的范围可能不同，两者都原样呈现。","default-build entries, plus Windows gzopen_w. Every entry retains its signature, domain, preconditions, results, memory effects, and error paths. The documented contract and the Lean goal may differ in scope; each is shown as it is.")}</p>'
        body = banner + controls + '<div class="rf-api-list">'+''.join(cards)+'</div><p id="api-empty" hidden>'+t('没有匹配项。试试函数名的一部分。','No matches. Try part of a function name.')+'</p>'
        write(current, shell(t("API 契约", "API contracts"), body, current, lang,
                             other=other, intro=f'<p>{t("完整公开接口索引","The complete public-interface index")}</p>'))


def render_portals() -> None:
    for lang in ("en", "zh"):
        zh = lang == "zh"
        t = lambda a, b: a if zh else b
        suffix = ".zh.html" if zh else ".html"
        current = OUT / "reference" / ("index"+suffix)
        other = current.with_name("index.html" if zh else "index.zh.html")
        def link(file, label):
            return f'<a href="{href(doc_path(REPO/"docs"/file,lang),current)}">{label} ↗</a>'
        body = f'<p class="rf-scope-note"><a href="{href(doc_path(REPO/"docs/progress.md",lang),current)}">{t("结论的状态","Status of the results")} →</a> {t("每项结论、每个公开函数是完成还是未完成，以及哪些不在计划内。","Done or not done, for each result and each public function, and what is not planned.")}</p>'
        body += f'<p class="rf-intro">{t("这里是规格、接口契约和证明讲解的入口。长的推导和错误路径都完整保留。","The entry to the specifications, the interface contracts and the proof explanations. Long arguments and error paths are kept in full.")}</p>'
        body += f'<section class="rf-portal-section"><span>01 / ZLIB</span><h2>{t("算法与接口","Algorithms and interfaces")}</h2><a class="rf-portal-primary" href="api{suffix}">{t("全部公开 API 契约","All public API contracts")} ↗</a><div class="rf-link-grid">'+link('api/contracts.md',t('契约术语与定义域','Contract vocabulary and domains'))+link('api/streams.md',t('流、缓冲区与调用顺序','Streams, buffers, and call order'))+link('format/README.md',t('DEFLATE、zlib 与 gzip 格式','DEFLATE, zlib, and gzip formats'))+link('format/model.md',t('格式的 Lean 模型','The Lean format model'))+'</div></section>'
        body += f'<section class="rf-portal-section"><span>02 / VERIFICATION</span><h2>{t("形式化验证","Formal verification")}</h2><a class="rf-portal-primary" href="proofs{suffix}">{t("inflate 与 deflate 的证明路线","Inflate and deflate proof routes")} ↗</a><div class="rf-link-grid">'+link('design/architecture.md',t('翻译与运行时架构','Translation and runtime architecture'))+link('design/internal-contracts.md',t('内部函数义务','Internal helper obligations'))+link('proof/method.md',t('单函数证明方法','Proving one function'))+link('safety.md',t('安全目标与调用者义务','Safety goals and caller obligations'))+link('trusted-base.md',t('信任边界','Trusted base'))+link('deviations.md',t('范围限制','Scope restrictions'))+link('findings.md',t('在 zlib 中发现的问题','Issues found in zlib'))+link('checking/README.md',t('完成的结论依靠什么','What a done result rests on'))+link('progress.md',t('结论的状态','Status of the results'))+link('glossary.md',t('术语表','Glossary'))+'</div></section>'
        body += f'<details class="rf-common"><summary>{t("全部页面","All pages")}</summary><ul>'
        for file in documents():
            body += '<li>'+link(file.relative_to(REPO/'docs').as_posix(),html.escape(document_title(file,lang)))+'</li>'
        body += '</ul></details>'
        write(current,shell(t('规格与文档索引','Specifications and documentation'),body,current,lang,other=other))
        current=OUT/'reference'/('proofs'+suffix)
        other=current.with_name('proofs.html' if zh else 'proofs.zh.html')
        engine=[('inflate','inflate.md',t('解压引擎','Decompression engine'),t('窗口内容、真实模式、位前缀、查表、退出与跨调用序列。','Window contents, actual modes, supporting bits, lookup, exits, and call sequences.')),
                ('deflate','deflate.md',t('压缩引擎','Compression engine'),t('窗口、哈希链、匹配搜索、策略循环、符号账本、块输出与默认封装。','Windows, hash chains, matching, strategy loops, symbol ledgers, block output, and the default wrapper.'))]
        body=f'<p class="rf-scope-note">{t("先从引擎的完整论证进入，再按查表、复制、编码和内存等组件查阅细节。每条路线都连接到具体函数约定和相关定义。","Start with an engine’s full argument, then follow lookup, copying, coding, and memory components in detail. Each route connects to concrete function contracts and definitions.")}</p><div class="rf-engine-grid">'
        for name,file,label,desc in engine:
            target=doc_path(REPO/'docs/proof'/file,lang)
            fn=OUT/'reference/functions'/(name+suffix)
            body+=f'<section><span>{name}.c</span><h2>{label}</h2><p>{desc}</p><a href="{href(target,current)}">{t("完整证明细节","Full proof details")} →</a><a href="{href(fn,current)}#formal-target">{t("公开契约与精确目标","Public contract and exact target")} →</a></section>'
        body+='</div><div class="rf-link-grid">'
        for file,label in [('inftrees.md',t('解码表构造','Decode-table construction')),('inffast.md',t('快速解码','Fast decoding')),('trees.md',t('树、位输出与共享缓冲区','Trees, bit emission, and shared storage')),('method.md',t('证明方法与不变量','Proof method and invariants')),('adler32.md','Adler-32'),('crc32.md','CRC-32'),('zutil.md',t('分配与工具函数','Allocation and utilities'))]:
            body+=link('proof/'+file,label)
        body+='</div>'
        body+=f'<p><a href="targets{suffix}">{t("调用序列、拒绝与前提可满足性的目标命题","Statements of the goals for call sequences, refusals and satisfiable premises")} →</a></p>'
        write(current,shell(t('证明细节','Proof details'),body,current,lang,other=other))


def source_path(source: Path, lang: str) -> str:
    """Lean sources are read on GitHub at the built commit; the site keeps no copy."""
    return GITHUB+source.relative_to(REPO).as_posix()


def render_sources() -> None:
    sources=set((REPO/'ZlibF').rglob('*.lean'))|{REPO/'ZlibF.lean'}
    for document in documents():
        for raw in re.findall(r'\]\(([^)]+\.lean(?:#[^)]*)?)\)',document.read_text()):
            url=urlsplit(raw)
            if not url.scheme and not url.netloc:
                linked=(document.parent/unquote(url.path)).resolve()
                if linked.is_relative_to(REPO) and linked.exists():sources.add(linked)
    sources=sorted(sources)
    catalog=[]
    for source in sources:
        raw=source.read_text()
        relative=source.relative_to(REPO).as_posix()
        group=relative.split('/')[1] if '/' in relative else 'Root'
        symbols=re.findall(r'^(?:(?:private|protected|noncomputable)\s+)?(?:def|theorem|lemma|structure|inductive|abbrev|class)\s+([\w.\']+)',raw,re.M)
        catalog.append((source,group,symbols))
    for lang in ('en','zh'):
        zh=lang=='zh';suffix='.zh.html' if zh else '.html';current=OUT/'reference'/('sources'+suffix)
        other=current.with_name('sources.html' if zh else 'sources.zh.html')
        title='Lean 源码与证明正文' if zh else 'Lean source and proof bodies'
        body='<p class="rf-scope-note">'+('按用途查找 Lean 模块：实现证明、函数规格、数学推导、运行时模型或 C 翻译。可以按模块路径或声明名搜索。' if zh else 'Find Lean modules by role: implementation proofs, specifications, mathematics, the runtime model, or C translation. Search by module path or declaration name.')+'</p>'
        group_labels={'Proof':'实现证明','Spec':'函数与格式规格','Math':'数学推导','Runtime':'运行时模型','Zlib':'C 源码翻译','Root':'模块入口'}
        body+='<div class="rf-search"><label for="api-search">'+('搜索模块或声明名' if zh else 'Search modules or declaration names')+'</label><input id="api-search" type="search" autocomplete="off"><div class="rf-filters"><label>'+('分组' if zh else 'Group')+'<select id="api-group"><option value="">'+('全部模块' if zh else 'All modules')+'</option>'+''.join('<option value="'+name+'">'+(group_labels[name]+'（'+name+'）' if zh else name)+'</option>' for name in group_labels)+'</select></label><select id="api-scope" hidden><option value=""></option></select><output id="api-count" aria-live="polite"></output></div></div><div class="rf-api-list">'
        for source,group,symbols in catalog:
            relative=source.relative_to(REPO).as_posix()
            keys=' '.join([relative,*symbols])
            body+=f'<a class="rf-api-row rf-source-row" data-group="{group}" data-scope="source" data-search="{html.escape(keys,quote=True)}" href="{source_path(source,lang)}"><code>{html.escape(source.name)}</code><span>{html.escape(relative)}</span><small>{group_labels.get(group,group) if zh else group}</small><b>↗</b></a>'
        body+='</div><p id="api-empty" hidden>'+('没有匹配模块。' if zh else 'No matching modules.')+'</p>'
        write(current,shell(title,body,current,lang,other=other))


def render_targets(manifest: dict) -> None:
    """The statements of the goals that are about more than one function."""
    excerpts=goal_excerpts()
    safety=other_goals()
    domains={goal.rsplit('.',1)[-1] for goal in manifest['nonvacuity_goals']}
    sections=[
        (('调用序列的安全','Safety of call sequences'),[n for n in safety if n.endswith('_sequence_safety')]),
        (('拒绝','Refusals'),[n for n in safety if n.endswith('_refusal')]),
        (('前提可以满足','The premises can be met'),[n for n in safety if n in domains]),
        (('完整的序列契约（安全之外）','Full sequence contracts (beyond safety)'),[goal.rsplit('.',1)[-1] for goal in manifest['sequence_goals']]),
    ]
    full={goal.rsplit('.',1)[-1]:goal for goal in manifest['sequence_goals']}
    listed=[n for _,names in sections for n in names]
    if set(safety)-set(listed) or len(listed)!=len(set(listed)):
        raise ValueError('A goal about more than one function has no section, or two')
    for lang in ('en','zh'):
        zh=lang=='zh';suffix='.zh.html' if zh else '.html'
        current=OUT/'reference'/('targets'+suffix)
        other=current.with_name('targets.html' if zh else 'targets.zh.html')
        status=href(doc_path(REPO/'docs/progress.md',lang),current)
        body='<p class="rf-scope-note">'+('这些目标说的不是单个函数：完整的调用序列、对无效流或句柄的拒绝，以及各目标的前提可以满足。每个函数自己的目标在该函数的页面上。哪些已经完成，见<a href="'+status+'">结论的状态</a>；完整的序列契约是功能目标，它们各自的状态写在下面每一条旁边。' if zh else 'These goals are about more than one function: whole call sequences, the refusal of an invalid stream or handle, and that the premises of the goals can be met. The goal of each function is on the page of that function. Which are done is on the <a href="'+status+'">status page</a>; the state of each full sequence contract, which is a functional goal, is shown with it below.')+'</p>'
        for title,names in sections:
            body+='<h2>'+title[0 if zh else 1]+'</h2>'
            for name in names:
                source,line,code=excerpts[name]
                # The status page lists the goals of the safety results. A full sequence contract is
                # a functional goal and is not listed there, so its state is shown here.
                shown=f'<p class="rf-proof-status">{"状态：" if zh else "State: "}{functional_state(goal_done(full[name]),lang)}</p>' if name in full else ''
                body+=f'<section id="{name}"><h3>{name}</h3>{shown}<pre><code class="language-lean">{html.escape(code)}</code></pre><a href="{source_path(source,lang)}#L{line}">{"完整上下文" if zh else "Complete context"} ↗</a></section>'
        write(current,shell('目标的命题' if zh else 'Statements of the goals',body,current,lang,other=other))


def render_proof_routes() -> None:
    routes=json.loads((SITE/'content/proof-routes.json').read_text())
    for lang in ('en','zh'):
        zh=lang=='zh';suffix='.zh.html' if zh else '.html'
        current=OUT/'reference'/('proofs'+suffix)
        text=current.read_text()
        body='<section class="rf-proof-routes"><h2>'+('实际证明的阅读路线' if zh else 'Reading the actual proofs')+'</h2><p>'+('下面按实现步骤排列关键引理。先读每项解决的问题和前提，再点击查看具体推导；完整接口证明需要把这些步骤连接起来。' if zh else 'Follow key lemmas in implementation order. Read the problem and premises for each step, then open its derivation. Whole-interface proofs connect these steps.')+'</p>'
        for engine in ('inflate','deflate'):
            body+=f'<h3>{engine}</h3><ol class="rf-proof-steps">'
            for route in routes:
                if route['engine']!=engine:continue
                source=REPO/route['path'];name=route['declaration']
                # A curated route may refer to a later development snapshot.
                # Never present a missing declaration as evidence in an older one.
                if not source.exists():continue
                raw=source.read_text()
                found=re.search(r'^(?:(?:private|protected|noncomputable)\s+)?(?:theorem|lemma|def)\s+'+re.escape(name)+r'\b',raw,re.M)
                if not found:continue
                line=raw[:found.start()].count('\n')+1
                body+=f'<li><a href="{source_path(source,lang)}#L{line}">{html.escape(route["topic"][lang])}</a><p>{html.escape(route["summary"][lang])}</p><small>{html.escape(route["premise"][lang])}</small><code>{html.escape(name)}</code></li>'
            body+='</ol>'
        body+='</section>'
        text=text.replace('</article>',body+'</article>',1)
        write(current,text)


def build_reference() -> None:
    validate_sources()
    manifest=json.loads((REPO/'tests/audit/public-api.json').read_text())
    render_docs()
    render_sources()
    render_api(manifest)
    render_targets(manifest)
    render_portals()
    render_proof_routes()
    count=len(list((OUT/'reference').rglob('*.html')))
    print(f"Built {count} reference pages; {len(manifest['apis'])} public API entries per language")

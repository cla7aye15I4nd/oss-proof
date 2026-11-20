"""Render the unified oss-proof portal and shared verification overview."""
from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path
import html
import json
import os
import re
import shutil
import sys

SITE_DIR = Path(__file__).resolve().parent
REPO = SITE_DIR.parent
OUT = SITE_DIR / "dist"

sys.path.insert(0, str(REPO))
sys.path.insert(0, str(REPO / "projects/zlib/docs/web"))

from framework.manifest import Project, load_all_projects
from syntax import color_blocks

SHARED_STATIC_FILES = (
    "base.css",
    "reference.css",
    "book.css",
    "navigation.css",
    "syntax.css",
    "select.css",
    "select.js",
    "select-model.mjs",
    "navigation.js",
    "reference.js",
    "diagram-view.mjs",
    "favicon.svg",
)

REV_FILES = (
    "base.css",
    "reference.css",
    "book.css",
    "navigation.css",
    "syntax.css",
    "portal.css",
    "select.css",
    "select.js",
    "select-model.mjs",
    "navigation.js",
    "reference.js",
    "diagram-view.mjs",
)

_PAIR_RE = re.compile(r"\(\s*``([A-Za-z0-9_'.]+)\s*,\s*``([A-Za-z0-9_'.]+)\s*\)")
_NAME_RE = re.compile(r"``([A-Za-z0-9_'.]+)")


@dataclass(frozen=True)
class ParsedResults:
    proved: tuple[tuple[str, str], ...]
    not_done: tuple[str, ...]
    required: tuple[str, ...]


def parse_results_lists(text: str) -> ParsedResults:
    clean = re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", "", text, flags=re.S))

    def extract_list(defn: str) -> str:
        m = re.search(rf"\bdef\s+{defn}\b[^=]*:=\s*\[(.*?)\]", clean, flags=re.S)
        if not m:
            raise ValueError(f"missing `def {defn} := [...]` in Results.lean")
        return m.group(1)

    proved = tuple(_PAIR_RE.findall(extract_list("proved")))
    not_done = tuple(_NAME_RE.findall(extract_list("notDone")))
    required = tuple(_NAME_RE.findall(extract_list("required")))
    return ParsedResults(proved=proved, not_done=not_done, required=required)


@dataclass(frozen=True)
class ProjectSummary:
    project: Project
    route: str
    brand: str
    upstream_version: str
    target: str
    documented_functions: int
    proved_functions: int
    proved_goals: int
    stated_goals: int
    required_goals: int
    proved_required_goals: int
    done: bool
    findings_count: int
    patches_count: int
    summary_en: str
    summary_zh: str
    has_full_book: bool
    has_articles: bool


def summarize_project(proj: Project) -> ProjectSummary:
    results_rel = proj.results_module.replace(".", "/") + ".lean"
    results_text = (proj.root / results_rel).read_text()
    parsed = parse_results_lists(results_text)
    proved_set = {goal for goal, _ in parsed.proved}
    proved_count = len(parsed.proved)
    stated_count = len(parsed.proved) + len(parsed.not_done)
    req_count = len(parsed.required)
    proved_req = sum(1 for g in parsed.required if g in proved_set)

    cov_cfg = proj.data.get("checks", {}).get("coverage")
    doc_fns = 0
    proved_fns = 0
    if cov_cfg:
        api_manifest = json.loads((proj.root / cov_cfg["manifest"]).read_text())
        hidden = set(api_manifest.get("undocumented", {}).get("functions", []))
        for api in api_manifest.get("apis", []):
            if api.get("scope") == "lp64-linux" and api["function"] not in hidden:
                doc_fns += 1
                if api.get("safety_goal") in proved_set:
                    proved_fns += 1

    site_cfg = proj.data.get("site", {})
    upstream_cfg = proj.data["upstream"]
    done = req_count > 0 and proved_req == req_count and (doc_fns == 0 or proved_fns == doc_fns)
    has_full_book = bool(site_cfg.get("builder"))
    has_articles = (proj.root / "docs/en/read/codec.md").is_file()
    return ProjectSummary(
        project=proj,
        route=site_cfg.get("route", proj.id),
        brand=site_cfg.get("brand", f"{proj.title} × Lean"),
        upstream_version=f"{proj.title} {upstream_cfg.get('version', '')}".strip(),
        target=upstream_cfg.get("target", "x86_64 Linux LP64"),
        documented_functions=doc_fns,
        proved_functions=proved_fns,
        proved_goals=proved_count,
        stated_goals=stated_count,
        required_goals=req_count,
        proved_required_goals=proved_req,
        done=done,
        findings_count=int(site_cfg.get("findings_count", 0)),
        patches_count=int(site_cfg.get("patches_count", 0)),
        summary_en=site_cfg["summary"]["en"],
        summary_zh=site_cfg["summary"]["zh"],
        has_full_book=has_full_book,
        has_articles=has_articles,
    )


def href(target: Path, current: Path) -> str:
    return os.path.relpath(target, current.parent).replace(os.sep, "/")


def asset_revision() -> str:
    return sha256(b"".join((OUT / "static" / n).read_bytes() for n in REV_FILES)).hexdigest()[:12]


def copy_shared_static() -> None:
    src_static = REPO / "projects/zlib/docs/web/static"
    dst_static = OUT / "static"
    if dst_static.exists():
        shutil.rmtree(dst_static)
    dst_static.mkdir(parents=True, exist_ok=True)
    for name in SHARED_STATIC_FILES:
        shutil.copyfile(src_static / name, dst_static / name)
    shutil.copyfile(SITE_DIR / "static/portal.css", dst_static / "portal.css")
    shutil.copytree(src_static / "fonts", dst_static / "fonts")
    (dst_static / "vendor").mkdir(parents=True, exist_ok=True)
    for vendor_name in ("mermaid-12.2.0.js", "mermaid-license.txt"):
        shutil.copyfile(src_static / "vendor" / vendor_name, dst_static / "vendor" / vendor_name)
    (OUT / ".nojekyll").touch()


def write_html(path: Path, content: str) -> None:
    content = color_blocks(content)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content)


def render_root_redirect() -> None:
    doc = (
        '<!doctype html><html lang="en" data-root-redirect><head><meta charset="utf-8">'
        '<meta name="viewport" content="width=device-width,initial-scale=1">'
        '<title>oss-proof</title><link rel="canonical" href="en/index.html">'
        '<script>(function(){var p=(navigator.language||"").toLowerCase().startsWith("zh")?"zh":"en";'
        'location.replace("./"+p+"/index.html"+location.search+location.hash);})();</script>'
        '</head><body><h1>oss-proof</h1>'
        '<p><a href="en/index.html">English</a> · <a href="zh/index.html">中文</a></p></body></html>'
    )
    write_html(OUT / "index.html", doc)


def badge(done: bool, lang: str) -> str:
    label = ("完成" if done else "未完成") if lang == "zh" else ("done" if done else "not done")
    cls = "done" if done else "not-done"
    return f'<span class="hm-badge hm-{cls}">{label}</span>'


def global_toc(current: Path, lang: str, page_title: str, summaries: list[ProjectSummary]) -> str:
    zh = lang == "zh"
    t = lambda cn, en: cn if zh else en
    idx = href(OUT / lang / "index.html", current)
    body = (
        f'<button type="button" class="bk-global-trigger" data-global-toc aria-controls="book-global-toc" '
        f'aria-expanded="false" title="{t("打开目录", "Open contents")}">'
        f'<svg viewBox="0 0 20 20" aria-hidden="true"><path d="M3 5h14M3 10h14M3 15h14"/></svg>'
        f'<span>{t("目录", "Contents")}</span></button>'
        f'<dialog class="bk-global-dialog" id="book-global-toc" aria-labelledby="book-global-title">'
        f'<div class="bk-global-header"><div><span>OSS-PROOF</span>'
        f'<h2 id="book-global-title">{t("目录", "Contents")}</h2></div>'
        f'<button type="button" data-toc-close aria-label="{t("关闭目录", "Close contents")}">×</button></div>'
        f'<div class="bk-global-location"><span>{t("正在阅读", "READING NOW")}</span>{html.escape(page_title)}</div>'
        f'<label class="bk-global-search">{t("查找库或主题", "Find a library or section")}'
        f'<input type="search" data-toc-search placeholder="{t("zlib、zstd、方法、检查…", "zlib, zstd, method, checking…")}" autocomplete="off"></label>'
        f'<nav class="bk-global-tree" aria-label="{t("全站目录", "Site contents")}">'
    )
    body += (
        f'<details class="bk-global-section" data-toc-section open>'
        f'<summary>{t("总览章节", "Overview")}</summary><ul>'
        f'<li data-toc-entry><a href="{idx}#libraries">{t("开源验证库", "Libraries")}</a></li>'
        f'<li data-toc-entry><a href="{idx}#method">{t("共同验证方法", "Verification method")}</a></li>'
        f'<li data-toc-entry><a href="{idx}#checking">{t("完成的结论依靠什么", "What a done result rests on")}</a></li>'
        f'</ul></details>'
    )
    body += f'<details class="bk-global-section" data-toc-section open><summary>{t("开源 C 库", "C libraries")}</summary><ul>'
    for item in summaries:
        sub_base = OUT / item.route / lang
        body += (
            f'<li data-toc-entry><a href="{href(sub_base / "index.html", current)}">{html.escape(item.brand)}</a></li>'
            f'<li data-toc-entry><a href="{href(sub_base / "progress.html", current)}">{html.escape(item.project.title)} · {t("结论的状态", "Status of the results")}</a></li>'
        )
        if item.has_full_book:
            body += (
                f'<li data-toc-entry><a href="{href(sub_base / "api.html", current)}">{html.escape(item.project.title)} · {t("公开 API 契约", "Public API contracts")}</a></li>'
            )
    body += "</ul></details>"
    body += f'</nav><p class="bk-global-empty" data-toc-empty hidden>{t("没有匹配条目。", "No matching entries.")}</p></dialog>'
    return body


def render_portal_page(lang: str, summaries: list[ProjectSummary]) -> None:
    zh = lang == "zh"
    t = lambda cn, en: cn if zh else en
    current = OUT / lang / "index.html"
    other = OUT / ("en" if zh else "zh") / "index.html"
    asset = lambda name: href(OUT / "static" / name, current)
    revision = asset_revision()

    page_title = t("oss-proof：开源 C 库的形式化验证", "oss-proof")
    lead = t(
        "用 Lean 4 对开源 C 库的逐语句翻译作机器检查的证明：公开函数在每条定理写明的前提下没有未定义行为、没有内存错误、没有泄漏，并且终止。",
        "Machine-checked Lean 4 proofs about statement-by-statement translations of open-source C libraries: every covered public function is free of undefined behaviour, memory errors and leaks, and terminates, under the premises each theorem states.",
    )

    cards: list[str] = []
    for item in summaries:
        sub = OUT / item.route / lang
        patches_note = (
            t(f"含 {item.patches_count} 个补丁", f"with {item.patches_count} patches")
            if item.patches_count
            else t("无补丁", "unpatched")
        )
        links = [
            (href(sub / "index.html", current), t("总览与范围 →", "Overview and scope →")),
            (href(sub / "progress.html", current), t("结论的状态", "Status of the results")),
        ]
        if item.has_full_book:
            links.append((href(sub / "api.html", current), t("公开 API 契约", "Public API contracts")))
            links.append((href(sub / "proofs.html", current), t("证明细节", "Proof details")))
        if item.findings_count:
            links.append((href(sub / "findings.html", current), t(f"上游发现的问题（{item.findings_count}）", f"Issues found ({item.findings_count})")))
        if item.has_articles:
            links.append((href(sub / "read/codec.html", current), t("三篇交互算法文章", "Interactive codec articles")))

        links_html = "".join(f'<a href="{u}">{html.escape(lbl)}</a>' for u, lbl in links)
        fn_stat = f"{item.proved_functions} / {item.documented_functions}" if item.documented_functions else "—"
        goal_stat = (
            f"{item.proved_required_goals} / {item.required_goals}"
            if item.required_goals
            else f"{item.proved_goals} / {item.stated_goals}"
        )
        goal_label = (
            t("必需目标（已完成 / 总数）", "Required goals (done / total)")
            if item.required_goals
            else t("已登记目标（已证 / 已列）", "Registered goals (proved / stated)")
        )
        cards.append(
            f'<article class="op-card" id="lib-{html.escape(item.project.id)}">'
            f'<div class="op-card-head"><div class="op-card-title">'
            f'<h3><a href="{href(sub / "index.html", current)}">{html.escape(item.brand)}</a></h3>'
            f'{badge(item.done, lang)}</div>'
            f'<span class="op-card-meta">{html.escape(item.upstream_version)} ({patches_note}) · {html.escape(item.target)}</span></div>'
            f'<p>{html.escape(item.summary_zh if zh else item.summary_en)}</p>'
            f'<dl class="op-metrics">'
            f'<div><dt>{t("有文档的公开函数", "Documented public functions")}</dt><dd>{fn_stat}</dd></div>'
            f'<div><dt>{goal_label}</dt><dd>{goal_stat}</dd></div>'
            f'<div><dt>{t("在上游发现的真实缺陷", "Confirmed upstream issues")}</dt><dd>{item.findings_count}</dd></div>'
            f'</dl>'
            f'<div class="op-links">{links_html}</div>'
            f'</article>'
        )

    mermaid = (
        'flowchart LR\n'
        '    S["选定的 C 源码与补丁"] -->|"逐语句人工翻译"| T["Lean 翻译与故障模型"]\n'
        '    T --> I["初始化定理：建立状态不变量"]\n'
        '    I --> V["跨调用保持不变量、帧边界与无泄漏"]\n'
        '    V --> G["Lean 内核检查精确目标命题"]'
        if zh
        else
        'flowchart LR\n'
        '    S["Pinned C source and patches"] -->|"statement-by-statement"| T["Lean translation and fault model"]\n'
        '    T --> I["Init theorem establishes invariant"]\n'
        '    I --> V["Calls preserve invariant, frame, no leak"]\n'
        '    V --> G["Lean kernel checks exact goal"]'
    )

    body = (
        f'<section id="libraries"><h2>{t("验证库与状态", "Libraries and status")}</h2>'
        f'<p>{t("每个结论只使用两种状态：完成（存在命题恰好等于目标的 Lean 定理且通过全部检查）或未完成。", "Each result has one of two states: done (a Lean theorem whose statement is exactly the goal exists and passes every check) or not done.")}</p>'
        f'<div class="op-grid">{"".join(cards)}</div></section>'
        f'<section id="method"><h2>{t("共同验证方法", "How every proof is built")}</h2>'
        f'<p>{t("同一套翻译规则、严格 ISO C17 内存与故障模型及证明结构用于所有库。", "Every library in this collection follows the same translation discipline, strict ISO C17 memory and fault model, and proof structure.")}</p>'
        f'<div class="op-steps">'
        f'<div class="op-step"><small>01</small><strong>{t("逐语句翻译", "Translate statement by statement")}</strong>'
        f'<p>{t("C 代码按原语句顺序翻译为 Lean。ISO C17 中可到达的每一种未定义行为（包括空指针或悬垂指针加零与跨对象指针减法）都表示为显式故障 Fault.ub；无符号算术回绕，有符号算术逐处检查。", "Pinned C code is translated to Lean without reordering or simplifying. Every ISO C17 undefined behaviour—including null or dangling pointer + 0 and cross-object pointer subtraction—raises Fault.ub; unsigned arithmetic wraps and signed arithmetic is checked.")}</p></div>'
        f'<div class="op-step"><small>02</small><strong>{t("定义表示不变量", "Define representation invariants")}</strong>'
        f'<p>{t("对每种流、解码器或文件句柄定义跨调用保持的状态性质：拥有的堆块、缓冲区容量、表内容与游标上界。", "Each stream, decoder or handle carries an explicit invariant over its owned heap blocks, buffer capacities, lookup tables and cursors.")}</p></div>'
        f'<div class="op-step"><small>03</small><strong>{t("逐函数证明，不假设被调函数", "Prove each function without assumptions")}</strong>'
        f'<p>{t("不把被调函数的契约当作公理。每个内部函数都在其自身翻译上证明定理；每个公开函数证明无故障返回、只写允许的内存帧并按账本分配与释放。", "No callee contract is assumed. Every helper has a theorem about its own translation; every public entry is proved to return without fault, write only its frame, and match its allocation ledger.")}</p></div>'
        f'<div class="op-step"><small>04</small><strong>{t("归纳调用历史并给出非空见证", "Compose histories and witness premises")}</strong>'
        f'<p>{t("对任意合法调用序列作归纳，证明生命周期与关闭释放无泄漏；单独的非空性定理给出满足前提的具体初始堆。", "Induction over call sequences proves safety and leak-free teardown across arbitrary histories, paired with concrete non-vacuity witnesses.")}</p></div>'
        f'</div>'
        f'<pre><code class="language-mermaid">{mermaid}</code></pre>'
        f'</section>'
        f'<section id="checking"><h2>{t("完成的结论依靠什么", "What a done result rests on")}</h2>'
        f'<p>{t("Lean 内核检查每一条证明：定理的类型必须在语法上恰好等于目标命题，只允许三条标准公理（propext、Classical.choice、Quot.sound），禁止 sorry、native_decide、bv_decide、unsafe、partial、opaque、自定义公理与外部绑定。", "Lean’s kernel checks every proof: each theorem’s type must be syntactically equal to its goal, using only the three standard axioms (propext, Classical.choice, Quot.sound), with no sorry, native_decide, bv_decide, unsafe, partial, opaque, extra axiom or extern binding.")}</p>'
        f'<p>{t("证明建立在显式的可信基础之上：Lean 内核与检查器、内存与指针运行时模型、C 到 Lean 的人工翻译、选定的上游源码与补丁、构建配置与外部接口模型，以及目标命题本身。开启 AddressSanitizer 与 UndefinedBehaviorSanitizer 的差分测试把翻译与真实 C 逐字节对比，作为一致性的证据（而非证明）。", "Every proof rests on an explicit trusted base: the Lean kernel and checkers, the runtime model of memory and pointers, the hand translation from C, the pinned upstream source and patches, the target build and external-call model, and the goal statements themselves. Differential tests under AddressSanitizer and UndefinedBehaviorSanitizer compare the translation byte-for-byte against the real C as evidence of fidelity, not proof.")}</p>'
        f'</section>'
    )

    top_nav = (
        f'<span class="site-links">'
        f'<a href="#libraries">{t("验证库", "Libraries")}</a>'
        f'<a href="#method">{t("方法", "Method")}</a>'
        f'<a href="#checking">{t("检查机制", "Checking")}</a>'
        f'</span>'
    )
    footer = (
        f'<footer class="site-stamp">'
        f'<a href="https://github.com/cla7aye15I4nd/oss-proof">GitHub</a> · '
        f'<a href="#libraries">{t("验证库与状态", "Libraries and status")}</a>'
        f'</footer>'
    )

    doc = (
        f'<!doctype html><html lang="{lang}"><head>'
        f'<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">'
        f'<title>{html.escape(page_title)}</title>'
        f'<meta name="description" content="{html.escape(lead, quote=True)}">'
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
        f'<a class="article-brand" href="index.html">oss-proof</a>'
        f'<div>{top_nav}<a data-language href="{href(other, current)}" hreflang="{t("en", "zh")}">{t("EN", "中文")}</a></div></nav>'
        f'<div class="rf-layout"><article class="rf-body" id="content">'
        f'<header class="rf-hero"><div class="rf-eyebrow">{t("形式化验证", "FORMAL VERIFICATION")}</div>'
        f'<h1 id="oss-proof">{html.escape(page_title)}</h1><p>{html.escape(lead)}</p></header>'
        f'{body}</article></div>{footer}</main>'
        f'{global_toc(current, lang, page_title, summaries)}</body></html>'
    )
    write_html(current, doc)


def build_portal() -> list[ProjectSummary]:
    OUT.mkdir(parents=True, exist_ok=True)
    copy_shared_static()
    summaries = [summarize_project(p) for p in load_all_projects(REPO)]
    render_root_redirect()
    for lang in ("en", "zh"):
        render_portal_page(lang, summaries)
    print(f"Built oss-proof portal ({len(summaries)} registered project(s))")
    return summaries


if __name__ == "__main__":
    build_portal()

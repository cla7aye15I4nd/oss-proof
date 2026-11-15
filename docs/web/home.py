"""The landing page and the one-screen status summary, both generated from the progress data."""
from __future__ import annotations

from collections import Counter
from pathlib import Path
import html
import json
import re

from book import BOOK
from pagekit import COMMIT, DATE, BRANCH, REPO_URL, route_href
from reference import (OUT, REPO, NOTICE, md, paired_anchors, rewrite, direct_status,
                       progress_targets, shell, translated, write)

RANK = {'open': 0, 'checked': 1, 'registered': 2}
LEVEL = {
    'open': ('未完成', 'open'),
    'checked': ('已检查', 'checked'),
    'registered': ('已登记', 'registered'),
}
# Result number, safety goals that decide it (None: every other required goal), goals linked, statement (zh, en).
# The three safety results and their order are those of AGENTS.md. The round trip of the default
# stream is planned after them and has no row here until it has goals in the manifest.
RESULTS = [
    (1, ('inflate_safety', 'inflate_sequence_safety'), ('inflate_safety', 'inflate_sequence_safety'),
     '`inflate` 对每个输入都安全：没有未定义行为、内存错误、泄漏，并且终止；对每个调用序列和缓冲区的任何切分都成立。',
     '`inflate` is safe on every input: no undefined behaviour, no memory error, no leak, and it terminates, for every call sequence and every split of the buffers.'),
    (2, ('deflate_safety', 'deflate_sequence_safety'), ('deflate_safety', 'deflate_sequence_safety'),
     '`deflate` 对每个输入都安全，对每个调用序列都成立。',
     '`deflate` is safe on every input, for every call sequence.'),
    (3, None, ('compress_safety', 'uncompress_safe', 'gz_sequence_safety', 'gz_refusal', 'inflate_back_sequence_safety'),
     '其余每个有文档的公开函数都安全：`compress*` 与 `uncompress*`、其他流函数、校验和函数、gzip 文件接口和回调解码器 `inflateBack`。',
     'Every other documented public function is safe: `compress*` and `uncompress*`, the other stream functions, the checksums, the gzip file interface and the callback decoder `inflateBack`.'),
]


def required_goals() -> list[str]:
    """Short names of the required goals, as scripts/verification.py defines them."""
    manifest = json.loads((REPO / 'tests/audit/public-api.json').read_text())
    hidden = set(manifest.get('undocumented', {}).get('functions', []))
    required = [a['safety_goal'] for a in manifest['apis'] if a['scope'] == 'lp64-linux' and a['function'] not in hidden]
    required += manifest.get('safety_goals', []) + manifest.get('nonvacuity_goals', [])
    return list(dict.fromkeys(g.rsplit('.', 1)[-1] for g in required))


def result_goals(names) -> tuple:
    if names is not None:
        return names
    taken = {n for _, decided, _, _, _ in RESULTS if decided for n in decided}
    return tuple(n for n in required_goals() if n not in taken)


def target_level(name: str) -> str:
    target = progress_targets().get(name)
    if target is None:
        raise ValueError('Core result names a target missing from the progress data: ' + name)
    return {'registered': 'registered', 'local': 'checked'}.get(target.status, 'open')


def result_level(names) -> str:
    return min((target_level(n) for n in names), key=RANK.get)


def counts() -> Counter:
    return Counter({'registered': 0, 'local': 0, 'open': 0, 'blocked': 0, 'not-planned': 0}) + Counter(t.status for t in progress_targets().values()) + Counter(total=len(progress_targets()))


def evidence_href(name: str, current: Path, lang: str) -> str:
    return route_href('reference/docs/progress', current, lang, progress_targets()[name].anchor)


def badge(level: str, lang: str) -> str:
    return f'<span class="hm-badge hm-{level}">{LEVEL[level][lang == "en"]}</span>'


def inline_code(text: str) -> str:
    return re.sub(r'`([^`]+)`', r'<code>\1</code>', html.escape(text))


def results_table(current: Path, lang: str, detail: bool) -> str:
    zh = lang == 'zh'
    t = lambda a, b: a if zh else b
    rows = []
    for number, decided, shown, cn, en in RESULTS:
        names = result_goals(decided)
        level = result_level(names)
        done = sum(target_level(n) == 'registered' for n in names)
        links = ' · '.join(f'<a href="{evidence_href(n, current, lang)}"><code>{n}</code></a>' for n in shown)
        if len(shown) < len(names):
            links += f' · <a href="{route_href("reference/docs/coverage", current, lang)}">{t("每个函数对应的定理", "the theorem of every function")}</a>'
        rows.append(f'<li class="hm-result"><div class="hm-result-head"><b>{number}</b>{badge(level, lang)}'
                    f'<small>{done}/{len(names)} {t("个必需目标已登记", "required goals registered")}</small></div>'
                    f'<p>{inline_code(cn if zh else en)}</p><p class="hm-links">{t("命题与证据", "statement and evidence")}: {links}</p></li>')
    return '<ol class="hm-results">' + ''.join(rows) + '</ol>'


def levels_note(lang: str) -> str:
    if lang == 'zh':
        return ('<p class="rf-scope-note"><b>未完成</b>：还没有精确定理。<b>已检查</b>：定理在集成分支 <code>dev</code> 上，快速关卡在该提交上全部通过；本页用它专指已检查但尚未登记的定理。'
                '<b>已登记</b>：定理已列入 <code>tests/audit/theorems.txt</code>。只有在某个具名提交上验收套件全部通过后，才可称为<b>已验收</b>；'
                '已验收的提交写在进度记录的“范围”一节，本页的状态只读取登记记录。</p>')
    return ('<p class="rf-scope-note"><b>open</b>: no exact theorem yet. <b>checked</b>: the theorem is on the integration branch <code>dev</code> and the fast gate is green on that commit; this page uses it for a theorem that is checked and not yet registered. '
            '<b>registered</b>: the theorem is listed in <code>tests/audit/theorems.txt</code>. A result is <b>accepted</b> only when the acceptance suite '
            'is green on a named commit. The accepted commits are named in the Scope section of the progress record; the status on this page is read from the registry only.</p>')


ARTICLES = [
    ('read/codec', '一个完整的小编解码器：重复片段、Huffman 编码、规则的传递与终止。从 `ABABABAB` 开始，逐步重建 DEFLATE 的核心。',
     'A complete small codec: repeated passages, Huffman codes, how the rules are transmitted, and how decoding ends. It starts from `ABABABAB` and rebuilds the core of DEFLATE.'),
    ('read/optimizations', 'zlib 如何真正实现并优化压缩与解压：窗口、哈希链、匹配搜索、查表和复制。这是最深入的一篇。',
     'How zlib actually implements and tunes deflate and inflate: window, hash chains, match search, table lookup and copying. The deepest article.'),
    ('read/features', '流式调用、字典、封装、Adler-32 与 CRC-32，以及应用接口：为什么完整缓冲区不够用。',
     'Streaming, dictionaries, wrappers, Adler-32, CRC-32 and the application interface: why complete buffers are not enough.'),
]


def render_home() -> None:
    for lang in ('en', 'zh'):
        zh = lang == 'zh'
        t = lambda a, b: a if zh else b
        suffix = '.zh.html' if zh else '.html'
        current = OUT / ('index' + suffix)
        other = OUT / ('index.html' if zh else 'index.zh.html')
        c = counts()
        body = (f'<section id="results"><h2>{t("三项核心结论", "Three core results")}</h2>'
                f'<p>{t("安全性方面有三项结论，按此顺序验收。下面的状态直接取自登记记录。之后计划证明默认 zlib 流的往返性质（先压缩再解压得到原输入）：条件形式已证明、尚未登记，完备性和无条件形式尚未证明。", "There are three safety results, accepted in this order. The status below is read from the registry. Planned after them: the round trip of the default zlib stream (compressing and then decompressing gives back the input). Its conditional form is proved and not yet registered; completeness and the unconditional form are open.")}</p>'
                + results_table(current, lang, False) +
                f'<p>{t("翻译和运行时模型与 C 相符，这一点靠审阅和测试，不是靠证明：见", "That the translation and the runtime model match the C is reviewed and tested, not proved: see the")} '
                f'<a href="{route_href("reference/docs/trusted-base", current, lang)}">{t("可信基础", "trusted base")}</a>{t("；调用必须满足的条件见", ". The conditions a call must meet are in the")} '
                f'<a href="{route_href("reference/docs/deviations", current, lang)}">{t("偏离记录", "deviations")}</a>{t("。验收（在一个具名提交上全部审计通过）记录在", ". Acceptance (the full audit, green on a named commit) is recorded in")} '
                f'<a href="{route_href("reference/docs/progress", current, lang, "scope")}">{t("范围", "Scope")}</a>{t("。", ".")}</p>'
                + levels_note(lang) +
                f'<p><a href="{route_href("status", current, lang)}">{t("完整状态、计划内与不计划的范围、下一步工作", "Full status, planned and not-planned scope, next work")} →</a></p></section>')
        body += f'<section id="articles"><h2>{t("先读 zlib 本身", "Read zlib first")}</h2><ol class="hm-articles">'
        for number, (route, cn, en) in enumerate(ARTICLES, 1):
            title = BOOK[number - 1]['title'][0 if zh else 1]
            body += f'<li><a href="{route_href(route, current, lang)}">{html.escape(title)}</a><p>{inline_code(cn if zh else en)}</p></li>'
        body += '</ol></section>'
        body += (f'<section id="reference"><h2>{t("参考与证据", "Reference and evidence")}</h2><ul>'
                 f'<li><a href="{route_href("status", current, lang)}">{t("结果与进度", "Results and progress")}</a>: {t("三项结论、范围、下一步", "the three results, scope, next work")}</li>'
                 f'<li><a href="{route_href("reference/index", current, lang)}">{t("规格", "Specifications")}</a>: {t("安全目标、API 契约、格式、可信基础与偏离记录", "safety goals, API contracts, formats, trusted base and deviations")}</li>'
                 f'<li><a href="{route_href("reference/proofs", current, lang)}">{t("证明", "Proofs")}</a>: {t("证明方法与各组件的论证", "method and the argument for each component")}</li>'
                 f'<li><a href="{route_href("reference/docs/glossary", current, lang)}">{t("术语表", "Glossary")}</a> · '
                 f'<a href="{route_href("reference/docs/checking/contributing", current, lang)}">{t("参与贡献", "Contributing")}</a></li></ul></section>')
        lead = t('用 Lean 4 对 zlib 的逐语句翻译作机器检查的证明：默认 x86_64 Linux 构建中每个有文档的公开函数都是安全的，即没有未定义行为、没有内存错误、没有泄漏，并且终止；每条定理都写明自己的前提。',
                 'Machine-checked Lean 4 proofs about a statement-by-statement translation of zlib: every documented public function of the default x86_64 Linux build is safe, with no undefined behaviour, no memory error, no leak, and termination, under the premises each theorem states.')
        redirect = ('<script>(function(){var h=location.hash.slice(1);if(h&&!document.getElementById(h))'
                    f'location.replace("{route_href("read/codec", current, lang)}#"+h)}})();</script>')
        write(current, shell(t('zlib × Lean', 'zlib × Lean'), body + redirect, current, lang, other=other,
                             intro=f'<p>{inline_code(lead)}</p>',
                             eyebrow=t('形式化验证', 'FORMAL VERIFICATION'),
                             description=re.sub(r'`', '', lead)))


# --- status page -----------------------------------------------------------------

def _headings(text: str):
    result, fence = [], None
    for number, line in enumerate(text.splitlines()):
        marker = re.match(r'^\s*(`{3,}|~{3,})', line)
        if marker:
            if fence is None:
                fence = marker[1][0]
            elif fence == marker[1][0]:
                fence = None
        elif fence is None:
            found = re.match(r'^(#{1,6})\s+(.*?)\s*(?:\{#[^}]+\})?\s*$', line)
            if found:
                result.append((number, len(found[1]), found[2]))
    return result


def _cut(text: str, ordinal: int) -> str:
    heads = _headings(text)
    start, level, _ = heads[ordinal]
    end = next((n for n, lv, _ in heads[ordinal + 1:] if lv <= level), len(text.splitlines()))
    return '\n'.join(text.splitlines()[start:end])


def _ordinal(text: str, title: str) -> int:
    return next(i for i, (_, _, name) in enumerate(_headings(text)) if name == title)


def _section(en: str, zh: str | None, title: str) -> tuple[str, str]:
    """The English section and the same section of the Chinese twin, by heading position."""
    ordinal = _ordinal(en, title)
    return _cut(en, ordinal), (_cut(zh, ordinal) if zh else '')


def render_status() -> None:
    source = REPO / 'docs/progress.md'
    english = source.read_text()
    for lang in ('en', 'zh'):
        zh = lang == 'zh'
        t = lambda a, b: a if zh else b
        suffix = '.zh.html' if zh else '.html'
        current = OUT / ('status' + suffix)
        other = OUT / ('status.html' if zh else 'status.zh.html')
        text, fresh = translated(source) if zh else (english, True)
        try:
            scope_en, scope_zh = _section(english, text if zh else None, 'Scope')
            next_en, next_zh = _section(english, text if zh else None, 'Ordered next work')
            if zh and _headings(text)[_ordinal(english, 'Scope')][1] != 2:
                raise ValueError
        except (ValueError, IndexError, StopIteration):
            fresh = fresh and not zh
            scope_zh = next_zh = ''
        use_en = not zh or not fresh
        scope = scope_en if use_en else scope_zh
        nxt = next_en if use_en else next_zh
        scope = re.sub(r'^#+ .*\n', '', scope, count=1)
        nxt = re.sub(r'^#+ .*\n', '', nxt, count=1)
        # Every required goal is registered: keep the paragraph before the table; the page links the full table.
        nxt = re.split(r'\n\n(?=\|)', nxt, maxsplit=1)[0]
        nxt = re.split(r'\n\n(?:Ordered\. |按顺序排列)', nxt, maxsplit=1)[0]
        wrap = lambda s: ('<div lang="en">' + s + '</div>') if (zh and not fresh) else s

        def render(markdown_text: str) -> str:
            html_text, _, _ = md(markdown_text, baselevel=2)
            return rewrite(html_text, source, current, lang)
        c = counts()
        stats = t(f'<code>tests/audit/goals.txt</code> 中共有 {c["total"]} 个目标（必需的安全目标只是其中一部分）：已登记 {c["registered"]}，已检查未登记 {c["local"]}，未完成 {c["open"] + c["blocked"]}，不在计划内 {c["not-planned"]}。这些数字不是工作量的百分比。',
                  f'<code>tests/audit/goals.txt</code> lists {c["total"]} goals (the required safety goals are a part of them): {c["registered"]} registered, {c["local"]} checked but not registered, {c["open"] + c["blocked"]} open, {c["not-planned"]} not planned. These are not a percentage of effort.')
        evidence = route_href('reference/docs/progress', current, lang)
        body = (f'<p class="rf-scope-note">{t("快照", "Snapshot")}: <a href="{REPO_URL}/commit/{COMMIT}"><code>{COMMIT[:10]}</code></a>, {DATE}, '
                f'{t("分支", "branch")} {html.escape(BRANCH)}. {stats}</p>'
                f'<h2 id="core-results">{t("三项核心结论", "Three core results")}</h2>' + results_table(current, lang, True) + levels_note(lang) +
                f'<p class="rf-scope-note">{t("下面的范围表把第三项结论分成四行（3a 到 3d）：整缓冲区函数、回调解码器、gzip 文件接口，以及其余有文档的函数。", "The scope table below splits the third result into four rows (3a to 3d): the whole-buffer functions, the callback decoder, the gzip file interface, and the remaining documented functions.")}</p>' +
                f'<h2 id="scope">{t("计划内与不计划", "Planned and not planned")}</h2>' + wrap(render(scope)) +
                f'<h2 id="next-work">{t("下一步工作", "Next work")}</h2>' + wrap(render(nxt)) +
                f'<p><a href="{route_href("reference/docs/progress", current, lang, "ordered-next-work")}">{t("进度记录中的这一节", "This section in the progress record")}</a></p>'
                f'<h2 id="evidence">{t("证据", "Evidence")}</h2><ul>'
                f'<li><a href="{evidence}">{t("证据索引", "Evidence index")}</a>: {t("每个目标的命题、证明和依赖。", "the statement, proof and dependencies of every target.")}</li>'
                f'<li><a href="{route_href("reference/docs/progress", current, lang, "proof-progress-graph")}">{t("全部目标的依赖图", "Dependency graph of all targets")}</a></li>'
                f'<li><a href="{route_href("reference/docs/trusted-base", current, lang)}">{t("可信基础", "Trusted base")}</a> · '
                f'<a href="{route_href("reference/docs/deviations", current, lang)}">{t("偏离记录：调用者的检查清单", "Deviations: the caller\'s checklist")}</a> · '
                f'<a href="{route_href("reference/docs/coverage", current, lang)}">{t("每个函数对应的定理", "Coverage by function")}</a> · '
                f'<a href="{route_href("reference/docs/model-limits", current, lang)}">{t("模型的限制", "Model limits")}</a> · '
                f'<a href="{route_href("reference/docs/sanitizer-reports", current, lang)}">{t("Sanitizer 报告", "Sanitizer reports")}</a></li></ul>')
        title = t('结果与进度', 'Results and progress')
        write(current, shell(title, (NOTICE if zh and not fresh else '') + body, current, lang, other=other,
                             eyebrow=t('当前状态', 'CURRENT STATUS'),
                             intro=f'<p>{t("三项核心结论的当前状态，以及什么在计划内、什么不在。", "Where the three core results stand, and what is planned and what is not.")}</p>'))


def build_home() -> None:
    render_home()
    render_status()
    print('Built the landing page and the status summary')

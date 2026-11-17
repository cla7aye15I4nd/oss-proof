"""The landing page. The state of each result is computed from the progress data."""
from __future__ import annotations

from pathlib import Path
import html
import re

from book import BOOK
from pagekit import route_href
from progress import functions, goal_done, other_goals, required_goals, roundtrip_goals, state
from reference import OUT, shell, write

# Result number, goals that decide it (None: every other goal of the safety results; (): no goal
# is stated), goals linked, statement (zh, en). The same four rows are on the status page,
# docs/progress.md; tests/test_progress.py compares them.
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
    (4, roundtrip_goals(), ('compress_uncompress_roundtrip', 'stream_roundtrip_total'),
     '默认 zlib 流的往返：`uncompress(compress(x)) = x`；用默认级别的 `deflateInit` 压缩、再用 `inflateInit` 解压，在每一种调用序列下都得到原输入。',
     'The round trip of the default zlib stream: `uncompress(compress(x)) = x`, and compressing with `deflateInit` at the default level and then decompressing with `inflateInit` gives back the input under every call sequence.'),
]


def result_goals(names) -> tuple:
    if names is not None:
        return names
    taken = {n for _, decided, _, _, _ in RESULTS if decided for n in decided}
    return tuple(n for n in required_goals() if n not in taken)


def result_done(names) -> bool:
    """A result with no stated goal is not done."""
    goals = result_goals(names)
    return bool(goals) and all(goal_done(n) for n in goals)


def goal_href(name: str, current: Path, lang: str) -> str:
    """Where the statement of a goal is shown."""
    owner = next((f.name for f in functions() if f.goal == name), None)
    if owner:
        return route_href('reference/functions/' + owner, current, lang, 'safety-target')
    if name not in other_goals() + roundtrip_goals():
        raise ValueError('A result names a goal that is not one of its goals: ' + name)
    return route_href('reference/targets', current, lang, name)


def badge(done: bool, lang: str) -> str:
    return f'<span class="hm-badge hm-{"done" if done else "not-done"}">{state(done, lang)}</span>'


def inline_code(text: str) -> str:
    return re.sub(r'`([^`]+)`', r'<code>\1</code>', html.escape(text))


def results_table(current: Path, lang: str) -> str:
    zh = lang == 'zh'
    t = lambda a, b: a if zh else b
    rows = []
    for number, decided, shown, cn, en in RESULTS:
        links = ' · '.join(f'<a href="{goal_href(n, current, lang)}"><code>{n}</code></a>' for n in shown)
        if decided is None:
            links += f' · <a href="{route_href("reference/docs/progress", current, lang, "functions")}">{t("每个函数的目标", "the goal of every function")}</a>'
        statement = f'<p class="hm-links">{t("命题", "statements")}: {links}</p>' if links else ''
        rows.append(f'<li class="hm-result"><div class="hm-result-head"><b>{number}</b>{badge(result_done(decided), lang)}</div>'
                    f'<p>{inline_code(cn if zh else en)}</p>{statement}</li>')
    return '<ol class="hm-results">' + ''.join(rows) + '</ol>'


def states_note(lang: str) -> str:
    if lang == 'zh':
        return ('<p class="rf-scope-note"><b>完成</b>：存在一条 Lean 定理，它的命题恰好就是这个目标，并且通过了本项目的每一项检查。'
                '<b>未完成</b>：没有这样的定理。</p>')
    return ('<p class="rf-scope-note"><b>Done</b>: a Lean theorem whose statement is exactly the goal exists and passes every check of the project. '
            '<b>Not done</b>: there is no such theorem.</p>')


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
        progress = route_href('reference/docs/progress', current, lang)
        body = (f'<section id="results"><h2>{t("结论", "Results")}</h2>'
                f'<p>{t("前三项是安全结论；第四项是一项功能结论。每一项的状态是完成或未完成。", "The first three are the safety results; the fourth is a functional result. Each one is done or not done.")}</p>'
                + results_table(current, lang) + states_note(lang) +
                f'<p>{t("翻译和运行时模型与 C 相符，这一点靠审阅和测试，不是靠证明：见", "That the translation and the runtime model match the C is reviewed and tested, not proved: see the")} '
                f'<a href="{route_href("reference/docs/trusted-base", current, lang)}">{t("可信基础", "trusted base")}</a>{t("；调用必须满足的条件见", ". The conditions a call must meet are in the")} '
                f'<a href="{route_href("reference/docs/deviations", current, lang)}">{t("偏离记录", "deviations")}</a>{t("；一项完成的结论依靠什么，见", ". What a done result rests on is in")} '
                f'<a href="{route_href("reference/docs/checking/README", current, lang)}">{t("这一页", "its own page")}</a>{t("。", ".")}</p>'
                f'<p><a href="{progress}">{t("每个函数的状态，以及哪些不在计划内", "The state of every function, and what is not planned")} →</a></p></section>')
        body += f'<section id="articles"><h2>{t("先读 zlib 本身", "Read zlib first")}</h2><ol class="hm-articles">'
        for number, (route, cn, en) in enumerate(ARTICLES, 1):
            title = BOOK[number - 1]['title'][0 if zh else 1]
            body += f'<li><a href="{route_href(route, current, lang)}">{html.escape(title)}</a><p>{inline_code(cn if zh else en)}</p></li>'
        body += '</ol></section>'
        body += (f'<section id="reference"><h2>{t("参考", "Reference")}</h2><ul>'
                 f'<li><a href="{progress}">{t("结论的状态", "Status of the results")}</a>: {t("每项结论、每个函数是完成还是未完成", "done or not done, for each result and each function")}</li>'
                 f'<li><a href="{route_href("reference/index", current, lang)}">{t("规格", "Specifications")}</a>: {t("安全目标、API 契约、格式、可信基础与偏离记录", "safety goals, API contracts, formats, trusted base and deviations")}</li>'
                 f'<li><a href="{route_href("reference/proofs", current, lang)}">{t("证明", "Proofs")}</a>: {t("证明方法与各组件的论证", "method and the argument for each component")}</li>'
                 f'<li><a href="{route_href("reference/docs/glossary", current, lang)}">{t("术语表", "Glossary")}</a></li></ul></section>')
        lead = t('用 Lean 4 对 zlib 的逐语句翻译作机器检查的证明：默认 x86_64 Linux 构建中每个有文档的公开函数都是安全的，即没有未定义行为、没有内存错误、没有泄漏，并且终止；每条定理都写明自己的前提。',
                 'Machine-checked Lean 4 proofs about a statement-by-statement translation of zlib: every documented public function of the default x86_64 Linux build is safe, with no undefined behaviour, no memory error, no leak, and termination, under the premises each theorem states.')
        redirect = ('<script>(function(){var h=location.hash.slice(1);if(h&&!document.getElementById(h))'
                    f'location.replace("{route_href("read/codec", current, lang)}#"+h)}})();</script>')
        write(current, shell(t('zlib × Lean', 'zlib × Lean'), body + redirect, current, lang, other=other,
                             intro=f'<p>{inline_code(lead)}</p>',
                             eyebrow=t('形式化验证', 'FORMAL VERIFICATION'),
                             description=re.sub(r'`', '', lead)))


def build_home() -> None:
    render_home()
    print('Built the landing page')

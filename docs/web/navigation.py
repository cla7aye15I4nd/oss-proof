"""The sole navigation surface for the book and its references."""
from pathlib import Path
import html
import os
import re
from book import BOOK, chapter_sections

OUT = Path(__file__).resolve().parent / 'dist'


def global_contents(current, lang, title, toc=''):
    zh = lang == 'zh'
    t = lambda a, b: a if zh else b
    relative = current.relative_to(OUT / lang).as_posix()

    def url(route, anchor=''):
        return os.path.relpath(OUT / lang / (route + '.html'), current.parent).replace(os.sep, '/') + ('#' + anchor if anchor else '')

    def a(route, cn, en, anchor=''):
        mark = ' aria-current="page"' if relative == route + '.html' and not anchor else ''
        return f'<a href="{url(route, anchor)}"{mark}>{html.escape(t(cn, en))}</a>'

    def local_toc():
        return re.sub(r'<li>', '<li data-toc-entry>', toc)

    body = f'''<button type="button" class="bk-global-trigger" data-global-toc aria-controls="book-global-toc" aria-expanded="false" title="{t('打开目录','Open contents')}"><svg viewBox="0 0 20 20" aria-hidden="true"><path d="M3 5h14M3 10h14M3 15h14"/></svg><span>{t('目录','Contents')}</span></button>
<dialog class="bk-global-dialog" id="book-global-toc" aria-labelledby="book-global-title"><div class="bk-global-header"><div><span>ZLIB × LEAN</span><h2 id="book-global-title">{t('目录','Contents')}</h2></div><button type="button" data-toc-close aria-label="{t('关闭目录','Close contents')}">×</button></div>
<div class="bk-global-location"><span>{t('正在阅读','READING NOW')}</span>{html.escape(title)}</div>
<label class="bk-global-search">{t('查找章节或小节','Find a chapter or section')}<input type="search" data-toc-search placeholder="{t('匹配、查表、字典…','Matching, tables, dictionaries…')}" autocomplete="off"></label>
<nav class="bk-global-tree" aria-label="{t('全书目录','Book contents')}">'''
    is_book = False
    for i, item in enumerate(BOOK):
        active = relative == item['route'] + '.html'
        is_book |= active
        body += f'<details class="bk-global-section" data-toc-section {("open" if active else "")}><summary><small>{i+1:02}</small>{a(item["route"], *item["title"])}</summary>'
        if active and toc:
            body += local_toc()
        else:
            body += '<ul>' + ''.join(f'<li data-toc-entry>{a(item["route"], title, title, anchor)}</li>' for anchor, title in chapter_sections(item['key'], lang)) + '</ul>'
        body += '</details>'
    if toc and not is_book:
        body += f'<details class="bk-global-section" data-toc-section open><summary>{t("本页小节","On this page")}</summary>{local_toc()}</details>'
    for cn, en, links in [
        ('接口与文档参考', 'API and documentation', [
            ('api', '全部公开 API', 'All public APIs'),
            ('specifications', '完整文档', 'Complete documentation'),
        ]),
        ('形式化验证参考', 'Formal verification references', [
            ('proof/method', '验证方法', 'Verification method'),
            ('proofs', '实现论证', 'Implementation arguments'),
            ('targets', '目标的命题', 'Statements of the goals'),
            ('sources', 'Lean 源码', 'Lean source'),
            ('progress', '结论的状态', 'Status of the results'),
            ('checking', '完成的结论依靠什么', 'What a done result rests on'),
        ]),
    ]:
        body += f'<details class="bk-global-section" data-toc-section><summary>{t(cn, en)}</summary><ul>'
        for route, cn, en in links:
            body += f'<li data-toc-entry>{a(route, cn, en)}</li>'
        body += '</ul></details>'
    body += f'</nav><p class="bk-global-empty" data-toc-empty hidden>{t("没有匹配的小节。","No matching sections.")}</p></dialog>'
    fallback = ''.join(f'<li>{a(c["route"], *c["title"])}</li>' for c in BOOK)
    return body + f'<noscript><nav class="bk-static-contents" aria-label="{t("章节","Chapters")}"><ol>{fallback}</ol></nav></noscript>'

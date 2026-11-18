"""Three bilingual zlib essays, with separate technical references."""
from hashlib import sha256
from urllib.parse import urlsplit
import html
import re
import textwrap

from markdown import Markdown
from reference import OUT, SITE, REPO, doc_path, href, write
from navigation import global_contents
from pagekit import top_links, stamp, describe
from codec_trace import render_trace
from book import BOOK, chapter_source


def label(pair, lang):
    return pair[lang == 'en']


def page_path(route, lang):
    return OUT / lang / (route + '.html')


def link(route, current, lang, anchor=''):
    return href(page_path(route, lang), current) + ('#' + anchor if anchor else '')


def localize(body, current, lang):
    """Resolve author-facing project URLs without escaping the Pages subpath."""
    def replace(match):
        raw = html.unescape(match.group(1))
        url = urlsplit(raw)
        if url.netloc == 'github.com' and ('/oss-proof/blob/main/projects/zlib/docs/' in url.path or '/zlib-f/blob/main/docs/' in url.path):
            sep = '/oss-proof/blob/main/projects/zlib/docs/' if '/oss-proof/blob/main/projects/zlib/docs/' in url.path else '/zlib-f/blob/main/docs/'
            rel = url.path.split(sep, 1)[1]
            for prefix in ('en/', 'zh/'):
                if rel.startswith(prefix):
                    rel = rel[len(prefix):]
            target = doc_path(REPO / 'docs' / lang / rel, lang)
        elif raw.startswith('/static/'):
            target = OUT / url.path.lstrip('/')
        elif raw.startswith('/') and url.path.endswith('.html'):
            target = OUT / lang / url.path.lstrip('/')
        else:
            return match.group(0)
        result = href(target, current)
        if url.query:
            result += '?' + url.query
        if url.fragment:
            result += '#' + url.fragment
        return 'href="' + html.escape(result, quote=True) + '"'
    return re.sub(r'href="([^"]+)"', replace, body)


def markdown(text, current, lang):
    def example(match):
        name, part = match.groups()
        source = (SITE / 'static/examples' / (name + '.c')).read_text()
        start = '/* BEGIN ' + part + ' */'
        end = '/* END ' + part + ' */'
        if source.count(start) != 1 or source.count(end) != 1:
            raise ValueError('Missing example fragment: ' + name + '#' + part)
        code = textwrap.dedent(source.split(start, 1)[1].split(end, 1)[0]).strip()
        return '\n```c\n' + code + '\n```\n'
    text = re.sub(r'<!-- example:([a-z0-9-]+)#([a-z0-9-]+) -->', example, text)
    parser = Markdown(extensions=['fenced_code', 'tables', 'attr_list', 'toc', 'md_in_html', 'footnotes'])
    return localize(parser.convert(text), current, lang), parser.toc


def shell(title, body, route, lang, *, toc='', number=None):
    current = page_path(route, lang)
    other = page_path(route, 'en' if lang == 'zh' else 'zh')
    t = lambda a, b: a if lang == 'zh' else b
    asset = lambda name: href(OUT / 'static' / name, current)
    names = ['book.css', 'book.js', 'navigation.css', 'navigation.js', 'zlib-essay.js', 'reference.js', 'syntax.css']
    styles = ['base.css', 'zlib-essay.css', 'zlib-search.css', 'zlib-lookup.css', 'zlib-overlay.css', 'zlib-table-proof.css', 'layout.css', 'reference.css', 'book.css', 'navigation.css', 'syntax.css']
    styles += [f'zlib-{scene}-scene.css' for scene in ['roundtrip', 'refill', 'blockcost', 'lengths', 'fastpath', 'checkpoint']]
    styles += ['zlib-playground.css', 'minimal-codec.css', 'deflate-format.css']
    names += styles + ['diagram-view.mjs']
    names += ['zlib-playground.js', 'zlib-playground-model.mjs', 'zlib-playground-worker.js', 'minimal-codec.js', 'minimal-codec-model.mjs', 'deflate-format.js', 'deflate-format-model.mjs']
    names += [p.name for p in (SITE / 'static').glob('zlib-*-scene.*')]
    names += [p.name for p in (SITE / 'static').glob('zlib-*-model.mjs')]
    revision = sha256(b''.join((SITE / 'static' / n).read_bytes() for n in sorted(set(names)))).hexdigest()[:12]
    css = ''.join(f'<link rel="stylesheet" href="{asset(n)}?v={revision}">' for n in styles)
    scripts = f'<script type="module" src="{asset("zlib-essay.js")}?v={revision}"></script>' + ''.join(f'<script defer src="{asset(n)}?v={revision}"></script>' for n in ['reference.js', 'book.js', 'navigation.js'])
    eyebrow = f'{number:02} / {len(BOOK):02}' if number else t('参考', 'REFERENCE')
    return f'''<!doctype html><html lang="{lang}"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>{html.escape(title)} · zlib × Lean</title><meta name="description" content="{html.escape(describe(body,title),quote=True)}"><link rel="icon" href="{asset('favicon.svg')}" type="image/svg+xml">{css}{scripts}</head><body><a class="zl-skip" href="#content">{t('跳到正文','Skip to content')}</a><main class="zl-page bk-page bk-book"><nav class="article-topbar"><a class="article-brand" href="{link('index',current,lang)}">zlib × Lean</a><div>{top_links(current,lang)}<a data-language href="{href(other,current)}">{t('English','中文')}</a></div></nav><header class="bk-hero bk-hero-chapter"><span class="bk-eyebrow">{eyebrow}</span><h1>{html.escape(title)}</h1></header><article id="content" class="bk-article" data-book-chapter="{number or 'reference'}">{body}</article>{stamp(current,lang)}</main>{global_contents(current,lang,title,toc)}</body></html>'''


def render_chapter(item, lang, number):
    current = page_path(item['route'], lang)
    source = chapter_source(item['key'], lang)
    for comparison in ['window', 'search', 'storage']:
        source = source.replace('<!-- comparison:' + comparison + ' -->', render_trace(current, lang, comparison))
    body, toc = markdown(source, current, lang)
    write(current, shell(label(item['title'], lang), body, item['route'], lang, toc=toc, number=number))


def build_reading():
    for lang in ('en', 'zh'):
        for number, item in enumerate(BOOK, 1):
            render_chapter(item, lang, number)
    print('Built three bilingual zlib essays; public API and formal references remain separate')

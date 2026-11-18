"""Three complete zlib essays."""
from functools import lru_cache
from pathlib import Path
import re


def article(key, route, zh, en, sections):
    return {'key': key, 'route': route, 'title': (zh, en), 'anchors': [tuple(s.split('|')) for s in sections.split(';')]}


BOOK = [
    article('foundations', 'read/codec', '基础压缩：LZ77 与 Huffman', 'A complete codec: LZ77 and Huffman',
            'purpose|无损压缩的任务|The lossless task;lz77|重复片段与复制指令|Repeated passages and copies;huffman|符号频率与编码|Symbol frequencies and codes;codebook|传递编码规则|Transmitting the codebook;packet|完整数据表示|The complete packet;decode|独立还原|Independent decoding;deflate|连接 DEFLATE|Connecting to DEFLATE;roadmap|后续需求|What follows'),
    article('optimizations', 'read/optimizations', 'zlib 的实现与优化', 'Implementing and optimizing zlib',
            'costs|基本方案的成本|Costs of the baseline;window|回引范围与存储|References and storage;refill|搬移与补充输入|Sliding and refilling;hash|候选索引|Candidate indexing;search|搜索与预算|Search and budgets;lazy|延迟匹配|Lazy matching;records|记录与频率|Records and frequencies;huffman|构造编码|Constructing codes;lengths|限制码长|Limiting code lengths;canonical|规范编码|Canonical codes;blocks|块选择|Block selection;bits|位写入|Writing bits;storage|存储复用|Reusing storage;decode-bits|读位与预读|Bit input and lookahead;tables|解码表|Decode tables;lookup|查表|Table lookup;copy|复制|Copying;fast|快速路径|The fast path;configuration|配置与取舍|Settings and tradeoffs'),
    article('features', 'read/features', 'zlib 的功能扩展：流式处理与校验', 'Extending zlib: streams and integrity',
            'needs|应用的新需求|Application requirements;stream|持续的任务|A continuing task;buffers|分批输入输出|Input and output batches;flush|刷新与完成|Flush and completion;dictionary|字典|Dictionaries;reset|重置|Reset;copy|复制任务|Copying a task;wrappers|封装|Wrappers;checksums|内容校验|Checking the content;adler|Adler-32|Adler-32;crc|CRC-32|CRC-32;combine|组合分段结果|Combining chunks;interfaces|应用接口|Application interfaces;errors|错误与资源|Errors and resources;program|实际 C 调用|Actual C calls;playground|运行自己的输入|Run your own input'),
]
BY_KEY = {item['key']: item for item in BOOK}
APPENDICES = []
CHECKSUM_PARTS = {'adler', 'crc', 'checksum-proof'}


def route_for(key):
    return BY_KEY[key]['route'] if key in BY_KEY else key


def destination(key, section=''):
    return route_for(key), section


def chapter_source(key, lang):
    route = BY_KEY[key]['route']
    return (Path(__file__).resolve().parents[1] / lang / (route + '.md')).read_text()


@lru_cache(maxsize=6)
def chapter_sections(key, lang):
    source = chapter_source(key, lang)
    return [(anchor, title.replace('`', '').replace('*', ''))
            for title, anchor in re.findall(r'^## (.*?) \{#([^}]+)\}\s*$', source, re.M)]

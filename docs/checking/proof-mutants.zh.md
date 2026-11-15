<!-- source-sha256: 593e7a6f44ddd491ca728ab64f22fa1992e67d2780ea1b9b38e53ec04e7af9ec -->

# 证明变异体

证明变异体是在源码的一份临时副本里，故意放进某个翻译后函数的一处错误。这之后，该函数的证明必须无法通过检查。如果证明仍然通过，说明它并不依赖被改动的那段代码。本页先从头到尾展示一个变异体，再定义术语，然后给出步骤和规则。

变异体被杀死，是证明对这一处修改敏感的证据。它不证明目标覆盖了每一种错误。登记各目标时由哪些行承担证据，是一份带日期的记录：[变异体证据](mutant-evidence.md)。

## 一个变异体，从头到尾

C 函数 `adler32` 把它的参数原样传下去：

```c
uLong ZEXPORT adler32(uLong adler, const Bytef *buf, uInt len) {
    return adler32_z(adler, buf, len);
}
```

变异体 `adler32-wrapper-length` 让翻译传递 `len + 1`。它是列表 `tests/proof-mutants/public-checksums.tsv` 中的一行。一行有五个字段，以制表符分隔：

| 字段 | 这一行中的值 |
| --- | --- |
| `NAME` | `adler32-wrapper-length` |
| `FILE` | `ZlibF/Zlib/adler32.c.lean` |
| `OLD` | `adler32_z adler buf len.toUInt64` |
| `NEW` | `adler32_z adler buf (len.toUInt64 + 1)` |
| `PROOF_MODULES` | `adler32.c,adler32.c.public-any,adler32.c.public-one,public-adler-update` |

这个变异体在目标允许的一个输入上改变了行为。`Goal.adler32_safety` 允许长度为 0 的 `NULL` 缓冲区。长度为 0 时，变异体以长度 1 调用 `adler32_z`；而 `adler32_z` 在长度为 1 时先读取 `buf[0]`，之后才把 `buf` 与 `NULL` 比较。所以变异体通过 `NULL` 读取，任何“`adler32` 是安全的”的证明对它都不可能成立。

运行这一行。第二个参数是作用于名字的正则表达式。

```sh
bash tests/audit/proofmut.sh tests/proof-mutants/public-checksums.tsv '^adler32-wrapper-length$'
```

运行器把工作区及其构建缓存复制到一个临时目录。它先原样构建这四个证明模块；它们必须能构建。然后它在 `FILE` 的副本中把 `OLD` 换成 `NEW`，再构建这四个模块。最后它为这一行打印一行输出：名字、判定、第二次构建的秒数，以及那次构建的第一个错误。

```console
baseline: the listed proof modules build unmutated
adler32-wrapper-length                   KILLED        <N>s error: ZlibF/Proof/<module>.lean:<line>:<column>: ...
1 killed, 0 equivalent (build as expected), 0 known gaps (proofs still build), 0 bad mutants
PROOFMUT PASS
```

第一、第三和第四行是脚本打印的原文。**第二行是示意**：它的版式是脚本的版式，`<N>`、`<module>`、`<line>` 和 `<column>` 代表只有实际运行才能得到的值。这条命令需要 Lean 构建，写本页时没有运行。

判定 `KILLED` 的意思是：第一个错误位于 `PROOF_MODULES` 指定的四个模块之一。错误出在翻译文件本身，或出在别的证明里，对应的是另外的判定，不算数（见[判定](#verdicts)）。

这一行还有第二个用途。文件 `tests/audit/public-mutants.json` 在两个目标之下指定了它：

```json
"ZlibF.Spec.Public.Goal.adler32_safety": [
  {"list": "tests/proof-mutants/public-checksums.tsv", "name": "adler32-wrapper-length"}
]
```

（`Goal.adler32` 之下也有同样的一条。）对每个这样的条目，验收套件取出该目标已登记的证明，把变异后的 `adler32` 替换进去，并在全新的内核中检查结果。内核必须报告类型不匹配。成功时套件打印 `exact public proof rejects: ZlibF.Spec.Public.Goal.adler32_safety: adler32-wrapper-length`（文字取自 `scripts/verification.py`）。

## 发现目标有误的一行

存活下来的变异体就是一项发现。zlib.h 的宏 `gzgetc()` 在 `have` 不为零时从缓冲区读取，否则调用函数 `gzgetc`。行 `macro-have-guard-dropped` 去掉了对 `have` 的测试，于是在缓冲区里什么都没有时也走缓冲路径。它起初存活了下来：`Goal.gz_sequence_safety` 的整个证明仍然能构建。原因在目标：它只在 `have ≠ 0` 时运行这个宏，另一个分支在目标之外。目标在提交 `3c5292f7` 中得到更正（回归测试 `tests/verification/regressions/gz-macro-have-zero.lean`），这一行在 `zlib.h.gzgetc-macro` 中被杀死。

## 术语

| 术语 | 含义 |
| --- | --- |
| 列表 | 由若干行组成的 `.tsv` 文件。列表分在三个目录里（见[下文](#the-three-list-directories)）。 |
| 行 | 一个变异体：例子中的五个字段，加一个可选的标记。 |
| 键 | 某个目标在 `tests/audit/public-mutants.json` 中的条目：该目标已登记的证明必须拒绝的那些行。在其中被指定的行是**带键的行**；有条目的目标是**带键的目标**。 |
| 结构性变异体 | 不在循环体内、也不涉及机器算术的修改：去掉或替换一次调用，去掉一次存储，改变一个常量，返回错误的值。只有结构性变异体才带键（见[第 5 条规则](#a-keyed-row)）。 |
| 重述 | 证明文件中对某个函数代码的一份复写，由一条按展开即成立的等式（`rfl`）与翻译绑定。证明随后对这份复写做推理。 |
| 脚本行 | `FILE` 为 `script:PATH` 的行。脚本在翻译和它的每一处重述中做同样的修改。 |
| 语义列表 | `scripts/verification.py` 的 `SAFETY_MUTANT_LISTS` 中的八个列表之一。它们的行在关于行为的引理中被杀死，而不是在重述处。它们是 `tests/proof-mutants/` 下的 `deflate-header.tsv`、`deflate-strategies.tsv`、`deflate-ops.tsv`、`stream-refusal.tsv`、`infback-sequence.tsv`、`gz-refusal.tsv`、`gz-sequence.tsv` 和 `gz-read.tsv`。 |
| 固定证据 | 对不针对单个函数的必需目标：脚本指定作为其证据的列表和带键的目标（`PINNED_EVIDENCE`）。 |

### 三个列表目录 {#the-three-list-directories}

| 目录 | 内容 | 由谁运行 |
| --- | --- | --- |
| `tests/proof-mutants/` | 公开目标的列表（`public-*.tsv`）、`api-boundary.tsv`，以及八个语义列表和它们的变异脚本。新的行加在这里。 | 验收套件的二十个变异体分片，以及 `verification.py final`。 |
| `tests/audit/proofmut/` | 八个列表，每个 C 文件一个（`adler32.tsv`、`crc32.tsv`、`deflate.tsv`、`inflate.tsv`、`inftrees.tsv`、`trees.tsv`、`trees-out.tsv`、`zutil.tsv`），针对校验和、辅助函数、树、inflate、deflate 和解码表的证明。没有键指定它们。 | 只有 `verification.py final`，以及手动运行。 |
| `tests/proofmut/` | 九个各针对一个专题的小列表。其中三个列表（`crc-updates-public.tsv`、`deflate-default-init.tsv`、`gzip-frontier.tsv`）的行有键指定；分片运行这三个。那里的 `.py` 文件是独立的检查，没有任何工作流运行它们。 | 分片运行那三个列表；`verification.py final` 运行全部九个。 |

## 判定 {#verdicts}

`proofmut.sh` 为每一行打印下列判定之一。

| 判定 | 含义 |
| --- | --- |
| `KILLED` | 第一个错误位于预期的证明模块。变异检查通过。 |
| `SAME ok` | 标为等价的变异仍能构建。应审查等价的理由。 |
| `GAP (known)` | 已记录的证明缺口在开发模式下存活。它不算覆盖，严格验收时失败。 |
| `SURVIVED` | 没有标记的变异仍能构建。应调查是缺少覆盖还是变异等价。 |
| `BAD MUTANT` | 翻译，或证明目录之外的文件，出了错。应修复这个变异。 |
| `WRONG PLACE` | 另一个证明先失败。这不满足指定函数的检查。 |
| `SORRY` | 变异后的副本含有 `sorry`。应修复这个变异。 |
| `NO ERROR` | 构建失败，却没有可识别的错误，重试一次后仍然如此。没有确立证明拒绝了变异。 |
| `UNEXPECTED` | 标为等价的变异失败了。应审查标记和变异。 |
| `NOT APPLIED` | 替换文本没有恰好出现一次，或内容没有改变，或变异脚本失败。应更新这个变异。 |

被杀死的变异如果还带着过时的 `gap:` 标记，也算失败。缺口补上之后要去掉这个标记。

## 添加变异体

1. 选择列表。将来要带键的、针对公开函数的结构性变异体，放在 `tests/proof-mutants/` 下的列表中（例如 `public-safety.tsv`）。位于循环体内或涉及机器算术的变异体，以及需要成对修改的变异体，放在语义列表中。
2. 添加一行，字段以制表符分隔。以 `#` 开头的行是注释。

   ```text
   NAME <TAB> FILE <TAB> OLD <TAB> NEW <TAB> PROOF_MODULES [<TAB> same:REASON | gap:REASON]
   ```

   | 字段 | 含义 |
   | --- | --- |
   | `FILE` | 翻译源码相对于仓库根目录的路径，例如 `ZlibF/Zlib/adler32.c.lean`。也可以是 `script:PATH`：运行器调用 `python3 PATH <copy> NAME` 来生成变异体；这时 `OLD` 和 `NEW` 写作 `-`。 |
   | `OLD`、`NEW` | 替换文本。字面的 `\n` 表示换行；`OLD` 在 `FILE` 中恰好出现一次。 |
   | `PROOF_MODULES` | `ZlibF/Proof` 下的路径，用逗号分隔，不带 `.lean`，指明该函数的证明。只构建这些模块。 |
   | 可选的标记 | `same:` 说明变异体为什么等价；`gap:` 记录缺少的覆盖，只用于开发。带键的行中两者都不允许。 |

3. 用列表运行器运行这一行，并读它的判定。

   ```sh
   bash tests/audit/proofmut.sh tests/proof-mutants/public-safety.tsv '^deflatePrime'
   ```

4. 对带键的行，在 `tests/audit/public-mutants.json` 中该目标之下添加 `{"list": ..., "name": ...}`，然后检查这个键。

   ```sh
   python3 scripts/verification.py coverage
   ```

5. 对没有键的目标，在 `PINNED_EVIDENCE` 中添加它的条目或提高其中的数目。这是对 `scripts/` 的改动，要经过审查。

有用的变异会去掉一个检查或一次赋值，改变一个界限或一次比较，改动一个下标或一次移位，或者返回错误的结果。应在一个已证明的函数里选择不同的部位。语法错误不是证据。必需的变异体确实在某个允许的输入上改变了行为，这一点由审查确立；上面的例子对长度为 0 的 `NULL` 就是这样做的。

## 运行检查

在仓库根目录，有已构建好的 `.lake` 缓存时运行：

```sh
python3 scripts/verification.py mutants
python3 scripts/verification.py mutants --shard-count 20 --shard-index 3
bash tests/audit/proofmut.sh tests/audit/proofmut/adler32.tsv
bash tests/audit/proofmut.sh tests/audit/proofmut/crc32.tsv '^combine'
```

第一条命令先构建项目。然后，对每个带键的目标，它检查解析出的变异边界，重放原来的精确证明，再重放每个带键的行。之后它以严格模式运行 `api-boundary.tsv`、各语义列表，以及键所引用的每个列表。第二条命令运行二十个分片中的一个，与 CI 的做法相同。最后两条各运行一个列表，可以按变异体的名字筛选。它们在开发时有用，不能代替验收。

**分片。**带键的目标按名字顺序分给各分片；一个目标未改动的证明的重放，与它全部带键的行在同一个分片。各列表中没有标 `same:` 的行轮流分配，所以没有哪一行被漏掉或运行两次。无事可做的分片会被拒绝。

**列表运行器**把工作区和已构建好的缓存复制到一个临时目录。它原样构建列出的证明模块，把每个替换恰好应用一次，并且只构建指定的模块。报告的第一个错误必须位于预期的证明模块。原来的缓存保持不变。一次只运行一个变异体。

**严格模式**（`PROOFMUT_STRICT=1`）强制进行未改动的构建，拒绝每个 `gap:` 行，并要求至少有一个 `KILLED` 行；能构建的 `same:` 行不是证据。每个 `same:` 行所在的分片，同时还运行同一列表中某个必须被杀死的行。没有这种行的列表会被拒绝。跳过了未改动构建的运行不能用来支持验收。

**运行器设置。**`PROOFMUT_CACHE` 选择已构建好的缓存。`PROOFMUT_TIMEOUT` 设定每次构建的秒数，默认 3600。`PROOFMUT_KEEP=1` 保留临时副本；`PROOFMUT_SHOWLOG=1` 打印失败的细节。`PROOFMUT_BASELINE=0` 跳过未改动的构建，只用于本地诊断。`PROOFMUT_STRICT=1` 使这个跳过设置失效。

**哪里运行什么。**夜间套件运行这二十个分片。一个列表如果没有键引用它，又不是语义列表或 `api-boundary.tsv`，分片就不运行它；它只在 `python3 scripts/verification.py final` 中运行，后者以严格模式运行三个目录中的每个列表。没有运行过的列表不算通过的检查。

## 两种检查

| 检查 | 做什么 | 何时算作拒绝 |
| --- | --- | --- |
| 重新繁释（`tests/audit/proofmut.sh`） | 把列表中的一行应用到工作区的副本上，并构建该行指定的证明模块。 | 第一个错误位于这些证明模块之一（`KILLED`）。 |
| 内核重放（`zlibf-proof-replay`） | 取出某个目标已登记的精确证明，在全新的内核中，只把改动过的源码声明替换进它的依赖闭包。 | 内核报告类型不匹配。原来的证明先被接受。 |

套件运行的每个列表的每一行都经过重新繁释。带键的行还要另外经过内核重放。对重放来说，一个无关的定理失败，或一个带额外前提的更强定理失败，都不够。超时或内核资源错误不算拒绝。

这与 `tests/selftest.sh` 中的差分自测不同：后者要求靠比较执行结果来发现变异。只被测试发现的变异体，可能暴露出证明覆盖的缺失。验收套件防御什么、不防御什么，见[验证策略](../anti-cheating.md)。

## 哪些目标需要哪种证据

| 目标 | 审计要求的证据 |
| --- | --- |
| 公开函数的功能目标 `Goal.<function>`，在它已被证明时 | `public-mutants.json` 中的一个键，至少有一行。 |
| 函数自己的安全目标（`Goal.<function>_safety` 或 `_safe`），在它已被证明时 | 它自己的键。 |
| 不针对单个函数的已证明必需目标：四个序列安全目标、三个拒绝目标和四个非空性目标 | `scripts/verification.py` 的 `PINNED_EVIDENCE` 中的固定证据。 |

针对单个公开函数的已证明目标如果没有键，会被拒绝。脚本为此设有一个豁免列表（`MUTANT_COVERAGE_PENDING`）；它是空的，审计拒绝新增的条目。已证明的必需目标如果既没有键也没有固定证据，会被拒绝。

**固定证据。**十一个已证明的必需目标没有自己的键。对其中每一个，脚本固定了承担其证据的语义列表，每个列表附有必须被杀死的最少行数；还固定了一些带键的目标，它们的重放同时也检查这个目标：它们的证明是这个目标的推论，或与它共用运行引理。每个固定的列表都是变异体分片会运行的列表。每个固定的带键目标至少有一行。固定的带键目标可以是功能目标；下表最后两行各指定了一个。

| 目标 | 固定的列表（必须杀死的最少行数） | 固定的带键目标 |
| --- | --- | --- |
| `Goal.gz_sequence_safety` | `gz-sequence.tsv`（43）、`gz-read.tsv`（18） | 无 |
| `Goal.inflate_back_sequence_safety` | `infback-sequence.tsv`（11） | 无 |
| `Goal.deflate_sequence_safety` | `deflate-header.tsv`（5）、`deflate-strategies.tsv`（10）、`deflate-ops.tsv`（7） | `Goal.deflate_safety`、`Goal.deflateEnd_safety` |
| `Goal.inflate_sequence_safety` | 无 | `Goal.inflate_safety`、`Goal.inflateEnd_safety`、`Goal.inflateCopy_safety` |
| `Goal.inflate_refusal`、`Goal.deflate_refusal` | `stream-refusal.tsv`（5） | 无 |
| `Goal.gz_refusal` | `gz-refusal.tsv`（19） | 无 |
| `Goal.inflate_initialisation_domain` | 无 | `Goal.inflateInit2__safety` |
| `Goal.deflate_initialisation_domain` | 无 | `Goal.deflateInit2__safety` |
| `Goal.inflate_back_initialisation_domain` | `infback-sequence.tsv`（11） | `Goal.inflateBackInit_`（功能目标） |
| `Goal.gz_sequence_nonvacuity` | `gz-sequence.tsv`（43） | `Goal.gzdopen`（功能目标） |

表中的列表都在 `tests/proof-mutants/` 下。

## 规则

### 带键的行 {#a-keyed-row}

带键的行满足以下全部条件。脚本检查第 1 到第 4 条；重放预算保证第 5 条。

1. 列表是三个列表目录之一中的 `.tsv` 文件，名字恰好选中一行。
2. 该行的文件是带键函数的翻译源码。旧文本在该文件中恰好出现一次，位于函数体内，并且与新文本不同。签名保持不变。一个解析器检查两个版本，不加载候选的导入。
3. 该行没有 `same:` 或 `gap:` 标记，并且指定了证明模块。
4. 修改另一个函数、只改规格、注入声明，都不算。
5. **该行是结构性变异体：它不修改循环体，也不修改机器算术。**这两类变异体放在没有键的列表中，由重新繁释检查。

有第 5 条，是因为内核重放不能在预算之内驳倒每一种变异。只有内核报告类型不匹配，它才算拒绝了一个变异。有两类修改反而让内核无止境地工作：

- 修改自由变量上的机器算术，例如把 `x - left` 改成 `x - len`。为了驳倒它，内核把 `UInt64` 和 `UInt32` 的运算一直展开到 `Nat` 上的取模，却没有可以计算的值。在 `uncompress2_z` 上实测：806 s 后达到 12 GiB 的预算。
- `cdoWhile` 循环体内的任何修改，哪怕只是去掉一个测试。两个循环体匹配失败之后，内核在两边展开 `cdoWhile`。它的燃料递归随后一次展开一轮迭代，并在每一步重新比较循环体。在 `compress2_z` 上实测：467 s 后达到 12 GiB 的预算；去掉一个测试的变异 214 s 后达到 16 GiB。

结构性的修改很快就被拒绝。在 `uncompress2_z` 和 `compress2_z` 上，每个这样的行用 120 s 到 200 s，约 10.5 GB。超出预算（12 GiB 常驻内存；`ZLIBF_REPLAY_RSS_MB` 可以改变它）的重放会被终止并判为失败，失败信息提示把这一行移走。依赖闭包变大时不提高预算；解决办法是缩小重放的闭包。

列表中也保留算术变异体和循环体变异体，每个变异体分片都用重新繁释检查它们；这时证明在关于行为的引理处失败。`tests/proof-mutants/api-boundary.tsv` 就是例子：`uncompress2_z-destLen-count` 和两个 `refill-off-by-one` 行由重新繁释检查。意图相同而修改是结构性的行承担内核重放：`uncompress2_z-destLen-drop`（错误的 `destLen` 计数），以及两个 `initial-room` 行（输出空间超过剩余的量）。

### 重述与脚本行

有些证明对函数的一份重述做推理。只在一个文件里修改这种函数，会先在把重述与翻译绑定的那条等式处失败。这只说明证明与翻译绑定在一起。脚本行解决这个问题：它的脚本在翻译和它的每一处重述中做同样的修改，于是只有关于行为的引理才会失败。脚本行不能带键（第 2 条），所以它放在语义列表中。

### 冻结的行

语义列表和 `tests/proof-mutants/api-boundary.tsv` 的行，沿[防止悄悄删除的规则](goals.md#shrink-only-rules)所用的提交链冻结：每个字段都算，包括 `PROOF_MODULES` 列和标记，还包括脚本行的变异脚本的 sha256。可以添加行。修改或删除一行，需要在 `tests/audit/registry-removals.json` 中有 `mutant_rows` 条目 `{list, name, reason}`；什么也不豁免的条目会被当作过时条目拒绝。

已证明目标的键所含的引用以同样的方式受保护：没有 `mutant_references` 条目 `{goal, list, name, reason}`，引用不能消失，被引用的行也不能改变它的文件、旧文本或新文本。因此，提交者如果不在差异中留下理由，就不能删掉某个目标的键，不能把它的行减到只剩一行，也不能把某一行换成更弱的行。

有语义列表缺失或为空时，分片失败。

## 已知局限 {#known-limits}

- 审计器（`tests/audit/*.lean`）、`proofmut.sh`、`selftest.sh` 和变异脚本（`tests/proof-mutants/*.py`）是被信任的，与 `scripts/` 一样靠审查来保护。变异脚本的内容由它的哈希冻结，但它做了什么，只能靠阅读来检查。特别是，`proofmut.sh` 的 `BAD MUTANT` 防护把第一个错误与该行的 `FILE` 相比较，而脚本行的 `FILE` 就是脚本本身；所以，把错误写进预期证明模块的变异脚本会被算作 `KILLED`。要堵上这一点，需要重新设计脚本行；防御手段是审查。
- 带理由的删除条目是每条防删除规则经过审查的出口。它在差异中可见，过时的条目会被拒绝。
- 提交链覆盖 `HEAD` 仍然包含的、固定起点之后的历史。在起点之后改写 `dev` 的强制推送能绕过它；防御手段是禁止强制推送的分支保护。
- 一次杀死只说明证明对一处修改敏感。它不说明目标覆盖了每一种错误；有某个列表存在，或有过某个更早的结果，也不证明它的 C 文件中每个函数都被覆盖。
- 在重述处被拒绝的行，说明证明与翻译绑定在一起，不说明证明依赖被变异的那个检查。语义列表就是为覆盖这种情况而设的。
- **gz 目标的选择谓词只能靠阅读来检查。** 接受句柄的 gz 函数，其安全目标把序列目标的一个子句限制到这个函数的调用上。这是用一个选择谓词做到的：一个关于调用的谓词，即 `ZlibF/Spec/Safety/GzCalls.lean` 中 `GzCallSafety` 或 `GzCloseCallSafety` 的参数。没有任何检查把选择谓词与函数绑在一起。限制后的子句对每个选择谓词都已证明（`ZlibF/Proof/public-gz-call-safety.lean` 中的 `call_safety` 和 `close_safety`），所以，即使某个目标的选择谓词点的是另一个函数，这个目标仍然会被证明，也仍然与它的定理精确匹配。清单文件按目标的名字把函数与目标绑定。带键的行的重放同样不看选择谓词：被变异的函数在序列定理的证明内部失败，而每个这样的目标都使用这条序列定理。29 个选择谓词各自点的是自己的函数，这一点是靠阅读这 29 个命题确立的。同一个目标的拒绝子句直接调用该函数，所以没有这个局限。
- gz 函数 `gzoffset`、`gztell`、`gzseek`、`gzgetc_` 和 `gzprintf` 只是把句柄传给另一个函数，再转换结果。它们的带键的行改的是传下去的句柄，或者是结果。它们所到达的代码的证据，在被调用函数的键里（`tests/proof-mutants/public-gz-safety.tsv` 的文件头）。

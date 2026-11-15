<!-- source-sha256: d8e69e7c253088f65dd24ad6eaea6095a4731dc956c24a13d8319125d8845ca4 -->
# 证明参考：组件、页面、定理

本节每一页对应一个 C 文件，说明关于它的定理为什么成立。本页是地图：哪一页解释哪条定理，定理在哪里，处于哪个层级。读者只要熟悉 C，把 `zlib/` 下对应的文件打开对照，不读 Lean 也应当能读懂每一页。

每一个必需的安全目标，都有一条类型与它完全相同的已登记定理。必需集合里没有未完成的目标。每条定理假设了什么，写在它自己的页面和[偏离记录](../deviations.md)里；模型本身假设了什么，写在[可信基础](../trusted-base.md)和[模型的限制](../model-limits.md)里。

初次阅读请先看[图解导读](../overview.md)。术语见[术语表](../glossary.md)。

## 状态层级

这些页面用三个词说明一条定理的状态。[术语表](../glossary.md#status)给出定义，[检查](../checking/README.md#three-levels)说明每个层级背后有哪些检查，以及读者在哪里能看到它。

- **已检查。** 定理在集成分支 `dev` 上，并且快速关卡在该提交上全部通过：所有模块都能构建，没有 `sorry`，也没有被禁止的构造。Lean 的内核检查过这个证明。
- **已登记。** 定理还列在 `tests/audit/theorems.txt` 中，它的目标列在 `tests/audit/proved-goals.txt` 中。验收检查会审计这份清单里的定理：逐条核对定理的类型与目标是否一致，并检查它依赖的公理。
- **已验收。** 定理已登记，并且验收检查在一个指明的提交上全部通过。这个提交是 `bde170e9`（[进度，范围](../progress.md#scope)）。`inflate` 和 `deflate` 的四个初始化目标在那之后被放宽了；它们以放宽后的形式已登记，而已验收的是它们在那次提交上的形式。

已检查而未登记的定理，是某条已登记定理的证明内部的引理。页面提到这类定理时会说明。对已登记定理的公理检查会沿着依赖关系往下查，所以也覆盖这些引理。

差分测试属于验收检查。它把翻译与编译出来的 C 做比较，是翻译忠实于 C 的证据，不是证明。

这些页面上的文字是解释，不是被检查的对象。凡是页面给出了对 C 的某种解读、而没有定理陈述它的地方，都标有 **尚未由证明确认**。每个组件页面把这类内容集中在“没有定理陈述的 C 解读”一节。

## 必需与非必需

必需的结论是安全性结论：对默认 x86_64 Linux 构建中每一个有文档的公开函数，在它的调用序列上，没有未定义行为，没有内存错误，没有泄漏，并且会终止。这些目标在 `ZlibF/Spec/Safety/` 中；gzip 文件接口和回调解码器的目标在 `ZlibF/Spec/Public/GzSafety.lean`、`ZlibF/Spec/Public/GzRefusal.lean` 和 `ZlibF/Spec/Public/Sequences.lean` 中。

功能结论说的是函数算出了什么：校验和的值、解码出的字节。它们不是安全结论所必需的。其中许多已经证明并登记，每个页面都单列一节说明。有两个功能目标 `Goal.inflate` 和 `Goal.deflate`，被其他函数的安全证明用到。见[安全与功能的划分](../design/safety-functional-split.md)。

其他构建配置，以及 `zlib.h` 列为“未写入文档”的函数，都不是必需的；原因见[进度，范围](../progress.md#scope)。

## 序列定理覆盖什么

*序列*定理说的是一个流上每一串被允许的调用，而不是某一次调用。例如：

```c
deflateInit(&strm, level);
while (more_input) {
    strm.next_in = in;   strm.avail_in = n;      /* 调用者修改四个字段 */
    strm.next_out = out; strm.avail_out = m;
    deflate(&strm, Z_NO_FLUSH);                  /* 返回值任意 */
}
deflate(&strm, Z_FINISH);
deflateEnd(&strm);
```

`deflate_sequence_safety` 覆盖这个程序在任意压缩级别、任意缓冲区大小、任意输入下的运行，也覆盖由 `deflateInit2_`、各个 `deflate*` 调用和这类字段修改组成的其他任何程序。它说：每次调用都返回且不出故障，调用改动的内存就是它有权改动的内存，并且在任何时刻调用 `deflateEnd` 都会释放全部内存。

## 地图

所有模块都在 `ZlibF/Proof/` 下。本表提到的每一条定理都已登记在 `tests/audit/theorems.txt` 中。

| C 文件 | 页面 | 必需的安全定理 | 模块 |
| --- | --- | --- | --- |
| `adler32.c` | [Adler-32](adler32.md) | `adler32_safety`、`adler32_z_safety`、`adler32_combine_safety`、`adler32_combine64_safety` | `public-stateless-safety.lean` |
| `crc32.c` | [CRC-32](crc32.md) | `crc32_safety`、`crc32_z_safety`、`crc32_combine_safety`、`crc32_combine64_safety`、`crc32_combine_gen_safety`、`crc32_combine_gen64_safety`、`crc32_combine_op_safety` | `public-stateless-safety.lean` |
| `zutil.c` | [工具函数与分配](zutil.md) | `zlibVersion_safety`、`zlibCompileFlags_safety` | `public-stateless-safety.lean` |
| `inftrees.c` | [解码表](inftrees.md) | 没有公开函数。内部定理：`inflate_table_safe`、`inflate_table_decoder_safe` | `inftrees.c.lean`、`inftrees.c.decoder-safe.lean` |
| `inffast.c` | [快速解码](inffast.md) | 没有公开函数。内部定理：`inflate_fast_safe` | `inffast.c.final.lean` |
| `inflate.c` | [流式解码](inflate.md) | 序列定理：`inflate_sequence_safety_public`。每个函数一条：`inflate_safety` 和另外九条。此外有 `inflateInit__safety`、`inflateInit2__safety`、`inflateCopy_safety`、`inflate_refusal`，以及非空性定理 `inflate_initialisation_domain_public` | `public-inflate-sequence-safety.lean`、`public-stream-call-safety.lean`、`public-init-safety.lean`、`public-inflate-copy-safety.lean`、`public-stream-refusal.lean`、`public-inflate-init.lean` |
| `deflate.c` | [流式压缩](deflate.md) | 序列定理：`deflate_sequence_safety`。每个函数一条：`deflate_safety` 和另外十二条。此外有 `deflateInit__safety`、`deflateInit2__safety`、`deflate_copy_safety`、`deflate_refusal`，以及非空性定理 `deflate_initialisation_domain_public` | `public-deflate-goals.lean`、`public-stream-call-safety.lean`、`public-init-safety.lean`、`public-deflate-copy.lean`、`public-stream-refusal.lean`、`public-deflate-init-domain.lean` |
| `trees.c` | [树与块输出](trees.md) | 没有公开函数。它的引理服务于 `deflate_sequence_safety`。已登记的有：`tinyOverlayAt_256`、`tinyOverlayAt_128`（最小的两个 `memLevel` 下共享缓冲区的界）、`gen_bitlen_safe`、`pqdownheap_safe` | `deflate.c.engine.overlay-header-ref.lean`、`trees.c.heap.*.lean` |
| `infback.c` | [回调解码器](callbacks.md) | 序列定理：`inflate_back_sequence_safety`。非空性：`back_init_domain_public` | `infback.c.safety-fast.lean`、`public-infback-init.lean` |
| `gzlib.c`、`gzread.c`、`gzwrite.c`、`gzclose.c` | [Gzip 文件](gzip.md) | 序列定理：`gz_sequence_safety_public`。`NULL` 句柄：`gz_refusal`。非空性：`gz_sequence_nonvacuity_public` | `public-gz-sequence-safety.lean`、`public-gz-refusal.lean`、`public-gz-sequence-nonvacuity.lean` |
| `compress.c` | [`compress*` 的安全性](compress-safety.md) | `compress_safety`、`compress_z_safety`、`compress2_safety`、`compress2_z_safety`；界函数对应 `compressBound`、`compressBound_z` | `public-compress-safe-mid.lean`、`public-compress-bound.lean` |
| `uncompr.c` | [`uncompress*` 的安全性](uncompress-safety.md) | `uncompress_safe`、`uncompress_z_safe`、`uncompress2_safe`、`uncompress2_z_safe` | `public-uncompress-safe.lean` |

31 个 gz 函数和三个 `inflateBack` 函数的安全性，是通过各自的序列定理证明的。它们还没有单独的、针对一个函数的目标。这不是未完成的证明：序列目标覆盖了这些函数的每一次调用，清单 `tests/audit/public-api.json` 也把序列目标写作它们每一个的安全目标。

`trees.c` 页面解释的引理中，有一些已检查而未登记，其中包括 `memLevel` 为 3 到 9 时共享缓冲区的界（`dynamic_overlay_mid`、`dynamic_overlay_large`）。每条引理的层级见[树](trees.md#results)页面。

## 本节的其他页面

| 页面 | 内容 |
| --- | --- |
| [证明一个函数](method.md) | 方法：一个证明要说明什么，不变量、帧性质、所有权，以及证明卡住时怎样诊断 |
| [解码器的源码笔记](inflate-source-notes.md)、[压缩器的源码笔记](deflate-source-notes.md) | 翻译必须严格照做的 C 细节。它们是解读，不是定理 |
| [默认配置引擎](deflate-default-engine.md) | 早先针对一种配置得到的 `deflate` 功能结论 |
| [缓冲区工具函数](buffers.md) | 对 `compress.c`、`uncompr.c` 和界函数的解读，两个安全性页面依赖它们 |
| [早先的论证与参考来源](../history/references.md) | 从一个早先的开发到现有模块的对照表，保存在历史部分。它是复用记录，不提供任何证明 |

修正过的命题的记录在 `docs/history/` 中。其中两份涉及早先关于 `deflate` 的功能目标 `DeflateCompletes`：[结束之后的输入](../history/deflate-completion-input.md)和[空输出](../history/deflate-completion-null-output.md)。

## 功能结论

这些页面也解释了一些不是安全结论所必需的结论。它们都已登记。

| 页面 | 解释的功能结论 |
| --- | --- |
| [Adler-32](adler32.md)、[CRC-32](crc32.md) | 校验和的值和合并公式 |
| [解码表](inftrees.md)、[快速解码](inffast.md) | 表项就是规范编码；快速循环的一轮解码出格式中的一个记号 |
| [流式解码](inflate.md) | `Goal.inflate`，一次调用的完整契约（`inflate_public`） |
| [流式压缩](deflate.md) | `Goal.deflate`，一次调用的完整契约（`Zlib.Deflate.Universal.deflate_safety`） |
| [默认配置引擎](deflate-default-engine.md) | 在默认配置下：已完成的流能解码回它的输入（`DeflateCore.correct`） |

## 组件页面的结构

`inflate.c`、`inffast.c`、`inftrees.c`、`deflate.c` 和 `trees.c` 的页面各节相同。

1. **结论。** 定理、所在模块和层级。
2. **假设。** 主定理的每一条前提。
3. **不变量**，逐个子句用白话说明。
4. **每一步为什么保持它**，并指出承担这一步的定理。
5. **循环为什么会结束**：哪个度量在下降。
6. **难点在哪里。**
7. **没有定理陈述的 C 解读。**
8. **功能结论**（如果有）。

## 阅读顺序

解压方向：先读[解码表](inftrees.md)，再读[快速解码](inffast.md)，最后读[流式解码](inflate.md)。建表给出两个解码器都依赖的表形状，流式解码器建立快速路径的入口条件。

压缩方向：先读[流式压缩](deflate.md)，了解窗口和哈希链；再读[树](trees.md)，了解建树以及输出与符号共用的缓冲区。

gzip 文件接口和回调解码器建立在这些之上，它们的页面放到最后读。

## 约定

区间 `[a, b)` 包含 `a`，不包含 `b`。指针可以指向数组末尾之后的一个位置，但不能读那个位置。无符号运算像 C 一样回绕。有符号运算是带检查的：溢出在模型中是故障。

页面上出现三类标识符。

- `U1` 到 `U12` 是安全义务：十类未定义行为，加上终止和泄漏（[安全性](../spec/safety.md)）。
- `F1` 到 `F9` 是多个证明共用的结构性事实（[方法](method.md#structural-facts-used-by-several-proofs)）。
- `I-*` 是函数之间的内部契约（[内部契约](../spec/internal-contracts.md)）。

它们是义务和事实的名字，不是状态。

依赖默认构建的位宽、表或分配器的界，只对该构建成立。模型的整数规则和指针规则见[翻译语义](../design/translation.md)。

[证据索引](../progress.md)列出每一个目标的陈述、定理和依赖。

<!-- source-sha256: b8e216b429b9ec5ae101ce65b7453a60f18017a89fedacb22c684309c7f85b62 -->
# 证明参考：组件、页面、定理

本节每一页对应一个 C 文件，说明关于它的定理为什么成立。本页是地图：哪一页解释哪条定理。读者只要熟悉 C，把 `zlib/` 下对应的文件打开对照，不读 Lean 也应当能读懂每一页。

这些页面提到的每个安全目标都已完成：有一条类型与它完全相同的定理，Lean 内核检查过它的证明。[进度](../progress.md)列出每一项结论。每条定理假设了什么，写在它自己的页面和[偏离记录](../deviations.md)里；模型本身假设了什么，写在[可信基础](../trusted-base.md)和[模型的限制](../model-limits.md)里。

初次阅读请先看[总览](../overview.md)。术语见[术语表](../glossary.md)。

## 定理、引理与解读

页面提到定理和引理。目标的定理，类型与目标完全相同。引理是这样一条定理的证明内部的一步；页面提到引理时会说明。两者都经过 Lean 内核检查。

差分测试把翻译与编译出来的 C 做比较，是翻译忠实于 C 的证据，不是证明。

这些页面上的文字是解释，不是被检查的对象。凡是页面给出了对 C 的某种解读、而没有定理陈述它的地方，都标有 **尚未由证明确认**。按[同一个提纲](#the-shape-of-a-component-page)编排的页面把这类内容集中在“没有定理陈述的 C 解读”一节。

## 必需与非必需

必需的结论是安全结论：对默认 x86_64 Linux 构建中每一个有文档的公开函数，在它的调用序列上，没有未定义行为，没有内存错误，没有泄漏，并且会终止。两个 `compressBound` 契约陈述上界的值；它们充当这两个函数的安全目标。

功能结论说的是函数算出了什么：校验和的值、解码出的字节。它们不是安全结论所必需的。其中许多有定理，每个页面都把它们单独列在一节里。其中两个，`Goal.inflate` 和 `Goal.deflate`，被其他函数的安全证明用到。

其他构建配置，以及 `zlib.h` 列为未文档化的函数，都不是必需的；原因见[进度](../progress.md#not-planned)。

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

| C 文件 | 页面 | 必需的安全定理 |
| --- | --- | --- |
| `adler32.c` | [Adler-32](adler32.md) | `adler32_safety`、`adler32_z_safety`、`adler32_combine_safety`、`adler32_combine64_safety` |
| `crc32.c` | [CRC-32](crc32.md) | `crc32_safety`、`crc32_z_safety`、`crc32_combine_safety`、`crc32_combine64_safety`、`crc32_combine_gen_safety`、`crc32_combine_gen64_safety`、`crc32_combine_op_safety` |
| `zutil.c` | [工具函数与分配](zutil.md) | `zlibVersion_safety`、`zlibCompileFlags_safety` |
| `inftrees.c` | [解码表](inftrees.md) | 没有公开函数。内部定理：`inflate_table_safe`、`inflate_table_decoder_safe` |
| `inffast.c` | [快速解码](inffast.md) | 没有公开函数。内部定理：`inflate_fast_safe` |
| `inflate.c` | [流式解码](inflate.md) | 序列定理：`inflate_sequence_safety_public`。每个函数一条：`inflate_safety` 和另外九条。此外有 `inflateInit__safety`、`inflateInit2__safety`、`inflateCopy_safety`、`inflate_refusal`，以及非空性定理 `inflate_initialisation_domain_public` |
| `deflate.c` | [流式压缩](deflate.md) | 序列定理：`deflate_sequence_safety`。每个函数一条：`deflate_safety` 和另外十二条。此外有 `deflateInit__safety`、`deflateInit2__safety`、`deflate_copy_safety`、`deflate_refusal`，以及非空性定理 `deflate_initialisation_domain_public` |
| `trees.c` | [树与块输出](trees.md) | 没有公开函数。它的引理服务于 `deflate_sequence_safety`。关于内部步骤的定理有：`tinyOverlayAt_256`、`tinyOverlayAt_128`（最小的两个 `memLevel` 下共用缓冲区的界）、`gen_bitlen_safe`、`pqdownheap_safe` |
| `infback.c` | [回调解码器](callbacks.md) | 序列定理：`inflate_back_sequence_safety`。每个函数一条：`inflateBackInit__safety`、`inflateBack_safety`、`inflateBackEnd_safety`。非空性：`back_init_domain_public` |
| `gzlib.c`、`gzread.c`、`gzwrite.c`、`gzclose.c` | [Gzip 文件](gzip.md) | 序列定理：`gz_sequence_safety_public`。每个函数一条：`gzread_safety` 以及另外 31 条。`NULL` 句柄：`gz_refusal`。非空性：`gz_sequence_nonvacuity_public` |
| `compress.c` | [`compress*` 的安全性](compress-safety.md) | `compress_safety`、`compress_z_safety`、`compress2_safety`、`compress2_z_safety`；两个上界函数的定理与函数同名：`compressBound`、`compressBound_z` |
| `uncompr.c` | [`uncompress*` 的安全性](uncompress-safety.md) | `uncompress_safe`、`uncompress_z_safe`、`uncompress2_safe`、`uncompress2_z_safe` |

31 个 gz 函数、`gzvprintf` 和三个 `inflateBack` 函数，也各有一条单函数的安全定理。它把所属一族的序列定理用到一个函数的调用上，并且包括这个函数的拒绝：对接受句柄的 gz 函数是 `NULL` 句柄；对 `inflateBack` 和 `inflateBackEnd` 是 `NULL` 流和状态为 `NULL` 的流记录，对 `inflateBackEnd` 还有 `zfree` 为 `NULL`。`inflateBackInit_` 的定理覆盖 `zlib.h` 允许的每一次调用，不需要历史。

`inflate.c` 和 `deflate.c` 的单函数定理（初始化除外）同样有这两部分：对 `NULL` 流或不一致的流的拒绝，以及对可达流的调用。两条复制定理在对 `NULL` 参数的拒绝之外，还有对不一致的源的拒绝。`inflate_refusal` 和 `deflate_refusal` 各用一个命题陈述若干函数的拒绝（见 [inflate](inflate.md#refusals)、[deflate](deflate.md#refusals)）。

`trees.c` 页面解释的其他结论，是 `deflate_sequence_safety` 的证明内部的引理，其中包括 `memLevel` 为 3 到 9 时共用缓冲区的界（`dynamic_overlay_mid`、`dynamic_overlay_large`）。每一条见[树](trees.md#results)页面。

## 本节的其他页面

| 页面 | 内容 |
| --- | --- |
| [证明一个函数](method.md) | 方法：一个证明要说明什么，不变量、帧性质、所有权，以及内核检查和测试各提供什么 |
| [解码器的源码笔记](inflate-source-notes.md)、[压缩器的源码笔记](deflate-source-notes.md) | 翻译必须严格照做的 C 细节。它们是解读，不是定理 |
| [默认配置引擎](deflate-default-engine.md) | 针对一种配置的 `deflate` 功能结论 |
| [缓冲区工具函数](buffers.md) | 对 `compress.c`、`uncompr.c` 和上界函数的解读，两个安全性页面依赖它们 |

## 功能结论

这些页面也解释了一些不是安全结论所必需的结论。这张表里的每一项结论都有定理。

| 页面 | 解释的功能结论 |
| --- | --- |
| [Adler-32](adler32.md)、[CRC-32](crc32.md) | 校验和的值和合并公式 |
| [解码表](inftrees.md)、[快速解码](inffast.md) | 表项就是规范编码；快速循环的一轮解码出格式中的一个记号 |
| [流式解码](inflate.md) | `Goal.inflate`，一次调用的完整契约（`inflate_public`） |
| [流式压缩](deflate.md) | `Goal.deflate`，一次调用的完整契约（`Zlib.Deflate.Universal.deflate_safety`） |
| [默认配置引擎](deflate-default-engine.md) | 在默认配置下：按格式规格，已完成的流的输出是它的输入的一个合法 zlib 流，并且流能够被完成（`DeflateCore.correct`） |
| [往返](roundtrip.md) | 默认 zlib 流的往返：`uncompress(compress(x)) = x`，以及先 `deflate` 再 `inflate` 在每一种调用序列下都得回输入（`Goal.compress_uncompress_roundtrip`、`Goal.stream_roundtrip_total`） |

## 组件页面的结构

`inflate.c`、`inffast.c`、`inftrees.c`、`deflate.c` 和 `trees.c` 的页面按同一个提纲编排。对某个文件没有内容的节，它的页面就不设；有些页面另有自己的节。

1. **结论。** 定理以及每条定理陈述什么。
2. **假设。** 主定理的每一条前提。
3. **不变量**，逐个子句用白话说明。
4. **每一步为什么保持它**，并指出承担这一步的定理。
5. **循环为什么会结束**：哪个度量在下降。
6. **难点在哪里。**
7. **没有定理陈述的 C 解读。**
8. **功能结论**（如果有）。

`inftrees.c` 和 `trees.c` 的页面没有不变量一节；它们的论证在“每一步为什么安全”一节里。`trees.c` 的页面没有功能结论一节。

## 阅读顺序

解压方向：先读[解码表](inftrees.md)，再读[快速解码](inffast.md)，最后读[流式解码](inflate.md)。建表给出两个解码器都依赖的表形状，流式解码器确立快速路径的入口条件。

压缩方向：先读[流式压缩](deflate.md)，了解窗口和哈希链；再读[树](trees.md)，了解建树以及输出与符号共用的缓冲区。

gzip 文件接口和回调解码器建立在这些之上，它们的页面放到最后读。

## 约定

区间 `[a, b)` 包含 `a`，不包含 `b`。指针可以指向数组末尾之后的一个位置，但不能读那个位置。无符号运算像 C 一样回绕。有符号运算是带检查的：溢出在模型中是故障。

页面上出现三类标识符。

- `U1` 到 `U12` 是安全义务：十类未定义行为，加上终止和泄漏（[安全性](../spec/safety.md)）。
- `F1` 到 `F9` 是多个证明共用的结构性事实（[方法](method.md#structural-facts-used-by-several-proofs)）。
- `I-*` 是函数之间的内部契约（[内部契约](../spec/internal-contracts.md)）。

依赖默认构建的位宽、表或分配器的界，只对该构建成立。模型的整数规则和指针规则见[翻译语义](../design/translation.md)。

<!-- source-sha256: e90399f1dbb931262d7216077d74278f1079a9a15ee6b450efc588eddaf09528 -->
# 安全目标与功能目标

一个目标是一个关于 zlib 的 Lean 命题。目标分两类。**安全目标**说的是一次调用返回时没有未定义行为、没有内存错误、没有泄漏，并且调用会终止，这些都是在文档规定的定义域上说的。**功能目标**说的是这次调用算出了什么。本项目必需的结果是安全目标。本页说明这两类目标怎样分开，每组函数的安全目标是什么形式，以及哪些命题属于功能部分。哪些目标已经完成，见[状态页](../progress.md)。

## 安全目标不使用功能规格

安全目标的命题用到 C 的翻译、运行时，以及两类目标共用的定义：调用、历史、帧、参数、平台前提，以及流和 gzip 文件句柄的不变量（`Good`、`DGood`、`GzInv`）。它不用格式模型，不用 API 模型，也不用功能契约。Lean 模块的安排使这一点自然成立：陈述安全目标的模块，以及陈述共用定义的模块，都不导入功能规格的任何模块，直接导入和经由其他模块的导入都没有。所以读者不读任何功能规格，就能读完这些安全目标。

有一个例外：`compressBound` 和 `compressBound_z` 的目标提到 API 模型的公式 `compressBound`（共五行），并且写在功能规格之中（[见下文](#two-goals-per-public-function)）。

两类目标都在规格中陈述，规格的模块都不导入证明模块，直接导入和经由其他模块的导入都没有。所以一个目标的命题要在规格中读，也要在规格提到的翻译、运行时和数学中读，但从不在证明中读。关于 `Good`、`DGood` 和 `GzInv` 的引理在证明中；它们的定义不在。

关于公开函数的目标，不论是哪一类，Lean 名字都是 `ZlibF.Spec.Public.Goal.<name>`。

## 每个公开函数两个目标

`zlib.h` 中每个有文档、且在默认构建中的函数，有一个安全目标和一个功能目标。[安全性，“目标在哪里”](../spec/safety.md#where-the-goals-are)列出每个函数的安全目标。安全目标有三种形式。

- **不带流的调用**（校验和、`zlibVersion`、`zlibCompileFlags`、`compress*`、`uncompress*`）：在文档规定的定义域上，调用无故障地返回，只写声明的调用者区域，存活块保持原样。
- **流函数**（inflate 族和 deflate 族）：每个函数一个目标。它陈述的是：在一个流的每个可达历史上，再调用一次这个函数；以及对 `NULL` 流或不一致的流的拒绝。四个初始化函数不需要历史：它们的目标覆盖 `zlib.h` 允许的每一次调用（`InitArguments`）。`Goal.inflate_refusal` 和 `Goal.deflate_refusal` 各用一个命题陈述若干函数的拒绝。`Goal.inflate_sequence_safety` 和 `Goal.deflate_sequence_safety` 各用一个命题陈述一族的每个调用序列的安全：不变量在每个可达的流上成立，再调用一次是安全的，结束调用释放流所拥有的东西。
- **gzip 文件接口和 `inflateBack`**：同样是每个函数一个目标。每个目标把所属一族的序列目标（`Goal.gz_sequence_safety` 或 `Goal.inflate_back_sequence_safety`）的一个子句限制到一个函数上。它还带有这个函数的拒绝：对接受句柄的 gz 函数是 `NULL` 句柄；对 `inflateBack` 和 `inflateBackEnd` 是 `NULL` 流和状态为 `NULL` 的流记录，对 `inflateBackEnd` 还有 `NULL` 的 `zfree`。`Goal.gz_refusal` 用一个命题陈述各个 gz 函数对 `NULL` 句柄的拒绝。`Goal.inflateBackInit__safety` 覆盖 `zlib.h` 允许的每一次调用，与其他初始化目标一样。这两个序列目标也是安全目标。一直读到输入结束的 gz 调用，是在“它的描述符只交付有界数量的字节”这个前提（`ReadsFinite`）下证明会返回的；没有这个前提时，目标说的是这次调用除 `Fault.outOfFuel` 之外没有别的故障（[外部 I/O](external-io.md#the-os-oracle)）。

没有两个函数共用一个安全目标。

特殊情况：

- `compressBound` 和 `compressBound_z` 以它们的完整契约 `Goal.compressBound` 和 `Goal.compressBound_z` 作为安全目标。它们的翻译是纯函数，没有堆，也没有故障，所以单独的安全目标会按定义成立。每个契约说的是：对每个 64 位参数，翻译后的函数返回 API 模型的公式 `compressBound` 的值。
- `zlib.h` 列为未文档化的函数没有安全目标；其中的 `gzopen_w` 不在默认构建中，它没有任何目标。例外是 `gzvprintf`，它有 `Goal.gzvprintf_safety`。
- 四个 `uncompress*` 目标以 `_safe` 结尾；其他每个单函数安全目标都以 `_safety` 结尾。

流目标的强度取决于它的可达历史集合。四个非空性目标为每一族给出一个可达的见证：`Goal.inflate_initialisation_domain`、`Goal.deflate_initialisation_domain`、`Goal.inflate_back_initialisation_domain` 和 `Goal.gz_sequence_nonvacuity`。第五个目标 `Goal.inflateBack_call_domain` 为回调协议给出一个见证：针对每种协议的目标，强度取决于协议的集合。这五个目标与安全目标一样是必需的。`Goal.gz_initialisation_domain` 不在其中：它陈述的是 `gzopen` 的功能契约，不在计划内。

## 哪些属于功能部分

- 每个函数的结果契约 `Goal.<function>`，包括 gzip 文件接口的结果契约。
- 完整的序列契约 `Goal.inflate_sequence`、`Goal.deflate_sequence`、`Goal.inflate_back_sequence` 和 `Goal.gz_sequence`。前两个把所属一族的序列安全与功能子句合在一起。后两个陈述所属一族的生命周期，连同功能契约；`Goal.gz_sequence` 只针对操作系统的普通文件行为（`RegularOs`）这样陈述。
- 格式模型和 API 模型，以及它们的目标。名为 `ZlibF.Spec.Api.Goal.<name>` 的目标（例如 `ZlibF.Spec.Api.Goal.roundtrip`）是关于 API 模型的命题，不是关于翻译后的 C 的命题；例外是 `compress_bound_value` 和 `compress2_z_first_alloc_failure`，它们说的是翻译后的 `compress.c`。名为 `ZlibF.Spec.Token.Goal.<name>` 的目标是关于格式模型中符号格式的命题。
- 关于内部函数、并且用到格式模型的命题，例如关于解码表和快速解码器、谈到解码出的字节的命题，以及关于 CRC-32、提到格式模型的 `crc32Update` 的命题。关于内部函数而不用格式模型的命题属于共用部分，不属于功能部分。

完整契约 `Goal.X` 是 `X` 的功能目标。`X` 的安全目标是写在它旁边的另一个命题。

默认 zlib 流的往返未完成，也没有目标定义。它的一个有条件的形式有一条定理 `deflate_inflate_roundtrip`，定理的内容见[架构](architecture.md#the-layers)。

[设计](README.md) · [文档首页](../README.md)

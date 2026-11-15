<!-- source-sha256: 364d6f2756f43b472807e442a486d62c5fbb676623d087eadce9341e6d2b7ed4 -->
# 证明参考：组件、页面与定理

本节每一页解释一个 C 组件相关定理背后的论证。本页是地图：哪一页解释哪条定理，定理在哪个模块，处于什么状态。

每一页都交代三件事。

- **已证明什么。** 项目要求的每个安全目标都有一条已登记的定理，其类型与目标完全一致。各页给出这些定理的名称及其在 `ZlibF/Proof/` 下的 Lean 模块。
- **假设了什么。** 每条定理都明确写出前提。比 `zlib.h` 更窄的前提在[偏差记录](../deviations.md)中各占一行。模型本身见[可信基础](../trusted-base.md)。
- **还有什么未完成。** 要求的安全目标中没有未完成项。功能正确性不在计划内；[进度](../progress.md#scope)列出不在计划内的目标及原因。

初次阅读请先看[图解指南](../overview.md)。术语见[术语表](../glossary.md)。

## 状态等级

[AGENTS.md](../../AGENTS.md) 定义了两个等级，本节只在该含义下使用它们。

- **已检查。** 定理位于 `main`，且该提交的快速检查通过：全部模块可构建，没有 `sorry`，也没有禁用构造。
- **已接受。** 定理还列在 `tests/audit/theorems.txt` 中，并且验收套件在一个指明的提交上通过。

下表中的定理都列在 `tests/audit/theorems.txt` 中。验收套件在提交 `bde170e9` 上通过（[进度，范围](../progress.md#scope)），因此它们在该提交上是已接受的。差分测试属于该套件，它们是忠实性的证据，不是证明。

这些页面上的文字论证只是解释，不是经过检查的定理。页面对 C 源代码的某种解读若没有被证明直接陈述，文中会注明该处尚未完成确认；各页的写法是“尚未完成”或“仍需证明”。

## 必需与非必需

项目范围是安全性：对默认 x86_64 Linux 构建中每个有文档的公开函数及其调用序列，没有未定义行为，没有内存错误，没有泄漏，并且终止。安全目标位于 `ZlibF/Spec/Safety/`；gzip 文件接口和回调解码器的安全目标位于 `ZlibF/Spec/Public/GzSafety.lean`、`ZlibF/Spec/Public/GzRefusal.lean` 和 `ZlibF/Spec/Public/Sequences.lean`。

功能性结果说明函数算出了什么：校验和的值、解码出的字节、往返一致。它们不是必需的。其中许多在范围调整之前已经证明，并继续保持登记。各页会说明每个结果属于安全还是功能。安全证明用到的功能性事实仍在范围内，主要例子是单次调用的完整契约 `Goal.inflate` 和 `Goal.deflate`。见[安全与功能的划分](../design/safety-functional-split.md)。

## 地图

所有模块路径都在 `ZlibF/Proof/` 下。“序列”表示该定理覆盖每一个允许的调用历史，而不只是一次调用。

| 组件 | 页面 | 必需的安全定理 | 模块 |
| --- | --- | --- | --- |
| `adler32.c` | [Adler-32](adler32.md) | `adler32_safety`、`adler32_z_safety`、`adler32_combine_safety`、`adler32_combine64_safety` | `public-stateless-safety.lean` |
| `crc32.c` | [CRC-32](crc32.md) | `crc32_safety`、`crc32_z_safety`、`crc32_combine_safety`、`crc32_combine64_safety`、`crc32_combine_gen_safety`、`crc32_combine_gen64_safety`、`crc32_combine_op_safety` | `public-stateless-safety.lean` |
| `zutil.c` | [工具函数与分配](zutil.md) | `zlibVersion_safety`、`zlibCompileFlags_safety` | `public-stateless-safety.lean` |
| `inftrees.c` | [解码表](inftrees.md) | 没有公开函数。内部定理：`inflate_table_safe`、`inflate_table_decoder_safe` | `inftrees.c.lean`、`inftrees.c.decoder-safe.lean` |
| `inffast.c` | [快速解码](inffast.md) | 没有公开函数。内部定理：`inflate_fast_safe` | `inffast.c.final.lean` |
| `inflate.c` | [流解码](inflate.md) | 序列：`inflate_sequence_safety_public`。逐函数：`inflate_safety` 及其他 `inflate*_safety` 定理、`inflateInit__safety`、`inflateInit2__safety`、`inflateCopy_safety`。拒绝：`inflate_refusal`。非空泛性：`inflate_initialisation_domain_public` | `public-inflate-sequence-safety.lean`、`public-stream-call-safety.lean`、`public-init-safety.lean`、`public-inflate-copy-safety.lean`、`public-stream-refusal.lean`、`public-inflate-init.lean` |
| `deflate.c` | [流压缩](deflate.md) | 序列：`deflate_sequence_safety`。逐函数：`deflate_safety` 及其他 `deflate*_safety` 定理、`deflateInit__safety`、`deflateInit2__safety`、`deflate_copy_safety`。拒绝：`deflate_refusal`。非空泛性：`deflate_initialisation_domain_public` | `public-deflate-goals.lean`、`public-stream-call-safety.lean`、`public-init-safety.lean`、`public-deflate-copy.lean`、`public-stream-refusal.lean`、`public-deflate-init-domain.lean` |
| `trees.c` | [树与块输出](trees.md) | 没有公开函数。它的引理服务于 `deflate_sequence_safety`。重叠缓冲区余量：`dynamic_overlay_large`、`dynamic_overlay_mid`、`tinyOverlayAt_256`、`tinyOverlayAt_128` | `trees.c.universal-block.lean`、`trees.c.universal-overlay-mid.lean`、`deflate.c.engine.overlay-header-ref.lean` |
| `infback.c` | [回调解码器](callbacks.md) | 序列：`inflate_back_sequence_safety`。非空泛性：`back_init_domain_public` | `infback.c.safety-fast.lean`、`public-infback-init.lean` |
| `gzlib.c`、`gzread.c`、`gzwrite.c`、`gzclose.c` | [Gzip 文件](gzip.md) | 序列：`gz_sequence_safety_public`。`NULL` 句柄：`gz_refusal`。非空泛性：`gz_sequence_nonvacuity_public` | `public-gz-sequence-safety.lean`、`public-gz-refusal.lean`、`public-gz-sequence-nonvacuity.lean` |
| `compress.c` | [`compress*` 的安全性](compress-safety.md) | `compress_safety`、`compress_z_safety`、`compress2_safety`、`compress2_z_safety`。界限函数：`compressBound`、`compressBound_z` | `public-compress-safe-mid.lean`、`public-compress-bound.lean` |
| `uncompr.c` | [`uncompress*` 的安全性](uncompress-safety.md) | `uncompress_safe`、`uncompress_z_safe`、`uncompress2_safe`、`uncompress2_z_safe` | `public-uncompress-safe.lean` |

另有两页属于同一批组件。

- [缓冲区工具](buffers.md)解读 `compress.c`、`uncompr.c` 和界限函数的 C 代码，记录两页安全性证明所依赖的源代码决定。
- [证明一个函数](method.md)解释方法：契约、不变量、帧、所有权，以及证明卡住时如何诊断。

31 个 gz 函数和 3 个 `inflateBack` 函数的逐函数安全目标尚未陈述。在此之前，清单 `tests/audit/public-api.json` 把两个序列目标登记为这些函数各自的安全目标。

## 保留的功能性结果

这些页面还解释了一些非必需的结果。它们是早先证明的，继续保持登记。

| 页面 | 所解释的功能性结果 |
| --- | --- |
| [Adler-32](adler32.md)、[CRC-32](crc32.md) | 校验和的值与组合公式 |
| [解码表](inftrees.md)、[快速解码](inffast.md) | 表项实现规范码；一个快速步骤细化一个格式记号 |
| [流解码](inflate.md) | `Goal.inflate`，单次调用的完整契约（`inflate_public`） |
| [流压缩](deflate.md) | `Goal.deflate`，单次调用的完整契约（`Zlib.Deflate.Universal.deflate_safety`） |
| [Deflate 完成性：空输出](../history/deflate-completion-null-output.md)、[Deflate 完成性：结束后的输入](../history/deflate-completion-input.md) | 早先功能性目标 `DeflateCompletes` 的两个反例。它们是一次陈述修正的记录，不是必需结果 |

[早期论证与参考来源](references.md)把一个早期开发映射到当前模块。它是复用记录，不提供任何证明。

## 阅读顺序

解压部分：先读校验和与分配两页，再读解码表、快速解码器和流解码器。流解码器建立快速路径的入口条件；表构造建立两个解码器共用的谓词。

压缩部分：先读校验和与分配两页，再读[流压缩](deflate.md)了解窗口和哈希链，然后读[树](trees.md)了解树构造、位输出，以及输出与符号共用的缓冲区。这个共用缓冲区上的界限属于内存安全。

gzip 文件接口和回调解码器建立在流解码器和压缩器之上，它们的页面放在最后读。

## 约定

区间 `[a, b)` 包含 `a`，不包含 `b`。数组指针可以形成末尾后一位置，但不能读取该位置。无符号运算按 C 回绕。证明若需要普通算术，就要说明回绕不改变结果。

标识符 `U1`–`U12`、`F1`–`F9` 和 `I-*` 把推理与[安全规范](../spec/safety.md)、[方法](method.md)和[内部契约](../spec/internal-contracts.md)联系起来。它们命名的是义务，不表示状态。

由默认构建的位宽、表或分配器分支得到的界限只对该构建成立。整数、对象和控制流的共用规则见[翻译语义](../design/translation.md)。gzip 的外部世界由[外部 I/O 模型](../design/external-io.md)定义。

[证据索引](../progress.md)列出每个目标的陈述、证明和依赖。

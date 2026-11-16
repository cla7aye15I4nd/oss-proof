<!-- source-sha256: e2b21dbb54006c7b3d4bbb23f4a4439472bef45db78b7d5ea64b5c2ef4cd7cca -->
# 总览：关于 zlib 证明了什么

本页说明本项目关于 zlib 证明了什么、假设了什么、状态记录在哪里，以及证明是怎样搭起来的。要点是：默认 x86_64 Linux 构建中每个有文档的公开函数，都被证明在任何调用序列里是安全的；这是对 C 的一份 Lean 翻译证明的，前提是每条定理自己写明的条件。加粗的词在[术语表](glossary.md)中有定义。

<a id="proving-the-zlib-implementation"></a>

## 结论

**已证明。** zlib 的默认 x86_64 Linux 构建中，每个有文档的公开函数都是安全的。对其前提所容许的每个输入，翻译后的调用都会返回，没有未定义行为，没有内存错误，只写它获准写的内存（它的帧），不泄漏，并且终止。这对调用序列也成立：对 inflate 流、deflate 流、回调解码器和 gzip 文件句柄的每段历史都成立。这里的每一句话都是一个目标，由一个类型与该目标完全相同的定理证明；每个函数对应的定理见[按函数查覆盖情况](coverage.md)。

**所作假设。** 这些定理说的是一份运行在运行时模型上的 Lean 翻译。有六件事是被信任而没有被证明的（[可信基础](trusted-base.md)）：

1. Lean 内核、三条标准公理，以及审计程序；
2. 关于内存、指针、故障和循环的运行时模型；
3. 对 C 的手工翻译；
4. 选定的源码：固定版本的 `zlib/` 加上各个[补丁](../patches/README.md)；
5. 构建配置，以及分配、文件和格式化的模型；
6. 命题本身：每个目标说的确实是它该说的。

差分测试是忠实度的证据，不是证明。编译器、操作系统和硬件的正确性在证明之外。定理对调用者提出的前提列在[偏离记录](deviations.md)中，按函数排成核对清单。

**状态。** 每项结论的层级（已检查、已登记还是已验收）、每次验收运行所在的提交、目标的个数，以及剩余的工作，只记录在一个页面上：[进度页的“范围”一节](progress.md#scope)。

**并非必需。** 安全结论不需要功能正确性。有计划内的安全证明依赖某个功能性事实时，该事实在范围内；已经证明的部分保留。有一项功能结论是计划内的工作：默认 zlib 流先经 `deflate` 再经 `inflate` 的往返。它的条件形式说的是：两条调用序列都到达 `Z_STREAM_END` 时，输出等于输入。在它之后是完备性（空间足够时两边一定能结束）和无条件形式。仅关于模型的命题（说的是抽象 API 模型，而不是翻译后的 C）、其他构建配置，以及 `zlib.h` 声明为未文档化的函数，都不在计划内。[范围](progress.md#scope)列出每一组及其理由，并说明往返性质进行到哪一步。

## 目录

- [结论](#the-claim)
- [证明是怎样搭起来的](#how-the-proof-is-built)
- [怎样读一项结论](#how-to-read-a-result)
- [导读各章](#guide-chapters)
- [各条规则写在哪里](#where-each-rule-is-written)

## 证明是怎样搭起来的

<a id="shared-proof-rules"></a>
<a id="argument"></a>
<a id="1-what-must-be-proved"></a>
<a id="3-what-must-be-proved-and-why"></a>
<a id="7-how-the-arguments-become-checked-claims"></a>
<a id="3-how-the-proof-is-built"></a>
<a id="31-translate-the-actual-c-execution"></a>
<a id="32-establish-an-invariant-by-initialization"></a>
<a id="33-preserve-it-through-calls"></a>
<a id="34-relate-executions-to-byte-meaning"></a>
<a id="4-the-inflate-argument"></a>
<a id="5-how-the-proof-is-built"></a>
<a id="5-the-deflate-argument"></a>
<a id="51-translate-the-actual-c-execution"></a>
<a id="52-establish-an-invariant-by-initialization"></a>
<a id="53-preserve-it-through-calls"></a>
<a id="54-relate-executions-to-byte-meaning"></a>
<a id="6-the-inflate-argument"></a>
<a id="7-the-deflate-argument"></a>
<a id="73-establish-preserve-and-compose"></a>

证明分四步。

1. **翻译。** 固定版本的 C 加上已登记的补丁，由人手工逐条语句翻译成 Lean。C 可能到达的每一种未定义行为，在翻译里都成为故障 `Fault.ub`。
2. **定义不变量。** 对每一类流定义一个不变量：在每次调用之前都成立的、关于流状态的事实。以 inflate 流为例：窗口是 `NULL`，或者是一个恰好 `2^wbits` 字节的可写块，其中有效字节的个数（`whave`）不超过它的大小（`WinInv`）。
3. **逐个函数证明。** 证明初始化函数建立这个不变量。对其余每个函数，证明它在不变量成立时返回而不出故障，保持不变量，只写它的帧，并且分配和释放的恰好是它的账本所记的那些块。不假设任何函数的行为：每个被调用的函数都有一条关于它自己的翻译的定理。
4. **组合。** 对调用历史作归纳，就得到序列目标。End 函数被证明会释放流拥有的每一个块。另有一条非空性定理给出一个具体的堆，在它上面初始化成功，所以这些前提不是空的。

```mermaid
flowchart LR
    S["固定版本的 C 与补丁"] -->|"手工翻译"| T["Lean 翻译"]
    T --> I["init：建立不变量"]
    I --> V["不变量成立"]
    V -->|"任意一次调用：不出故障，只写它的帧"| V
    V --> E["End：释放拥有的每个块"]
```

[通用方法](proof/method.md)详细给出这个归纳，[实现论证](proof/README.md)给出每个 C 组件的不变量。

## 怎样读一项结论

<a id="evidence"></a>
<a id="6-reading-a-formal-result"></a>
<a id="61-find-its-exact-statement"></a>
<a id="62-follow-its-proof-and-evidence"></a>
<a id="8-reading-a-formal-result"></a>
<a id="81-find-its-exact-statement"></a>
<a id="82-follow-its-proof-and-evidence"></a>
<a id="74-locate-the-exact-evidence"></a>

一项结论有四个部分：目标、它的前提、证明它的定理，以及它的层级。下面以 `inflate` 为例。

| 部分 | 对 `inflate` 而言 |
| --- | --- |
| 目标 | `Goal.inflate_safety`，在 `ZlibF/Spec/Safety/Streams.lean` 中 |
| 它说了什么 | 两个子句。调用子句：对每个堆、每个流 `r` 和每个 `flush` 值，只要前提成立，调用 `inflate(r, flush)` 就返回而不出故障，保持不变量，只写流自己的块、流记录、挂接的 gzip 头部和输出范围，并且存活块集合的变化与它的账本完全一致（`StreamCallSafe`）。拒绝子句：对 `NULL` 流或不一致的流，调用返回 `Z_STREAM_ERROR`，不写原先存活的任何块，存活块的集合保持原样 |
| 前提 | 调用子句的前提是 `StreamCallDomain`：流是可达的（有一段从成功的初始化开始的历史产生了它）；每个字节对象都小于 2^63 字节；缓冲区符合[偏离记录](deviations.md#stream-calls-inflate-and-deflate)的描述（`StreamArguments`）。拒绝子句的前提是：流是被拒绝的流（`RefusedInflate`，见[偏离记录，注 2](deviations.md#note-2-refused-streams)），并且模型的堆在下一个未用块号及其之后没有存活的块（`Fresh`） |
| 定理 | `ZlibF.Spec.Public.StreamCallSafetyProof.inflate_safety`，在 `ZlibF/Proof/public-stream-call-safety.lean` 中 |
| 层级 | 已检查、已登记或已验收（见[术语表](glossary.md#status)）。[范围](progress.md#scope)记录层级和验收运行所在的提交 |

[按函数查覆盖情况](coverage.md)对每个函数给出同样的四个部分。

读任何一项结论时，有三点要留意。

- 关于某一个分支的引理，或者关于抽象 API 模型的定理，并不确立一个公开函数的结论。只有类型与目标完全相同的定理才算。
- 有限次的差分测试检查的是例子，证明不了关于所有输入的命题。
- 下面的导读各章用文字描述实现。这些对 C 的解读**尚未由证明确认**：只有已登记的定理才能定论。

## 导读各章

<a id="reading-path"></a>
<a id="1-follow-a-complete-task"></a>
<a id="1-what-zlib-does"></a>
<a id="11-one-library-three-related-formats"></a>
<a id="12-repetition-becomes-a-backward-reference"></a>
<a id="13-meaning-of-compressed-bytes"></a>
<a id="13-symbols-become-bits-and-blocks"></a>
<a id="14-where-these-jobs-live-in-the-library"></a>
<a id="2-how-applications-use-the-apis"></a>
<a id="2-understand-the-encoded-bytes"></a>
<a id="21-one-decoder-two-kinds-of-lifetime"></a>
<a id="22-the-ordinary-inflate-loop"></a>
<a id="23-copies-reuse-and-borrowed-metadata"></a>
<a id="24-compression-has-its-own-completion-protocol"></a>
<a id="3-pause-and-continue-the-same-task"></a>
<a id="33-meaning-of-compressed-bytes"></a>
<a id="4-add-format-headers-and-integrity-checks"></a>
<a id="41-construct-and-interpret-decoding-tables"></a>
<a id="42-join-the-slow-and-fast-paths"></a>
<a id="43-close-the-call-and-its-history"></a>
<a id="5-reuse-branch-and-control-a-task"></a>
<a id="51-window-and-hash-chain-invariants"></a>
<a id="52-trees-symbols-and-shared-output-storage"></a>
<a id="53-publish-blocks-and-compose-calls"></a>
<a id="6-choose-an-application-interface"></a>
<a id="61-construct-and-interpret-decoding-tables"></a>
<a id="62-join-the-slow-and-fast-paths"></a>
<a id="63-close-the-call-and-its-history"></a>
<a id="71-window-and-hash-chain-invariants"></a>
<a id="72-follow-the-actual-implementation"></a>
<a id="72-trees-symbols-and-shared-output-storage"></a>
<a id="73-publish-blocks-and-compose-calls"></a>

下面六章各自沿着一个例子走过 zlib，并指出它带来的证明义务。它们解释机制；精确的契约在[规格](spec/README.md)中，按 C 组件展开的推导在[实现论证](proof/README.md)中。

| 章节 | 沿着例子理解…… |
| --- | --- |
| [1. 一次完整的任务](guide/round-trip.md) | 原始字节 → 压缩字节 → 恢复出的字节；开始、处理和释放。 |
| [2. 重复、编码与块](guide/encoding.md) | 重叠的历史复制、Huffman 编码和块的选择。 |
| [3. 流式处理](guide/streaming.md) | 缓冲区耗尽、保留的比特与历史，以及精确的续接。 |
| [4. 格式与完整性校验](guide/wrappers.md) | 共用的 DEFLATE 主体、封装条件和尾部校验。 |
| [5. 状态操作](guide/state-operations.md) | 为下一个任务重置、为检查点复制、字典与刷新。 |
| [6. 应用接口](guide/interfaces.md) | 整缓冲区、回调、gzip 文件和逻辑定位。 |

## 各条规则写在哪里

<a id="scope"></a>
<a id="project-status-and-remaining-work"></a>
<a id="11-the-implementation-and-configurations"></a>
<a id="12-safety-of-calls-and-lifetimes"></a>
<a id="2-assumptions-and-model-boundaries"></a>
<a id="21-platform-assumptions"></a>
<a id="22-caller-and-external-world-obligations"></a>
<a id="23-what-the-kernel-trusts"></a>
<a id="25-configuration-and-calling-protocol-are-separate"></a>
<a id="31-the-implementation-and-configurations"></a>
<a id="32-safety-of-calls-and-lifetimes"></a>
<a id="4-assumptions-and-model-boundaries"></a>
<a id="41-platform-assumptions"></a>
<a id="42-caller-and-external-world-obligations"></a>
<a id="43-what-the-kernel-trusts"></a>
<a id="71-scope-and-assumptions"></a>

| 问题 | 页面 |
| --- | --- |
| “安全”到底指什么：未定义行为、帧、终止、泄漏？ | [安全性](spec/safety.md) |
| 假设的是哪个平台？ | [平台](spec/platform.md)：默认 x86_64 Linux 构建；每个字节对象小于 `2^63` 字节，这并不限制流的长度 |
| 调用者的调用要满足什么？ | [偏离记录](deviations.md) |
| 模型有哪些调用者无能为力的限制？ | [模型的限制](model-limits.md) |
| 什么是被信任而没有被证明的？ | [可信基础](trusted-base.md) |
| 哪条定理覆盖某个函数？ | [按函数查覆盖情况](coverage.md) |
| 每项结论处于哪个层级，还剩什么工作？ | [进度](progress.md#scope) |
| 定理怎样成为已验收？ | [检查指南](checking/README.md) |

安全目标的全称量词覆盖其前提所容许的每个输入、参数、分配结果和历史。[输入配置](spec/input-configurations.md)中那些较窄的范围描述的是内部引理和目标图的颜色，并不限制安全目标。本页早先的叙述性记录原样保存在[总览变更记录](history/overview-changelog.md)中，属于历史资料。

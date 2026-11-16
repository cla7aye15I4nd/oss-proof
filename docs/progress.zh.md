<!-- source-sha256: 336ec5f5d3b7364a53039767cf3e31afc53c66faf2f0511711c27e8bcc9eb053 -->
# 证明进度与剩余工作

本页记录每项结论的层级和剩余的工作。只有本页记录这些：其他页面只说一条定理陈述了什么，层级则链接到这里。第一节“范围”说明什么在计划内、什么已验收以及在哪个提交上验收、什么不在计划内。中间很长的部分由证明记录生成：每个目标各有一个条目，给出它的命题、证明和依赖。这些结论是什么意思，请读[总览](overview.md)。某个函数由哪条定理覆盖，请读[按函数查覆盖情况](coverage.md)：那一页把每个函数对应到它的定理，不写层级。

## 范围

下面三项安全结论按顺序全部验收之后，项目即告完成。列在“不在计划内”之下的一切都不投入工作。

**计划内：三项安全结论。** 安全指没有未定义行为、没有内存错误、没有泄漏，并且终止。第三项结论分成四个部分。

| # | 结论 | 必需目标 |
| ---: | --- | --- |
| 1 | `inflate` 对每个输入、缓冲区的每种切分都安全，对它的调用序列也是如此。 | `Goal.inflate_safety`、`Goal.inflate_sequence_safety` |
| 2 | `deflate` 对每个输入、缓冲区的每种切分都安全，对它的调用序列也是如此。 | `Goal.deflate_safety`、`Goal.deflate_sequence_safety` |
| 3a | 整缓冲区函数是安全的：它们是第 1、2 项的组合。 | `Goal.compress_safety`、`Goal.compress2_safety`、`Goal.uncompress_safe`、`Goal.uncompress2_safe` 及其 `_z` 形式 |
| 3b | 回调解码器对每个输入、每种调用者协议都安全，对它的调用序列也是如此。 | `Goal.inflateBackInit__safety`、`Goal.inflateBack_safety`、`Goal.inflateBackEnd_safety`、`Goal.inflate_back_sequence_safety`、`Goal.inflate_back_initialisation_domain` |
| 3c | gzip 文件接口在一个句柄的每段历史上、对每个文件系统世界都安全。 | 31 个有文档的 gz 函数和 `gzvprintf` 的 32 个单函数安全目标；`Goal.gz_sequence_safety`；`Goal.gz_refusal`（`NULL` 句柄）；`Goal.gz_sequence_nonvacuity` |
| 3d | 其余每个有文档的函数都安全：其他流调用（连同初始化、End 和 Copy）、校验和、`compressBound*`、`zlibVersion` 和 `zlibCompileFlags`。 | 它们的 42 个单函数安全目标、`Goal.inflate_refusal`、`Goal.deflate_refusal`、`Goal.inflate_initialisation_domain`、`Goal.deflate_initialisation_domain` |

这六行包含了全部 98 个必需目标：2 + 2 + 8 + 5 + 35 + 46。这 98 个目标由 `scripts/verification.py` 根据 `tests/audit/public-api.json` 算出；每个目标的定理见[按函数查覆盖情况](coverage.md)。

按种类分，它们是 87 个单函数安全目标、4 个序列安全目标、3 个拒绝目标和 4 个非空性目标。在清单文件中，92 个在分组 `safety_goals` 里，4 个在 `nonvacuity_goals` 里，另外 2 个是 `compressBound` 和 `compressBound_z` 的完整契约，它们代替这两个纯函数的安全目标。

关于这张表有三点说明：

- 在 3c 中，每个调用在每个世界里的终止都已证明，只有 `gzread`、`gzfread`、`gzgetc`、`gzgetc_`、`gzgets` 和 `gzungetc` 例外。这六个调用需要小于 `2^61` 的读取预算（`ReadsFinite`），即使在 C 立即返回的情形下也是如此。
- `gzvprintf` 在 `zlib.h` 中是未文档化函数，但 `gzprintf` 要经过它，所以它随 3c 一起在计划内，它的目标 `Goal.gzvprintf_safety` 是必需的。
- 一个功能性事实在范围内，当且仅当有计划内的证明依赖它。

**每项结论的层级。** 已检查、已登记、已验收这三个层级的定义见[术语表](glossary.md#status)。定理已登记，并且验收套件在某个具名提交上全部通过，结论就是已验收的。验收套件包括公理关卡、精确目标匹配、自测和差分测试。证明变异体不属于它；它们的运行在下文单独记录。

| # | 是否已登记 | 在哪个提交上已验收 |
| ---: | --- | --- |
| 1 | 是，两个目标都已登记 | 序列目标以及 `Goal.inflate_safety` 的早先形式：`bde170e9`。已登记、未验收：`Goal.inflate_safety` 的现行形式 |
| 2 | 是，两个目标都已登记 | 序列目标以及 `Goal.deflate_safety` 的早先形式：`bde170e9`。已登记、未验收：`Goal.deflate_safety` 的现行形式 |
| 3a | 是，八个都已登记 | `bde170e9` |
| 3b | 是，五个都已登记 | 非空性目标以及序列目标的早先形式：`bde170e9`。已登记、未验收：三个单函数目标，以及序列目标的现行形式 |
| 3c | 是，35 个都已登记 | 序列目标、拒绝目标和非空性目标：`bde170e9`。已登记、未验收：32 个单函数目标 |
| 3d | 是，46 个都已登记 | `bde170e9`；下列目标的现行形式除外，它们已登记、未验收：四个 init 安全目标；`ZlibF/Spec/Safety/Streams.lean` 中其余 21 个单函数流安全目标；`Goal.inflateCopy_safety` 和 `Goal.deflateCopy_safety` |

“已登记、未验收”指：还没有哪次覆盖该目标现行形式的验收运行以全部通过结束。

**验收运行。** 每一条是工作流 `lean` 的一次运行，内容读自该次运行的记录。

- **`bde170e9`，全部通过。** 2026-11-15 的手动运行 43671067586。每个作业都通过：`build`、`no-sorry`、`audit_core`、`audit_selftest` 的两个分片、`diff_core`、`diff_harness` 的全部八个分片，以及 `audit` 和 `difftest` 两项结果。当时必需的 63 个目标都已登记。`main` 上文件树与它相同的提交 `74a2097c`，在同一天的夜间运行 43735018381 中全部通过。
- **`3fdbbc38`，已取消：不是已验收的提交。** 2026-11-15 的手动运行 43763696005，所在提交包含全部 98 个必需目标在该提交时的形式；其中 25 个此后有改动（见下文的拒绝子句）。这次运行启动时，变异体分片还是 `audit` 的一部分；它在只剩这些分片还在运行时被取消。取消之前已经通过的有：`build`、`no-sorry`、`audit_core`、`audit_selftest` 的两个分片、`diff_core`、`diff_harness` 的全部八个分片，以及 `difftest` 这项结果。二十个变异体分片被取消，所以 `audit` 这项结果失败，整次运行记为已取消。现在组成验收套件的各部分，在这次运行中都通过了。它之所以不算数，是因为这次运行的 `audit` 结果是失败，而验收是按这项结果来读的。没有任何结论凭这次运行算作已验收。
- **下一次运行：提交尚未指定。** <a id="next-acceptance-run"></a>在之后的某个提交上干净地运行一次验收套件，就会验收表中标为“已登记、未验收”的目标。这一行是记录它的唯一位置：提交、运行和日期。在填写之前，这些目标保持已登记。

差分测试是忠实度的证据，不是证明。

**证明变异体的运行。** 证明变异体是额外的证据。它们只按需运行，不构成任何关卡，连同提交在这里报告，与验收分开。

- **`bde170e9`，全部通过。** 运行 43671067586 的全部二十个变异体分片都通过。夜间运行 43735018381 的二十个分片也都通过，它所在的 `74a2097c` 是 `main` 上文件树相同的提交。
- **在更晚的提交上，还没有结束的变异体运行。** `3fdbbc38` 上那次运行的分片被取消了。`bde170e9` 之后登记的 35 个目标的变异体行是存在的（`tests/audit/public-mutants.json`），审计在 `3fdbbc38` 上检查过这一点；还没有哪次结束的运行执行过它们。

从 `bde170e9` 到本页之间，有以下改动：

- **每个 gz 函数和每个回调解码器函数都有了自己的安全目标。** 新增 35 个目标：31 个有文档的 gz 函数各一个，`gzvprintf` 一个，`inflateBackInit_`、`inflateBack` 和 `inflateBackEnd` 各一个（`ZlibF/Spec/Safety/GzCalls.lean`、`ZlibF/Spec/Safety/Back.lean`；证明在 `ZlibF/Proof/public-gz-call-safety.lean` 和 `ZlibF/Proof/public-back-safety.lean`）。它们在提交 `0cdd7bdd` 中登记：`tests/audit/` 下的登记表增加了这 35 个目标和它们的 35 条定理，清单文件为每个函数写明它自己的目标，`scripts/verification.py` 不再允许几个函数共用一个安全目标。必需目标从 63 个增加到 98 个。此前，gz 函数写的是 `Goal.gz_sequence_safety`，三个回调函数写的是 `Goal.inflate_back_sequence_safety`。这 35 个目标已登记、未验收：快速关卡在 `3fdbbc38` 上全部通过。
- **回调解码器的历史扩大了范围。** 历史的第一步（`BackSafeReachable.init`）不再要求 `inflateBackInit_` 之前 `state` 字段为 `NULL`（提交 `874a9398`，`ZlibF/Spec/Public/Sequences.lean` 中的 `BackInitArguments`）。因此 `Goal.inflate_back_sequence_safety` 覆盖的历史比它在 `bde170e9` 上覆盖的多。这一形式已登记、未验收。

- **四个初始化安全目标扩大了范围。** `Goal.inflateInit__safety`、`Goal.inflateInit2__safety`、`Goal.deflateInit__safety` 和 `Goal.deflateInit2__safety` 对 `zlib.h` 允许的每次调用都成立（提交 `101c6ab3`，`ZlibF/Spec/Safety/Initialisation.lean`；证明在 `8642e435`，`ZlibF/Proof/public-init-safety.lean`）。此前它们要求记录的 `state` 为 `NULL`、版本相符、`stream_size` 相符。范围扩大之后的四个目标已检查、已登记，尚未验收：快速关卡在 `8642e435` 上全部通过，但还没有哪次验收运行覆盖了包含它们的提交。它们在 `bde170e9` 上已验收的只是较窄的形式。
- **流安全目标陈述了对 `NULL` 流或不一致的流的拒绝。** `ZlibF/Spec/Safety/Streams.lean` 中的 23 个单函数流安全目标各增加了一个拒绝子句：十个 inflate 目标和十三个 deflate 目标，其中包括 `Goal.inflate_safety`、`Goal.deflate_safety`、`Goal.inflateEnd_safety` 和 `Goal.deflateEnd_safety`。两个复制目标 `Goal.inflateCopy_safety` 和 `Goal.deflateCopy_safety`（`ZlibF/Spec/Safety/Copy.lean`）陈述了对每一个被拒绝的源的拒绝（提交 `71188823`；证明在 `0c45d863`，`ZlibF/Proof/public-stream-call-safety.lean`、`ZlibF/Proof/public-inflate-copy-safety.lean` 和 `ZlibF/Proof/public-deflate-copy.lean`）。此前，流目标只覆盖对可达流的调用；`Goal.inflateCopy_safety` 没有针对不一致的源的子句，`Goal.deflateCopy_safety` 的那个子句只覆盖 `zalloc`、`zfree` 或 `state` 为 `NULL` 的源。每个目标的现行形式都蕴含它的早先形式（`ZlibF/Proof/public-stream-refusal-strengthening.lean`）。目标及其定理的名字没有变，所以登记表没有变。现行形式的这 25 个目标已检查、已登记，尚未验收：快速关卡在 `2ef5694c` 上全部通过，但还没有哪次验收运行覆盖了包含它们的提交。它们在 `bde170e9` 上已验收的只是早先的形式。
- **不是必需目标的命题有改动。** 快速解码器的规格允许输入和输出位于任意字节视图中，而不只是堆块中（提交 `4ed7315e`，`ZlibF/Spec/InflateFast*.lean`）；有一个回归文件从现行命题推出每个早先的命题（`tests/verification/regressions/inffast-byte-views-old-from-new.lean`）。两个功能定义有改动：`WrapperLength`（提交 `ac0fccc5`）和 `DeflateCompletes`（提交 `a2cf8723`）。这些命题中已登记的目标，其现行形式同样还没有结束的验收运行。
- **功能方面工作的证明模块有改动。** 关于 `inflate` 输出含义的模块（`ZlibF/Proof/inflate.c.meaning*.lean`）有新增和修改。其中没有任何定理被登记。

`goals.txt`、`proved-goals.txt` 和 `theorems.txt` 这三份列表的改动只有第一条所说的 35 个目标和 35 条定理；`public-mutants.json` 增加了这 35 个目标的键。全部改动就是 `bde170e9` 与本提交之间在 `ZlibF/Spec/`、`tests/audit/` 和 `scripts/` 下的差异。

**未完成。** 安全结论所需要的东西没有缺口。每个必需目标都已登记。剩下的是表中标为“已登记、未验收”的目标的验收（[按顺序的下一步工作](#ordered-next-work)）。

**安全结论之后的计划：默认 zlib 流的往返。** 默认流指默认压缩级别的 `deflateInit` 配上 `inflateInit`。顺序是：先证条件形式（当一个 `deflate` 调用序列和一个 `inflate` 调用序列都到达 `Z_STREAM_END` 时，`inflate` 写出的字节就是 `deflate` 读入的字节）；再证完备性（输出空间足够且分配成功时，两边都到达 `Z_STREAM_END`）；最后是无条件的往返，以及 `uncompress(compress(x)) = x`。条件形式已在 `dev` 上对翻译后的 C 检查：定理 `deflate_inflate_roundtrip`（`ZlibF/Proof/public-deflate-inflate-roundtrip.lean`），它没有登记。完备性和无条件形式未证明。已登记的目标 `Api.Goal.roundtrip` 是仅关于模型的命题：它说的是抽象 API 模型。先前在往返的 deflate 一侧所做的工作（`Ledger`、`ledger_*`、`completes`、`bound_before_output`、`deflate_sequence` 的解码部分）保留着；默认流的往返需要其中哪些，本页不作定论。

**不在计划内。** 这些不投入任何工作。已经为它们登记的结果保留。

| 分组 | 目标 | 原因 |
| --- | --- | --- |
| gzip 文件接口的功能部分 | `gz_sequence`、`gz_initialisation_domain`，以及各 gz 调用的功能子句（读出或写入的字节、安全之外的返回值） | 功能性。这些定理依赖一个人工建立的文件系统、描述符和 `printf` 格式化模型。gz 调用的安全性在计划内（3c）。 |
| 未文档化函数 | `zError`、`inflateSyncPoint`、`get_crc_table`、`inflateUndermine`、`inflateValidate`、`inflateCodesUsed`、`inflateResetKeep`、`deflateResetKeep`、`gzopen_w` | `zlib.h` 在 `undocumented functions (not part of the zlib API)` 之下声明了十个函数（`tests/audit/public-api.json` 的 `undocumented`），这是其中九个；第十个 `gzvprintf` 随 3c 在计划内。它们不是必需的公开目标，直接调用其中某一个也不是序列目标必需的操作；deflate 流的定义域排除了对 `deflateResetKeep` 的直接调用（[偏离记录](deviations.md#stream-calls-inflate-and-deflate)）。它们已登记的证明保持登记并接受审计。内部用法不变：`deflateReset` 和 `inflateReset` 要经过 `ResetKeep` 的引理。 |
| 回调解码器的解码部分 | `inflateBack` 与 `inflate_back_sequence` 的解码子句（交给 `out` 的内容、`Decodes`） | 功能性。回调解码器的安全性在计划内（3b）。 |
| 仅关于模型的命题 | `Api.Goal.inflate_rejects_invalid`，以及未登记的 `*_refines` 目标 | 它们说的是抽象模型，不是 C。前者还依赖八字节的检测延迟，而这个延迟已被反例否定。对非法输入的拒绝，是在 `inflate_sequence` 的格式部分中针对 C 陈述的（见下面“功能正确性”一行）。 |
| 其他构建配置 | 默认 x86_64 Linux 构建之外的每一种配置 | 每一种配置都要针对不同的平台模型把整个证明重做一遍。结论由默认构建承载。 |
| 为查询函数增加证明变异体 | 取值函数和常量查询 | 变异体用来防备证明的设置有误。对只有一行的查询函数，它们不会给计划内的结论增加任何东西。 |
| 功能正确性（上面的往返除外） | `inflate_sequence` 的格式部分（`inflate` 的输出等于格式：`ParseMeaning` 及其流侧与解码侧）、`InflateCompletes` 背后的 `DecoderFacts` 格式事实，以及 `uncompress*` 的格式子句；其他压缩级别、策略、窗口大小和封装的往返，带预设字典的往返，经由 gzip 文件接口或 `inflateBack` 的往返 | 安全结论不需要它们。计划内的证明所依赖的功能性事实仍在范围内。已经证明的部分保留，并列为已检查；归档的骨架表把未完成的行标为不在计划内（[inflate](history/skeleton-inflate.md)、[deflate](history/skeleton-deflate.md)）。 |

`Goal.gz_initialisation_domain` 不是必需的非空性目标。它陈述的是 `gzopen` 的功能契约（`OpenState`、`GzReachable`），上表第一行已把它列为不在计划内。没有计划内的安全证明依赖它：`Goal.gz_sequence_safety` 让每段历史从打开调用开始，并沿着历史证明 `GzInv`。在已登记的 gz 安全定理（`gz_sequence_safety_public`、`gz_sequence_nonvacuity_public`、`gz_refusal`）的导入闭包中，这个目标只出现在它自己的定义里，`GzReachable` 从不充当前提。gz 安全目标的前提可以被满足，这一点由已登记的 `Goal.gz_sequence_nonvacuity` 给出。这个命题仍留在 `tests/audit/goals.txt` 中，是一个未证明、不在计划内的目标。

对不在计划内的目标不作任何断言。报告里写“不在计划内”，决不写“已证明”。

**所有者的决定。** 这张表是带日期的记录；其他页面只陈述结果，不写日期。

| 日期 | 决定 |
| --- | --- |
| 2026-11-11 | 范围只限安全，以便更快完成。在此之前，`inflate` 的功能正确性是第 2 项结论。 |
| 2026-11-12 | 回调解码器（3b）和 gzip 文件接口（3c）在计划内，只证安全。`gzvprintf` 从未文档化函数一组移到 3c。补丁 0004 和 0005 可以先于上游提交落地。 |
| 2026-11-14 | `Goal.gz_initialisation_domain` 不是必需目标。 |
| 2026-11-15 | 默认 zlib 流的往返（含完备性）排在安全结论之后，在计划内。翻译的四种规范化写法被采纳（`AGENTS.md` 的“翻译”一节，原文标题为 Translation）。证明变异体是额外的证据，不再属于验收：完整运行一次需要几个小时。它们按需运行，不构成合并、验收或里程碑的关卡。状态只保存在本页：其他页面不写层级、验收所在的提交或目标的个数。 |

## 目录

- [范围：计划内与不在计划内](#scope)
- [全部目标及其依赖](#proof-progress-graph)
- [确切目标的证据](#target-evidence)
- [剩余工作](#remaining-work)
  - [核心证明骨架](#core-proof-skeletons)
  - [按顺序的下一步工作](#ordered-next-work)
  - [公开 API 的前置证明义务](#public-api-proof-readiness)
  - [规格审查](#specification-review)
  - [翻译审查](#translation-review)
  - [待复核的报告](#historical-reports-to-recheck)
- [早先的检查点（历史）](history/progress-checkpoints.zh.md)

下方生成区块中的数字是唯一的当前数字。审查记录和 `docs/history/` 中的数字反映写作时的状态。

<!-- proof-progress:start -->
## 证明进度图

**共有 274 个固定目标：196 个公开目标，78 个支撑目标。**
精确覆盖相应目标的证明中，228 个已登记，1 个仅在本地检查。
这些数字按目标计数，不表示验证工作量的完成百分比，也不代表最终 CI 结果。

**输入覆盖范围的颜色：** ⬜ 未证明 · 🟦 默认输入 · 🟨 常见输入 · 🟩 目标陈述所允许的全部输入。
各档范围统一定义在[输入配置](spec/input-configurations.md)中。
完整的固定目标证明，必须覆盖该目标的确切陈述所允许的全部输入。
若只证明默认输入或常见输入，也必须有经过检查、明确限定范围的契约；局部分支引理和手工填写的标签不能代替这种证明。
输入覆盖范围、证明是否登记、CI 是否通过，是三件不同的事。
红色边框表示已记录的阻碍，不会抹去该目标已经建立的其他覆盖结果。

每个当前固定目标只出现一次。公开 API、内部证明义务和抽象模型分组呈现。
实线表示固定目标之间实际存在的证明复用关系，追踪范围包含经辅助引理间接发生的引用。
虚线表示 C 函数调用，方向由被调用者指向调用者。它并不表示可以把被调用者的完整 API 契约当作证明前提：例如，默认初始化 `Init` 可以独立于通用初始化 `Init2` 完成证明。
只有在同类路径仍然存在时，图中才会省略冗余箭头。[证据索引](progress.md)保留了每条观察到的连接、规格引用和支撑证明族。
这些辅助证明不是额外的最终目标。缺少箭头既不能说明两个目标彼此独立，也不能列全今后需要完成的证明义务。

```mermaid
flowchart LR
  subgraph queries["Library queries"]
    n19["compressBound"]:::all
    n20["compressBound_z"]:::all
    n21["zlibVersion"]:::all
    n22["zlibCompileFlags"]:::all
    n23["zError"]:::all
    n30["get_crc_table"]:::all
  end
  style queries fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph checksums["Checksums"]
    n24["adler32"]:::all
    n25["adler32_z"]:::all
    n26["adler32_combine"]:::all
    n27["adler32_combine64"]:::all
    n28["crc32"]:::all
    n29["crc32_z"]:::all
    n31["crc32_combine_gen"]:::all
    n32["crc32_combine_gen64"]:::all
    n33["crc32_combine_op"]:::all
    n34["crc32_combine"]:::all
    n35["crc32_combine64"]:::all
    n161["adler32_safety"]:::all
    n162["adler32_z_safety"]:::all
    n163["adler32_combine_safety"]:::all
    n164["adler32_combine64_safety"]:::all
    n165["crc32_safety"]:::all
    n166["crc32_z_safety"]:::all
    n167["crc32_combine_gen_safety"]:::all
    n168["crc32_combine_gen64_<br/>safety"]:::all
    n169["crc32_combine_op_safety"]:::all
    n170["crc32_combine_safety"]:::all
    n171["crc32_combine64_safety"]:::all
  end
  style checksums fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph addresses["Byte-address model"]
    n181["ByteAddress<br/>address_read_is_pure"]:::all
    n182["ByteAddress<br/>raw_block_unchanged"]:::all
    n183["ByteAddress<br/>every_layout_is_<br/>representable"]:::all
    n184["ByteAddress<br/>every_existing_heap_<br/>accepts_layout"]:::all
    n185["ByteAddress<br/>mask_refines_base_plus_<br/>offset"]:::all
    n186["ByteAddress<br/>pointer_advance_<br/>preserves_low_bits"]:::all
    n187["ByteAddress<br/>first_aligned_offset"]:::all
    n188["ByteAddress<br/>byte_stores_preserve_<br/>bases"]:::all
    n189["ByteAddress<br/>byte_modifies_preserve_<br/>bases"]:::all
  end
  style addresses fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph inflate["Inflate streams"]
    n39["inflateCopy"]:::all
    n73["inflateInit2_"]:::all
    n74["inflateInit_"]:::all
    n77["inflateResetKeep"]:::all
    n78["inflateReset"]:::all
    n79["inflateReset2"]:::all
    n80["inflateEnd"]:::all
    n81["inflateGetDictionary"]:::all
    n82["inflateGetHeader"]:::all
    n87["inflateSetDictionary"]:::all
    n89["inflateSyncPoint"]:::all
    n90["inflateMark"]:::all
    n91["inflateCodesUsed"]:::all
    n92["inflateUndermine"]:::all
    n93["inflateValidate"]:::all
    n94["inflatePrime"]:::all
    n99["inflate"]:::all
    n105["inflateSync"]:::unproved
    n123["inflate_sequence_safety"]:::all
    n127["inflate_back_sequence_<br/>safety"]:::all
    n129["inflate_refusal"]:::all
    n133["inflate_safety"]:::all
    n134["inflateSetDictionary_<br/>safety"]:::all
    n135["inflateGetDictionary_<br/>safety"]:::all
    n136["inflateSync_safety"]:::all
    n137["inflateReset_safety"]:::all
    n138["inflateReset2_safety"]:::all
    n139["inflatePrime_safety"]:::all
    n140["inflateMark_safety"]:::all
    n141["inflateGetHeader_safety"]:::all
    n154["inflateEnd_safety"]:::all
    n156["inflateInit2__safety"]:::all
    n157["inflateInit__safety"]:::all
    n160["inflateCopy_safety"]:::all
  end
  style inflate fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph fast["Fast decoder obligations"]
    n192["InflateFastBodyOrigin<br/>actual_body_preserves_<br/>origin"]:::all
    n193["InflateFastBodyToken<br/>actual_body_refines_token"]:::all
    n194["InflateFastCallOrigin<br/>actual_fast_preserves_<br/>origin"]:::all
    n195["InflateFastDistanceOrigin<br/>actual_distance_block_<br/>preserves_origin"]:::all
    n196["InflateFastDistanceResult<br/>actual_distance_refines_<br/>lz77"]:::all
    n197["InflateFastDistance<br/>Semantics<br/>distance_lookup_matches_<br/>format"]:::all
    n198["InflateFast<br/>fast_safe"]:::all
    n199["InflateFast<br/>step_safe"]:::all
    n200["InflateFastLength<br/>Semantics<br/>length_lookup_matches_<br/>format"]:::all
    n201["InflateFastLengthTrace<br/>actual_body_retains_<br/>selected_length"]:::all
    n202["InflateFastMatchHistory<br/>actual_copy_match_<br/>refines_lz77"]:::all
    n203["InflateFastMatchHistory<br/>match_array_refines_lz77"]:::all
    n204["InflateFastOrigin<br/>actual_drop_preserves_<br/>origin"]:::all
    n205["InflateFastOrigin<br/>actual_pull_preserves_<br/>origin"]:::all
    n206["InflateFastOrigin<br/>actual_rollback_<br/>preserves_origin"]:::all
    n207["InflateFastOrigin<br/>drop_preserves_origin"]:::all
    n208["InflateFastOrigin<br/>initial_origin"]:::all
    n209["InflateFastOrigin<br/>pull_preserves_origin"]:::all
    n210["InflateFastOrigin<br/>rollback_preserves_origin"]:::all
  end
  style fast fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph tables["Decode-table obligations"]
    n211["InflateDecodeTable<br/>Rejection<br/>decode_table_classifies_<br/>input"]:::all
    n212["InflateDecodeTable<br/>Semantics<br/>decode_table_matches_<br/>format"]:::all
    n213["InflateDecodeTableShort<br/>short_decode_table_leaf_<br/>sound"]:::all
    n214["InflateDecodeTable<br/>Soundness<br/>decode_table_leaf_sound"]:::all
    n215["InflateDecodeTableFrame<br/>decode_table_read_<br/>preserved"]:::all
    n216["InflateDecodeTable<br/>Invariant<br/>constructor_establishes_<br/>decode_table_invariant"]:::all
    n217["InflateDecodeTable<br/>Invariant<br/>decode_table_invariant_<br/>of_prefix"]:::all
    n218["InflateDecodeTable<br/>Stability<br/>constructor_establishes_<br/>query_stability"]:::all
    n219["InflateDecodeTable<br/>Stability<br/>query_stability_of_prefix"]:::all
    n220["InflateDecodeTable<br/>Stability<br/>short_rejected_leaf_<br/>stays_invalid"]:::all
    n221["InflateFastTableFlags<br/>constructor_establishes_<br/>fast_leaf_flags"]:::all
    n222["InflateFastTableFlags<br/>fast_leaf_flags_of_prefix"]:::all
    n223["InflateFastTableFlags<br/>fixed_tables_have_fast_<br/>leaf_flags"]:::all
    n224["InflateFastTableFlags<br/>leaf_classification_<br/>agrees"]:::all
    n225["InflateTableContent<br/>inflate_table_content"]:::all
    n226["InflateTableSafety<br/>inflate_table_decoder_<br/>safe"]:::all
    n227["InflateTableExtent<br/>inflate_table_read_extent"]:::all
    n228["InflateRootTable<br/>constructor_root_bits"]:::all
    n229["InflateSubtable<br/>constructor_subtable_bits"]:::all
  end
  style tables fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph copy["Match-copy mathematics"]
    n230["LZ77CopySpec<br/>output_copy_refines_lz77"]:::all
    n231["LZ77CopySpec<br/>window_copy_refines_lz77"]:::all
    n232["LZ77HistorySpec<br/>copy_back_compose"]:::all
    n233["LZ77HistorySpec<br/>copy_back_extends_history"]:::all
    n234["LZ77HistorySpec<br/>retained_history_agrees"]:::all
    n235["LZ77HistorySpec<br/>window_distance_check_<br/>agrees"]:::all
  end
  style copy fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph deflate["Deflate streams"]
    n40["deflateCopy"]:::all
    n75["deflateInit2_"]:::all
    n76["deflateInit_"]:::all
    n83["deflateGetDictionary"]:::all
    n84["deflateEnd"]:::all
    n85["deflateResetKeep"]:::all
    n86["deflateReset"]:::all
    n88["deflateSetDictionary"]:::unproved
    n95["deflatePending"]:::all
    n96["deflateUsed"]:::all
    n97["deflateTune"]:::all
    n98["deflateSetHeader"]:::all
    n100["deflate"]:::all
    n101["deflateBound_z"]:::unproved
    n102["deflateBound"]:::unproved
    n103["deflatePrime"]:::unproved
    n104["deflateParams"]:::unproved
    n125["deflate_sequence_safety"]:::all
    n128["deflateCopy_safety"]:::all
    n130["deflate_refusal"]:::all
    n142["deflate_safety"]:::all
    n143["deflateSetDictionary_<br/>safety"]:::all
    n144["deflateGetDictionary_<br/>safety"]:::all
    n145["deflateReset_safety"]:::all
    n146["deflateParams_safety"]:::all
    n147["deflateTune_safety"]:::all
    n148["deflateBound_safety"]:::all
    n149["deflateBound_z_safety"]:::all
    n150["deflatePending_safety"]:::all
    n151["deflateUsed_safety"]:::all
    n152["deflatePrime_safety"]:::all
    n153["deflateSetHeader_safety"]:::all
    n155["deflateEnd_safety"]:::all
    n158["deflateInit2__safety"]:::all
    n159["deflateInit__safety"]:::all
  end
  style deflate fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph back["Callback decoding"]
    n36["inflateBackInit_"]:::all
    n37["inflateBack"]:::unproved
    n38["inflateBackEnd"]:::all
    n271["inflateBack_safety"]:::all
    n272["inflateBackEnd_safety"]:::all
    n273["inflateBackInit__safety"]:::all
  end
  style back fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph gzip["Gzip files"]
    n41["gzclose_r"]:::unproved
    n42["gzclose_w"]:::unproved
    n43["gzclose"]:::unproved
    n44["gzbuffer"]:::all
    n45["gzeof"]:::all
    n46["gztell64"]:::unproved
    n47["gztell"]:::unproved
    n48["gzoffset64"]:::all
    n49["gzoffset"]:::all
    n50["gzerror"]:::all
    n51["gzclearerr"]:::all
    n52["gzrewind"]:::all
    n53["gzseek64"]:::unproved
    n54["gzseek"]:::unproved
    n55["gzopen"]:::unproved
    n56["gzopen64"]:::unproved
    n57["gzdopen"]:::all
    n58["gzread"]:::unproved
    n59["gzfread"]:::unproved
    n60["gzgetc"]:::unproved
    n61["gzgetc_"]:::unproved
    n62["gzungetc"]:::unproved
    n63["gzgets"]:::unproved
    n64["gzdirect"]:::unproved
    n65["gzwrite"]:::unproved
    n66["gzfwrite"]:::unproved
    n67["gzputc"]:::unproved
    n68["gzputs"]:::unproved
    n69["gzvprintf"]:::unproved
    n70["gzprintf"]:::unproved
    n71["gzflush"]:::unproved
    n72["gzsetparams"]:::unproved
    n131["gz_sequence_safety"]:::all
    n132["gz_refusal"]:::all
    n179["gz_sequence_nonvacuity"]:::all
    n239["gzbuffer_safety"]:::all
    n240["gzclearerr_safety"]:::all
    n241["gzclose_safety"]:::all
    n242["gzclose_r_safety"]:::all
    n243["gzclose_w_safety"]:::all
    n244["gzdirect_safety"]:::all
    n245["gzdopen_safety"]:::all
    n246["gzeof_safety"]:::all
    n247["gzerror_safety"]:::all
    n248["gzflush_safety"]:::all
    n249["gzfread_safety"]:::all
    n250["gzfwrite_safety"]:::all
    n251["gzgetc_safety"]:::all
    n252["gzgetc__safety"]:::all
    n253["gzgets_safety"]:::all
    n254["gzoffset_safety"]:::all
    n255["gzoffset64_safety"]:::all
    n256["gzopen_safety"]:::all
    n257["gzopen64_safety"]:::all
    n258["gzprintf_safety"]:::all
    n259["gzvprintf_safety"]:::all
    n260["gzputc_safety"]:::all
    n261["gzputs_safety"]:::all
    n262["gzread_safety"]:::all
    n263["gzrewind_safety"]:::all
    n264["gzseek_safety"]:::all
    n265["gzseek64_safety"]:::all
    n266["gzsetparams_safety"]:::all
    n267["gztell_safety"]:::all
    n268["gztell64_safety"]:::all
    n269["gzungetc_safety"]:::all
    n270["gzwrite_safety"]:::all
  end
  style gzip fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph buffers["Whole-buffer operations"]
    n106["compress2_z"]:::unproved
    n107["compress2"]:::unproved
    n108["compress_z"]:::unproved
    n109["compress"]:::unproved
    n110["uncompress2_z"]:::unproved
    n111["uncompress2"]:::unproved
    n112["uncompress_z"]:::unproved
    n113["uncompress"]:::unproved
    n114["uncompress2_z_safe"]:::all
    n115["uncompress2_safe"]:::all
    n116["uncompress_z_safe"]:::all
    n117["uncompress_safe"]:::all
    n118["compress2_z_safety"]:::all
    n119["compress2_safety"]:::all
    n120["compress_z_safety"]:::all
    n121["compress_safety"]:::all
    n172["zlibVersion_safety"]:::all
    n173["zlibCompileFlags_safety"]:::all
  end
  style buffers fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph models["Format and API models"]
    n0["Goals<br/>format_deterministic"]:::all
    n1["Goals<br/>format_prefix_free"]:::all
    n2["Goals<br/>inflate_decodes"]:::all
    n3["Goals<br/>inflate_completes"]:::all
    n4["Goals<br/>inflate_rejects_invalid"]:::unproved
    n5["Goals<br/>deflate_valid"]:::all
    n6["Goals<br/>deflate_completes"]:::all
    n7["Goals<br/>deflate_full_flush_resync"]:::all
    n8["Goals<br/>roundtrip"]:::all
    n9["Goals<br/>roundtrip_completes"]:::all
    n10["Goals<br/>dict_roundtrip"]:::all
    n11["Goals<br/>header_roundtrip"]:::all
    n12["Goals<br/>deflate_bound_adequate"]:::all
    n13["Goals<br/>compress_bound_adequate"]:::all
    n14["Goals<br/>compress_roundtrip"]:::all
    n15["Goals<br/>gz_roundtrip"]:::all
    n16["Goals<br/>gz_seek_read<br/>Local exact proof"]:::all
    n17["Concrete<br/>compress_bound_value"]:::all
    n18["Concrete<br/>compress2_z_first_alloc_<br/>failure"]:::all
    n180["Inflate<br/>inflate_deferred_distance"]:::all
  end
  style models fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph lifecycle["Lifecycles and call sequences"]
    n122["inflate_sequence"]:::unproved
    n124["deflate_sequence"]:::unproved
    n126["inflate_back_sequence"]:::unproved
    n174["gz_sequence"]:::unproved
    n175["inflate_initialisation_<br/>domain"]:::all
    n176["deflate_initialisation_<br/>domain"]:::all
    n177["inflate_back_<br/>initialisation_domain"]:::all
    n178["gz_initialisation_domain"]:::unproved
  end
  style lifecycle fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph internal["Internal proof obligations"]
    n190["Crc32ByteViews<br/>crc32_z_all_byte_views"]:::all
    n191["Crc32ByteViews<br/>crc32_all_byte_views"]:::all
    n236["Token<br/>rejected_has_no_symbols"]:::all
    n237["Token<br/>step_composes_symbols"]:::all
    n238["Token<br/>symbols_exposes_step"]:::all
  end
  style internal fill:#f9fafb,stroke:#9ca3af,color:#111827
  n186 --> n187
  n191 --> n28
  n191 --> n99
  n191 --> n39
  n191 --> n123
  n190 --> n29
  n192 --> n194
  n194 --> n99
  n194 --> n39
  n194 --> n123
  n195 --> n192
  n196 --> n193
  n197 --> n196
  n198 --> n194
  n199 --> n193
  n199 --> n201
  n200 --> n193
  n202 --> n196
  n203 --> n202
  n204 --> n192
  n206 --> n194
  n207 --> n195
  n207 --> n204
  n208 --> n194
  n209 --> n195
  n209 --> n205
  n210 --> n206
  n211 --> n216
  n212 --> n211
  n213 --> n216
  n214 --> n211
  n214 --> n213
  n215 --> n217
  n215 --> n219
  n215 --> n222
  n216 --> n99
  n216 --> n39
  n216 --> n127
  n216 --> n123
  n217 --> n99
  n217 --> n39
  n217 --> n127
  n217 --> n123
  n218 --> n127
  n219 --> n127
  n220 --> n197
  n220 --> n200
  n225 --> n226
  n226 --> n227
  n226 --> n228
  n227 --> n216
  n229 --> n216
  n229 --> n228
  n230 --> n203
  n231 --> n203
  n232 --> n203
  n234 --> n8
  n234 --> n9
  n5 --> n10
  n5 --> n11
  n5 --> n8
  n5 --> n9
  n3 --> n9
  n2 --> n8
  n24 --> n161
  n26 --> n163
  n27 --> n164
  n25 --> n24
  n25 --> n162
  n28 --> n119
  n28 --> n118
  n28 --> n121
  n28 --> n120
  n28 --> n165
  n28 --> n100
  n28 --> n40
  n28 --> n125
  n28 --> n131
  n34 --> n170
  n35 --> n171
  n31 --> n167
  n31 --> n169
  n32 --> n168
  n32 --> n169
  n33 --> n169
  n29 --> n166
  n40 --> n128
  n84 --> n119
  n84 --> n118
  n84 --> n121
  n84 --> n120
  n84 --> n125
  n84 --> n131
  n75 --> n158
  n158 --> n159
  n95 --> n150
  n98 --> n153
  n97 --> n147
  n96 --> n151
  n130 --> n128
  n130 --> n144
  n130 --> n146
  n130 --> n143
  n130 --> n142
  n125 --> n148
  n125 --> n149
  n125 --> n155
  n125 --> n144
  n125 --> n146
  n125 --> n150
  n125 --> n152
  n125 --> n145
  n125 --> n143
  n125 --> n153
  n125 --> n147
  n125 --> n151
  n125 --> n142
  n131 --> n239
  n131 --> n240
  n131 --> n242
  n131 --> n241
  n131 --> n243
  n131 --> n244
  n131 --> n245
  n131 --> n246
  n131 --> n247
  n131 --> n248
  n131 --> n249
  n131 --> n250
  n131 --> n252
  n131 --> n251
  n131 --> n253
  n131 --> n255
  n131 --> n254
  n131 --> n257
  n131 --> n256
  n131 --> n258
  n131 --> n260
  n131 --> n261
  n131 --> n262
  n131 --> n263
  n131 --> n265
  n131 --> n264
  n131 --> n266
  n131 --> n268
  n131 --> n267
  n131 --> n269
  n131 --> n259
  n131 --> n270
  n45 --> n131
  n99 --> n131
  n99 --> n115
  n99 --> n114
  n99 --> n117
  n99 --> n116
  n38 --> n127
  n36 --> n273
  n36 --> n177
  n36 --> n127
  n39 --> n160
  n80 --> n123
  n73 --> n99
  n73 --> n39
  n73 --> n156
  n73 --> n123
  n156 --> n157
  n90 --> n140
  n94 --> n139
  n87 --> n123
  n127 --> n272
  n127 --> n271
  n129 --> n160
  n129 --> n154
  n129 --> n135
  n129 --> n138
  n129 --> n137
  n129 --> n134
  n129 --> n133
  n123 --> n154
  n123 --> n135
  n123 --> n141
  n123 --> n140
  n123 --> n139
  n123 --> n138
  n123 --> n137
  n123 --> n134
  n123 --> n136
  n123 --> n133
  n22 --> n173
  n21 --> n172
  n24 -.-> n100
  n24 -.-> n85
  n24 -.-> n88
  n24 -.-> n99
  n24 -.-> n87
  n25 -.-> n24
  n107 -.-> n109
  n106 -.-> n107
  n106 -.-> n108
  n20 -.-> n19
  n28 -.-> n100
  n28 -.-> n85
  n28 -.-> n88
  n28 -.-> n99
  n35 -.-> n34
  n32 -.-> n35
  n32 -.-> n31
  n33 -.-> n35
  n29 -.-> n28
  n100 -.-> n106
  n100 -.-> n104
  n100 -.-> n42
  n100 -.-> n71
  n100 -.-> n66
  n100 -.-> n67
  n100 -.-> n68
  n100 -.-> n69
  n100 -.-> n65
  n101 -.-> n102
  n84 -.-> n75
  n75 -.-> n76
  n75 -.-> n42
  n75 -.-> n71
  n75 -.-> n66
  n75 -.-> n67
  n75 -.-> n68
  n75 -.-> n72
  n75 -.-> n69
  n75 -.-> n65
  n76 -.-> n106
  n104 -.-> n72
  n86 -.-> n75
  n85 -.-> n86
  n41 -.-> n43
  n42 -.-> n43
  n60 -.-> n61
  n48 -.-> n49
  n52 -.-> n53
  n53 -.-> n54
  n46 -.-> n47
  n69 -.-> n70
  n99 -.-> n59
  n99 -.-> n60
  n99 -.-> n63
  n99 -.-> n58
  n99 -.-> n62
  n99 -.-> n110
  n80 -.-> n41
  n80 -.-> n110
  n73 -.-> n64
  n73 -.-> n59
  n73 -.-> n60
  n73 -.-> n63
  n73 -.-> n58
  n73 -.-> n62
  n73 -.-> n74
  n74 -.-> n110
  n78 -.-> n79
  n78 -.-> n105
  n79 -.-> n73
  n77 -.-> n78
  n111 -.-> n113
  n110 -.-> n111
  n110 -.-> n112
  n23 -.-> n100
  n23 -.-> n75
  n21 -.-> n106
  click n0 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Api/Goals.lean#L42" _blank
  click n1 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Api/Goals.lean#L47" _blank
  click n2 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Api/Goals.lean#L58" _blank
  click n3 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Api/Goals.lean#L69" _blank
  click n4 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Api/Goals.lean#L84" _blank
  click n5 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Api/Goals.lean#L99" _blank
  click n6 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Api/Goals.lean#L106" _blank
  click n7 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Api/Goals.lean#L116" _blank
  click n8 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Api/Goals.lean#L134" _blank
  click n9 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Api/Goals.lean#L143" _blank
  click n10 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Api/Goals.lean#L162" _blank
  click n11 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Api/Goals.lean#L180" _blank
  click n12 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Api/Goals.lean#L189" _blank
  click n13 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Api/Goals.lean#L196" _blank
  click n14 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Api/Goals.lean#L203" _blank
  click n15 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Api/Goals.lean#L214" _blank
  click n16 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Api/Goals.lean#L221" _blank
  click n17 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Api/Concrete.lean#L57" _blank
  click n18 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Api/Concrete.lean#L67" _blank
  click n19 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Queries.lean#L16" _blank
  click n20 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Queries.lean#L21" _blank
  click n21 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Queries.lean#L27" _blank
  click n22 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Queries.lean#L34" _blank
  click n23 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Queries.lean#L40" _blank
  click n24 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Checksums.lean#L41" _blank
  click n25 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Checksums.lean#L36" _blank
  click n26 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Checksums.lean#L62" _blank
  click n27 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Checksums.lean#L66" _blank
  click n28 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Checksums.lean#L93" _blank
  click n29 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Checksums.lean#L85" _blank
  click n30 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Checksums.lean#L102" _blank
  click n31 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Checksums.lean#L116" _blank
  click n32 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Checksums.lean#L119" _blank
  click n33 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Checksums.lean#L126" _blank
  click n34 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Checksums.lean#L138" _blank
  click n35 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Checksums.lean#L141" _blank
  click n36 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/Back.lean#L22" _blank
  click n37 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/Back.lean#L118" _blank
  click n38 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/Back.lean#L145" _blank
  click n39 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Copy.lean#L16" _blank
  click n40 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Copy.lean#L46" _blank
  click n41 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzClose.lean#L35" _blank
  click n42 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzClose.lean#L40" _blank
  click n43 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzClose.lean#L44" _blank
  click n44 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzControl.lean#L12" _blank
  click n45 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzControl.lean#L22" _blank
  click n46 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzControl.lean#L36" _blank
  click n47 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzControl.lean#L39" _blank
  click n48 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzControl.lean#L53" _blank
  click n49 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzControl.lean#L56" _blank
  click n50 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzControl.lean#L63" _blank
  click n51 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzControl.lean#L74" _blank
  click n52 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzControl.lean#L91" _blank
  click n53 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzControl.lean#L116" _blank
  click n54 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzControl.lean#L119" _blank
  click n55 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzOpen.lean#L65" _blank
  click n56 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzOpen.lean#L70" _blank
  click n57 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzOpen.lean#L75" _blank
  click n58 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzRead.lean#L22" _blank
  click n59 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzRead.lean#L37" _blank
  click n60 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzRead.lean#L58" _blank
  click n61 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzRead.lean#L61" _blank
  click n62 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzRead.lean#L66" _blank
  click n63 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzRead.lean#L80" _blank
  click n64 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzRead.lean#L103" _blank
  click n65 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzWrite.lean#L28" _blank
  click n66 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzWrite.lean#L43" _blank
  click n67 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzWrite.lean#L59" _blank
  click n68 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzWrite.lean#L71" _blank
  click n69 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzWrite.lean#L108" _blank
  click n70 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzWrite.lean#L112" _blank
  click n71 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzWrite.lean#L117" _blank
  click n72 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzWrite.lean#L134" _blank
  click n73 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Initialisation.lean#L15" _blank
  click n74 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Initialisation.lean#L20" _blank
  click n75 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Initialisation.lean#L25" _blank
  click n76 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Initialisation.lean#L32" _blank
  click n77 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Lifecycle.lean#L16" _blank
  click n78 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Lifecycle.lean#L23" _blank
  click n79 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Lifecycle.lean#L34" _blank
  click n80 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Lifecycle.lean#L51" _blank
  click n81 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Lifecycle.lean#L61" _blank
  click n82 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Lifecycle.lean#L71" _blank
  click n83 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Lifecycle.lean#L82" _blank
  click n84 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Lifecycle.lean#L92" _blank
  click n85 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Lifecycle.lean#L102" _blank
  click n86 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Lifecycle.lean#L105" _blank
  click n87 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Lifecycle.lean#L109" _blank
  click n88 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Lifecycle.lean#L131" _blank
  click n89 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/StreamQueries.lean#L15" _blank
  click n90 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/StreamQueries.lean#L24" _blank
  click n91 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/StreamQueries.lean#L35" _blank
  click n92 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/StreamQueries.lean#L43" _blank
  click n93 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/StreamQueries.lean#L51" _blank
  click n94 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/StreamQueries.lean#L62" _blank
  click n95 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/StreamQueries.lean#L75" _blank
  click n96 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/StreamQueries.lean#L86" _blank
  click n97 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/StreamQueries.lean#L94" _blank
  click n98 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/StreamQueries.lean#L107" _blank
  click n99 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Streams.lean#L28" _blank
  click n100 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Streams.lean#L68" _blank
  click n101 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Streams.lean#L105" _blank
  click n102 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Streams.lean#L109" _blank
  click n103 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Streams.lean#L114" _blank
  click n104 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Streams.lean#L132" _blank
  click n105 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Streams.lean#L151" _blank
  click n106 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Utilities.lean#L43" _blank
  click n107 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Utilities.lean#L48" _blank
  click n108 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Utilities.lean#L55" _blank
  click n109 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Utilities.lean#L60" _blank
  click n110 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Utilities.lean#L101" _blank
  click n111 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Utilities.lean#L105" _blank
  click n112 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Utilities.lean#L133" _blank
  click n113 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Utilities.lean#L137" _blank
  click n114 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Utilities.lean#L34" _blank
  click n115 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Utilities.lean#L37" _blank
  click n116 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Utilities.lean#L40" _blank
  click n117 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Utilities.lean#L43" _blank
  click n118 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Utilities.lean#L14" _blank
  click n119 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Utilities.lean#L18" _blank
  click n120 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Utilities.lean#L24" _blank
  click n121 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Utilities.lean#L28" _blank
  click n122 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Sequences.lean#L172" _blank
  click n123 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Sequences.lean#L28" _blank
  click n124 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Sequences.lean#L192" _blank
  click n125 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Sequences.lean#L19" _blank
  click n126 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/Sequences.lean#L175" _blank
  click n127 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/Sequences.lean#L196" _blank
  click n128 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Copy.lean#L24" _blank
  click n129 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Refusals.lean#L30" _blank
  click n130 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Refusals.lean#L50" _blank
  click n131 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzSafety.lean#L144" _blank
  click n132 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzRefusal.lean#L39" _blank
  click n133 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Streams.lean#L48" _blank
  click n134 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Streams.lean#L60" _blank
  click n135 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Streams.lean#L71" _blank
  click n136 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Streams.lean#L84" _blank
  click n137 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Streams.lean#L96" _blank
  click n138 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Streams.lean#L106" _blank
  click n139 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Streams.lean#L117" _blank
  click n140 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Streams.lean#L128" _blank
  click n141 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Streams.lean#L138" _blank
  click n142 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Streams.lean#L149" _blank
  click n143 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Streams.lean#L160" _blank
  click n144 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Streams.lean#L171" _blank
  click n145 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Streams.lean#L183" _blank
  click n146 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Streams.lean#L193" _blank
  click n147 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Streams.lean#L204" _blank
  click n148 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Streams.lean#L217" _blank
  click n149 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Streams.lean#L229" _blank
  click n150 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Streams.lean#L240" _blank
  click n151 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Streams.lean#L252" _blank
  click n152 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Streams.lean#L263" _blank
  click n153 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Streams.lean#L274" _blank
  click n154 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Streams.lean#L286" _blank
  click n155 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Streams.lean#L300" _blank
  click n156 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Initialisation.lean#L52" _blank
  click n157 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Initialisation.lean#L60" _blank
  click n158 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Initialisation.lean#L70" _blank
  click n159 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Initialisation.lean#L78" _blank
  click n160 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Copy.lean#L58" _blank
  click n161 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Checksums.lean#L20" _blank
  click n162 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Checksums.lean#L27" _blank
  click n163 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Checksums.lean#L35" _blank
  click n164 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Checksums.lean#L41" _blank
  click n165 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Checksums.lean#L48" _blank
  click n166 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Checksums.lean#L55" _blank
  click n167 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Checksums.lean#L62" _blank
  click n168 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Checksums.lean#L68" _blank
  click n169 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Checksums.lean#L75" _blank
  click n170 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Checksums.lean#L83" _blank
  click n171 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Checksums.lean#L89" _blank
  click n172 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Queries.lean#L18" _blank
  click n173 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Queries.lean#L23" _blank
  click n174 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/Sequences.lean#L225" _blank
  click n175 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Domains.lean#L15" _blank
  click n176 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Domains.lean#L28" _blank
  click n177 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/Domains.lean#L24" _blank
  click n178 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/Domains.lean#L50" _blank
  click n179 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Public/GzSafety.lean#L179" _blank
  click n180 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Api/Inflate.lean#L267" _blank
  click n181 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/ByteAddress.lean#L39" _blank
  click n182 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/ByteAddress.lean#L43" _blank
  click n183 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/ByteAddress.lean#L50" _blank
  click n184 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/ByteAddress.lean#L57" _blank
  click n185 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/ByteAddress.lean#L65" _blank
  click n186 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/ByteAddress.lean#L70" _blank
  click n187 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/ByteAddress.lean#L77" _blank
  click n188 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/ByteAddress.lean#L83" _blank
  click n189 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/ByteAddress.lean#L87" _blank
  click n190 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Crc32ByteViews.lean#L17" _blank
  click n191 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Crc32ByteViews.lean#L28" _blank
  click n192 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateFastBodyOrigin.lean#L18" _blank
  click n193 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateFastBodyToken.lean#L73" _blank
  click n194 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateFastCallOrigin.lean#L24" _blank
  click n195 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateFastDistanceOrigin.lean#L18" _blank
  click n196 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateFastDistanceResult.lean#L101" _blank
  click n197 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateFastDistanceSemantics.lean#L20" _blank
  click n198 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateFast.lean#L70" _blank
  click n199 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateFast.lean#L42" _blank
  click n200 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateFastLengthSemantics.lean#L34" _blank
  click n201 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateFastLengthTrace.lean#L51" _blank
  click n202 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateFastMatchHistory.lean#L39" _blank
  click n203 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateFastMatchHistory.lean#L25" _blank
  click n204 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateFastOrigin.lean#L68" _blank
  click n205 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateFastOrigin.lean#L57" _blank
  click n206 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateFastOrigin.lean#L81" _blank
  click n207 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateFastOrigin.lean#L38" _blank
  click n208 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateFastOrigin.lean#L27" _blank
  click n209 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateFastOrigin.lean#L32" _blank
  click n210 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateFastOrigin.lean#L46" _blank
  click n211 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateDecodeTableRejection.lean#L19" _blank
  click n212 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateDecodeTableSemantics.lean#L51" _blank
  click n213 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateDecodeTableShort.lean#L26" _blank
  click n214 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateDecodeTableSoundness.lean#L31" _blank
  click n215 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateDecodeTableFrame.lean#L20" _blank
  click n216 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateDecodeTableInvariant.lean#L51" _blank
  click n217 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateDecodeTableInvariant.lean#L68" _blank
  click n218 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateDecodeTableStability.lean#L30" _blank
  click n219 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateDecodeTableStability.lean#L43" _blank
  click n220 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateDecodeTableStability.lean#L54" _blank
  click n221 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateFastTableFlags.lean#L52" _blank
  click n222 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateFastTableFlags.lean#L66" _blank
  click n223 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateFastTableFlags.lean#L76" _blank
  click n224 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateFastTableFlags.lean#L42" _blank
  click n225 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateTableContent.lean#L32" _blank
  click n226 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateTableSafety.lean#L28" _blank
  click n227 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateTableExtent.lean#L28" _blank
  click n228 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateRootTable.lean#L21" _blank
  click n229 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/InflateSubtable.lean#L26" _blank
  click n230 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Math/LZ77CopySpec.lean#L22" _blank
  click n231 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Math/LZ77CopySpec.lean#L32" _blank
  click n232 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Math/LZ77HistorySpec.lean#L21" _blank
  click n233 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Math/LZ77HistorySpec.lean#L15" _blank
  click n234 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Math/LZ77HistorySpec.lean#L29" _blank
  click n235 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Math/LZ77HistorySpec.lean#L39" _blank
  click n236 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Format/Token.lean#L84" _blank
  click n237 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Format/Token.lean#L62" _blank
  click n238 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Functional/Format/Token.lean#L73" _blank
  click n239 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L45" _blank
  click n240 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L52" _blank
  click n241 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L252" _blank
  click n242 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L260" _blank
  click n243 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L268" _blank
  click n244 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L59" _blank
  click n245 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L286" _blank
  click n246 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L66" _blank
  click n247 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L239" _blank
  click n248 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L73" _blank
  click n249 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L81" _blank
  click n250 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L89" _blank
  click n251 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L224" _blank
  click n252 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L97" _blank
  click n253 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L104" _blank
  click n254 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L111" _blank
  click n255 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L118" _blank
  click n256 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L276" _blank
  click n257 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L281" _blank
  click n258 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L125" _blank
  click n259 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L134" _blank
  click n260 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L142" _blank
  click n261 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L149" _blank
  click n262 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L156" _blank
  click n263 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L163" _blank
  click n264 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L170" _blank
  click n265 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L178" _blank
  click n266 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L186" _blank
  click n267 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L194" _blank
  click n268 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L201" _blank
  click n269 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L208" _blank
  click n270 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/GzCalls.lean#L215" _blank
  click n271 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Back.lean#L46" _blank
  click n272 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Back.lean#L72" _blank
  click n273 "https://github.com/cla7aye15I4nd/zlib-f/blob/0c45d86/ZlibF/Spec/Safety/Back.lean#L30" _blank
  classDef unproved fill:#e5e7eb,color:#374151,stroke:#374151
  classDef default fill:#dbeafe,color:#1d4ed8,stroke:#1d4ed8
  classDef common fill:#fef3c7,color:#92400e,stroke:#92400e
  classDef all fill:#dcfce7,color:#166534,stroke:#166534
  classDef obstacle stroke:#b91c1c,stroke-width:3px
```

展开组件后，再展开一个目标，即可查看它的输入范围、状态和双向依赖。[证据索引](progress.md)保留提交 `0c45d86` 的目标与证明链接。

这一快照中没有记录在案的阻碍。

## 目标证据

<!-- proof-link-revision: 0c45d8635baffb4fda608517c4770ff7572f3978 -->

[证明讲解](overview.md) · [全部目标图](#proof-progress-graph) · [输入配置](spec/input-configurations.md)

本索引包含 **274 个固定目标**，分为公开接口执行、调用序列、初始化、实现层义务和抽象模型。每个目标分别列出输入范围、登记情况、证明正文和剩余工作。
抽象模型研究输入输出的数学关系；实现目标还要证明真实执行符合这些关系。一个本地证明完成后，仍需登记，并在具体提交上通过 CI 验收。所有证明都保留命题中写明的前置条件。
依赖区展示记录中已经建立的联系。未完成目标还需要哪些证明，见本页后面的具体工作清单。出现不允许的公理时，生成过程会停止。

## 状态说明

<a id="status-registered"></a>已登记证明：存在精确覆盖该目标、经过检查且列入登记表的定理。
<a id="status-local"></a>本地已检查：存在精确覆盖该目标的定理，但尚未列入登记表。
<a id="status-open"></a>未证明：还没有精确覆盖该目标的定理。
<a id="status-blocked"></a>存在阻碍：已有文档记录影响该目标的具体障碍。
<a id="status-not-planned"></a>不在计划内：目标仍然登记，但不在计划内，也不是必需目标（见范围）。
输入覆盖范围单独列出；CI 验收对应具体提交。
“陈述所允许的全部输入”指目标自身陈述的每个输入。目标陈述的输入可能少于 zlib.h 允许的范围：
[zlib.h 函数的无故障覆盖](#no-fault-coverage-of-zlibh-functions)列出了这些差距。

<a id="group-queries"></a>

## 库信息查询

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-compressbound"></a>[compressBound](../ZlibF/Spec/Functional/Queries.lean#L16) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/utility.md#compressbound); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.compressBound](../ZlibF/Proof/public-compress-bound.lean#L50) | — |
| <a id="target-zlibf-spec-public-goal-compressbound-z"></a>[compressBound_z](../ZlibF/Spec/Functional/Queries.lean#L21) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/utility.md#compressbound_z); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.compressBound_z](../ZlibF/Proof/public-compress-bound.lean#L47) | — |
| <a id="target-zlibf-spec-public-goal-zlibversion"></a>[zlibVersion](../ZlibF/Spec/Functional/Queries.lean#L27) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/utility.md#zlibversion); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.zlibVersion](../ZlibF/Proof/public-zlib-version.lean#L9) | — |
| <a id="target-zlibf-spec-public-goal-zlibcompileflags"></a>[zlibCompileFlags](../ZlibF/Spec/Functional/Queries.lean#L34) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/utility.md#zlibcompileflags); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.zlibCompileFlags](../ZlibF/Proof/public-zlib-compile-flags.lean#L7) | — |
| <a id="target-zlibf-spec-public-goal-zerror"></a>[zError](../ZlibF/Spec/Functional/Queries.lean#L40) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/utility.md#zerror); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.zError](../ZlibF/Proof/public-zerror.lean#L38) | — |
| <a id="target-zlibf-spec-public-goal-get-crc-table"></a>[get_crc_table](../ZlibF/Spec/Functional/Checksums.lean#L102) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/checksums.md#get_crc_table); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.get_crc_table](../ZlibF/Proof/public-get-crc-table.lean#L14) | — |

<a id="group-checksums"></a>

## 校验和

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-adler32"></a>[adler32](../ZlibF/Spec/Functional/Checksums.lean#L41) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/checksums.md#adler32); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.AdlerUpdateProof.adler_public](../ZlibF/Proof/public-adler-update.lean#L47) | — |
| <a id="target-zlibf-spec-public-goal-adler32-z"></a>[adler32_z](../ZlibF/Spec/Functional/Checksums.lean#L36) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/checksums.md#adler32_z); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.AdlerUpdateProof.adler_z_public](../ZlibF/Proof/public-adler-update.lean#L37) | — |
| <a id="target-zlibf-spec-public-goal-adler32-combine"></a>[adler32_combine](../ZlibF/Spec/Functional/Checksums.lean#L62) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/checksums.md#adler32_combine); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.AdlerCombineProof.combine_public](../ZlibF/Proof/public-adler-combine.lean#L119) | — |
| <a id="target-zlibf-spec-public-goal-adler32-combine64"></a>[adler32_combine64](../ZlibF/Spec/Functional/Checksums.lean#L66) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/checksums.md#adler32_combine64); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.AdlerCombineProof.combine64_public](../ZlibF/Proof/public-adler-combine.lean#L122) | — |
| <a id="target-zlibf-spec-public-goal-crc32"></a>[crc32](../ZlibF/Spec/Functional/Checksums.lean#L93) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/checksums.md#crc32); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.crc32](../ZlibF/Proof/public-crc-updates.lean#L29) | — |
| <a id="target-zlibf-spec-public-goal-crc32-z"></a>[crc32_z](../ZlibF/Spec/Functional/Checksums.lean#L85) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/checksums.md#crc32_z); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.crc32_z](../ZlibF/Proof/public-crc-updates.lean#L19) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine-gen"></a>[crc32_combine_gen](../ZlibF/Spec/Functional/Checksums.lean#L116) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/checksums.md#crc32_combine_gen); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.CrcCombineProof.gen](../ZlibF/Proof/public-crc-combine.lean#L77) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine-gen64"></a>[crc32_combine_gen64](../ZlibF/Spec/Functional/Checksums.lean#L119) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/checksums.md#crc32_combine_gen64); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.CrcCombineProof.gen64](../ZlibF/Proof/public-crc-combine.lean#L83) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine-op"></a>[crc32_combine_op](../ZlibF/Spec/Functional/Checksums.lean#L126) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/checksums.md#crc32_combine_op); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.CrcCombineProof.op](../ZlibF/Proof/public-crc-combine.lean#L89) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine"></a>[crc32_combine](../ZlibF/Spec/Functional/Checksums.lean#L138) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/checksums.md#crc32_combine); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.CrcCombineProof.combine](../ZlibF/Proof/public-crc-combine.lean#L95) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine64"></a>[crc32_combine64](../ZlibF/Spec/Functional/Checksums.lean#L141) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/checksums.md#crc32_combine64); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.CrcCombineProof.combine64](../ZlibF/Proof/public-crc-combine.lean#L101) | — |
| <a id="target-zlibf-spec-public-goal-adler32-safety"></a>[adler32_safety](../ZlibF/Spec/Safety/Checksums.lean#L20) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.adler32_safety](../ZlibF/Proof/public-stateless-safety.lean#L21) | — |
| <a id="target-zlibf-spec-public-goal-adler32-z-safety"></a>[adler32_z_safety](../ZlibF/Spec/Safety/Checksums.lean#L27) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.adler32_z_safety](../ZlibF/Proof/public-stateless-safety.lean#L25) | — |
| <a id="target-zlibf-spec-public-goal-adler32-combine-safety"></a>[adler32_combine_safety](../ZlibF/Spec/Safety/Checksums.lean#L35) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.adler32_combine_safety](../ZlibF/Proof/public-stateless-safety.lean#L29) | — |
| <a id="target-zlibf-spec-public-goal-adler32-combine64-safety"></a>[adler32_combine64_safety](../ZlibF/Spec/Safety/Checksums.lean#L41) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.adler32_combine64_safety](../ZlibF/Proof/public-stateless-safety.lean#L34) | — |
| <a id="target-zlibf-spec-public-goal-crc32-safety"></a>[crc32_safety](../ZlibF/Spec/Safety/Checksums.lean#L48) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.crc32_safety](../ZlibF/Proof/public-stateless-safety.lean#L39) | — |
| <a id="target-zlibf-spec-public-goal-crc32-z-safety"></a>[crc32_z_safety](../ZlibF/Spec/Safety/Checksums.lean#L55) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.crc32_z_safety](../ZlibF/Proof/public-stateless-safety.lean#L43) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine-gen-safety"></a>[crc32_combine_gen_safety](../ZlibF/Spec/Safety/Checksums.lean#L62) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.crc32_combine_gen_safety](../ZlibF/Proof/public-stateless-safety.lean#L47) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine-gen64-safety"></a>[crc32_combine_gen64_safety](../ZlibF/Spec/Safety/Checksums.lean#L68) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.crc32_combine_gen64_safety](../ZlibF/Proof/public-stateless-safety.lean#L51) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine-op-safety"></a>[crc32_combine_op_safety](../ZlibF/Spec/Safety/Checksums.lean#L75) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.crc32_combine_op_safety](../ZlibF/Proof/public-stateless-safety.lean#L55) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine-safety"></a>[crc32_combine_safety](../ZlibF/Spec/Safety/Checksums.lean#L83) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.crc32_combine_safety](../ZlibF/Proof/public-stateless-safety.lean#L67) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine64-safety"></a>[crc32_combine64_safety](../ZlibF/Spec/Safety/Checksums.lean#L89) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.crc32_combine64_safety](../ZlibF/Proof/public-stateless-safety.lean#L71) | — |

<a id="group-addresses"></a>

## 字节地址模型

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-c-byteaddress-spec-goal-address-read-is-pure"></a>[address_read_is_pure](../ZlibF/Spec/ByteAddress.lean#L39) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.address_read_is_pure](../ZlibF/Proof/ByteAddress.lean#L28) | — |
| <a id="target-c-byteaddress-spec-goal-raw-block-unchanged"></a>[raw_block_unchanged](../ZlibF/Spec/ByteAddress.lean#L43) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.raw_block_unchanged](../ZlibF/Proof/ByteAddress.lean#L33) | — |
| <a id="target-c-byteaddress-spec-goal-every-layout-is-representable"></a>[every_layout_is_representable](../ZlibF/Spec/ByteAddress.lean#L50) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.every_layout_is_representable](../ZlibF/Proof/ByteAddress.lean#L39) | — |
| <a id="target-c-byteaddress-spec-goal-every-existing-heap-accepts-layout"></a>[every_existing_heap_accepts_layout](../ZlibF/Spec/ByteAddress.lean#L57) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.every_existing_heap_accepts_layout](../ZlibF/Proof/ByteAddress.lean#L94) | — |
| <a id="target-c-byteaddress-spec-goal-mask-refines-base-plus-offset"></a>[mask_refines_base_plus_offset](../ZlibF/Spec/ByteAddress.lean#L65) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.mask_refines_base_plus_offset](../ZlibF/Proof/ByteAddress.lean#L54) | — |
| <a id="target-c-byteaddress-spec-goal-pointer-advance-preserves-low-bits"></a>[pointer_advance_preserves_low_bits](../ZlibF/Spec/ByteAddress.lean#L70) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.pointer_advance_preserves_low_bits](../ZlibF/Proof/ByteAddress.lean#L60) | — |
| <a id="target-c-byteaddress-spec-goal-first-aligned-offset"></a>[first_aligned_offset](../ZlibF/Spec/ByteAddress.lean#L77) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.first_aligned_offset](../ZlibF/Proof/ByteAddress.lean#L67) | — |
| <a id="target-c-byteaddress-spec-goal-byte-stores-preserve-bases"></a>[byte_stores_preserve_bases](../ZlibF/Spec/ByteAddress.lean#L83) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.byte_stores_preserve_bases](../ZlibF/Proof/ByteAddress.lean#L81) | — |
| <a id="target-c-byteaddress-spec-goal-byte-modifies-preserve-bases"></a>[byte_modifies_preserve_bases](../ZlibF/Spec/ByteAddress.lean#L87) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.byte_modifies_preserve_bases](../ZlibF/Proof/ByteAddress.lean#L88) | — |

<a id="group-inflate"></a>

## 解压流

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-inflatecopy"></a>[inflateCopy](../ZlibF/Spec/Functional/Copy.lean#L16) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflatecopy); [输入范围](spec/input-configurations.md#inflate-inputs) | [Zlib.Inflate.Proofs.inflate_copy_public](../ZlibF/Proof/public-inflate-copy.lean#L13) | — |
| <a id="target-zlibf-spec-public-goal-inflateinit2"></a>[inflateInit2_](../ZlibF/Spec/Functional/Initialisation.lean#L15) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflateinit2_); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.Proofs.InflateInit.inflate_init2_public](../ZlibF/Proof/public-inflate-init2.lean#L20) | — |
| <a id="target-zlibf-spec-public-goal-inflateinit"></a>[inflateInit_](../ZlibF/Spec/Functional/Initialisation.lean#L20) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflateinit_); [输入范围](spec/input-configurations.md#inflate-inputs) | [Zlib.Inflate.Proofs.inflate_default_init_contract](../ZlibF/Proof/inflate.c.default-entry.lean#L59); [ZlibF.Spec.Public.Proofs.InflateInit.init15_public](../ZlibF/Proof/public-inflate-init.lean#L86) | — |
| <a id="target-zlibf-spec-public-goal-inflateresetkeep"></a>[inflateResetKeep](../ZlibF/Spec/Functional/Lifecycle.lean#L16) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflateresetkeep); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateResetKeepProof.resetkeep_public](../ZlibF/Proof/public-inflate-reset-keep.lean#L10) | — |
| <a id="target-zlibf-spec-public-goal-inflatereset"></a>[inflateReset](../ZlibF/Spec/Functional/Lifecycle.lean#L23) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflatereset); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateResetProof.reset_public](../ZlibF/Proof/public-inflate-reset.lean#L18) | — |
| <a id="target-zlibf-spec-public-goal-inflatereset2"></a>[inflateReset2](../ZlibF/Spec/Functional/Lifecycle.lean#L34) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflatereset2); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateReset2Proof.reset2_public](../ZlibF/Proof/public-inflate-reset2.lean#L63) | — |
| <a id="target-zlibf-spec-public-goal-inflateend"></a>[inflateEnd](../ZlibF/Spec/Functional/Lifecycle.lean#L51) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflateend); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateEndProof.inflate_end_public](../ZlibF/Proof/public-inflate-end.lean#L57) | — |
| <a id="target-zlibf-spec-public-goal-inflategetdictionary"></a>[inflateGetDictionary](../ZlibF/Spec/Functional/Lifecycle.lean#L61) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflategetdictionary); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateDictionaryProof.inflate_getdict_public](../ZlibF/Proof/public-inflate-getdict.lean#L12) | — |
| <a id="target-zlibf-spec-public-goal-inflategetheader"></a>[inflateGetHeader](../ZlibF/Spec/Functional/Lifecycle.lean#L71) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflategetheader); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateHeaderProof.getheader_public](../ZlibF/Proof/public-inflate-header.lean#L36) | — |
| <a id="target-zlibf-spec-public-goal-inflatesetdictionary"></a>[inflateSetDictionary](../ZlibF/Spec/Functional/Lifecycle.lean#L109) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflatesetdictionary); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.Proofs.inflateSetDictionary_public](../ZlibF/Proof/public-inflate-setdict.lean#L94) | — |
| <a id="target-zlibf-spec-public-goal-inflatesyncpoint"></a>[inflateSyncPoint](../ZlibF/Spec/Functional/StreamQueries.lean#L15) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflatesyncpoint); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateQueryProof.syncpoint_public](../ZlibF/Proof/public-inflate-small-queries.lean#L46) | — |
| <a id="target-zlibf-spec-public-goal-inflatemark"></a>[inflateMark](../ZlibF/Spec/Functional/StreamQueries.lean#L24) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflatemark); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateMarkProof.mark_public](../ZlibF/Proof/public-inflate-mark.lean#L72) | — |
| <a id="target-zlibf-spec-public-goal-inflatecodesused"></a>[inflateCodesUsed](../ZlibF/Spec/Functional/StreamQueries.lean#L35) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflatecodesused); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.Proofs.inflate_codes_used](../ZlibF/Proof/Api/QueryLayout.lean#L73) | — |
| <a id="target-zlibf-spec-public-goal-inflateundermine"></a>[inflateUndermine](../ZlibF/Spec/Functional/StreamQueries.lean#L43) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflateundermine); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateQueryProof.undermine_public](../ZlibF/Proof/public-inflate-small-queries.lean#L62) | — |
| <a id="target-zlibf-spec-public-goal-inflatevalidate"></a>[inflateValidate](../ZlibF/Spec/Functional/StreamQueries.lean#L51) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflatevalidate); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateQueryProof.validate_public](../ZlibF/Proof/public-inflate-small-queries.lean#L77) | — |
| <a id="target-zlibf-spec-public-goal-inflateprime"></a>[inflatePrime](../ZlibF/Spec/Functional/StreamQueries.lean#L62) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflateprime); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflatePrimeProof.prime_public](../ZlibF/Proof/public-inflate-prime.lean#L118) | — |
| <a id="target-zlibf-spec-public-goal-inflate"></a>[inflate](../ZlibF/Spec/Functional/Streams.lean#L28) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflate); [输入范围](spec/input-configurations.md#inflate-inputs) | [Zlib.Inflate.Proofs.inflate_public](../ZlibF/Proof/public-inflate.lean#L11) | — |
| <a id="target-zlibf-spec-public-goal-inflatesync"></a>[inflateSync](../ZlibF/Spec/Functional/Streams.lean#L151) | 未证明 / 未证明 | [契约](../docs/spec/api/inflate-stream.md#inflatesync); [输入范围](spec/input-configurations.md#inflate-inputs) | — | [需要：扫描与状态序列](progress.md#readiness-inflatesync) |
| <a id="target-zlibf-spec-public-goal-inflate-sequence-safety"></a>[inflate_sequence_safety](../ZlibF/Spec/Safety/Sequences.lean#L28) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#inflate-inputs) | [Zlib.Inflate.Proofs.inflate_sequence_safety_public](../ZlibF/Proof/public-inflate-sequence-safety.lean#L11) | — |
| <a id="target-zlibf-spec-public-goal-inflate-back-sequence-safety"></a>[inflate_back_sequence_safety](../ZlibF/Spec/Public/Sequences.lean#L196) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#inflate-inputs) | [Zlib.Infback.Safety.inflate_back_sequence_safety](../ZlibF/Proof/infback.c.safety-fast.lean#L438) | — |
| <a id="target-zlibf-spec-public-goal-inflate-refusal"></a>[inflate_refusal](../ZlibF/Spec/Safety/Refusals.lean#L30) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.RefusalProof.inflate_refusal](../ZlibF/Proof/public-stream-refusal.lean#L46) | — |
| <a id="target-zlibf-spec-public-goal-inflate-safety"></a>[inflate_safety](../ZlibF/Spec/Safety/Streams.lean#L48) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.inflate_safety](../ZlibF/Proof/public-stream-call-safety.lean#L65) | — |
| <a id="target-zlibf-spec-public-goal-inflatesetdictionary-safety"></a>[inflateSetDictionary_safety](../ZlibF/Spec/Safety/Streams.lean#L60) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.inflateSetDictionary_safety](../ZlibF/Proof/public-stream-call-safety.lean#L70) | — |
| <a id="target-zlibf-spec-public-goal-inflategetdictionary-safety"></a>[inflateGetDictionary_safety](../ZlibF/Spec/Safety/Streams.lean#L71) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.inflateGetDictionary_safety](../ZlibF/Proof/public-stream-call-safety.lean#L75) | — |
| <a id="target-zlibf-spec-public-goal-inflatesync-safety"></a>[inflateSync_safety](../ZlibF/Spec/Safety/Streams.lean#L84) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.inflateSync_safety](../ZlibF/Proof/public-stream-call-safety.lean#L80) | — |
| <a id="target-zlibf-spec-public-goal-inflatereset-safety"></a>[inflateReset_safety](../ZlibF/Spec/Safety/Streams.lean#L96) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.inflateReset_safety](../ZlibF/Proof/public-stream-call-safety.lean#L85) | — |
| <a id="target-zlibf-spec-public-goal-inflatereset2-safety"></a>[inflateReset2_safety](../ZlibF/Spec/Safety/Streams.lean#L106) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.inflateReset2_safety](../ZlibF/Proof/public-stream-call-safety.lean#L90) | — |
| <a id="target-zlibf-spec-public-goal-inflateprime-safety"></a>[inflatePrime_safety](../ZlibF/Spec/Safety/Streams.lean#L117) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.inflatePrime_safety](../ZlibF/Proof/public-stream-call-safety.lean#L95) | — |
| <a id="target-zlibf-spec-public-goal-inflatemark-safety"></a>[inflateMark_safety](../ZlibF/Spec/Safety/Streams.lean#L128) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.inflateMark_safety](../ZlibF/Proof/public-stream-call-safety.lean#L100) | — |
| <a id="target-zlibf-spec-public-goal-inflategetheader-safety"></a>[inflateGetHeader_safety](../ZlibF/Spec/Safety/Streams.lean#L138) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.inflateGetHeader_safety](../ZlibF/Proof/public-stream-call-safety.lean#L105) | — |
| <a id="target-zlibf-spec-public-goal-inflateend-safety"></a>[inflateEnd_safety](../ZlibF/Spec/Safety/Streams.lean#L286) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.inflateEnd_safety](../ZlibF/Proof/public-stream-call-safety.lean#L172) | — |
| <a id="target-zlibf-spec-public-goal-inflateinit2-safety"></a>[inflateInit2__safety](../ZlibF/Spec/Safety/Initialisation.lean#L52) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InitSafetyProof.inflateInit2__safety](../ZlibF/Proof/public-init-safety.lean#L112) | — |
| <a id="target-zlibf-spec-public-goal-inflateinit-safety"></a>[inflateInit__safety](../ZlibF/Spec/Safety/Initialisation.lean#L60) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InitSafetyProof.inflateInit__safety](../ZlibF/Proof/public-init-safety.lean#L132) | — |
| <a id="target-zlibf-spec-public-goal-inflatecopy-safety"></a>[inflateCopy_safety](../ZlibF/Spec/Safety/Copy.lean#L58) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateCopySafetyProof.inflateCopy_safety](../ZlibF/Proof/public-inflate-copy-safety.lean#L17) | — |

<a id="group-fast"></a>

## 快速解码器的证明义务

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlib-inffast-spec-bodyorigin-goal-actual-body-preserves-origin"></a>[actual_body_preserves_origin](../ZlibF/Spec/InflateFastBodyOrigin.lean#L18) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.BodyOriginProof.actual_body_preserves_origin](../ZlibF/Proof/inffast.c.body-origin.lean#L380); [Zlib.Inffast.Proofs.actual_body_preserves_origin](../ZlibF/Proof/inffast.c.body-origin.lean#L380) | — |
| <a id="target-zlib-inffast-spec-bodytoken-goal-actual-body-refines-token"></a>[actual_body_refines_token](../ZlibF/Spec/InflateFastBodyToken.lean#L73) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.BodyTokenProof.actual_body_refines_token](../ZlibF/Proof/inffast.c.body-token.lean#L571); [Zlib.Inffast.Proofs.actual_body_refines_token](../ZlibF/Proof/inffast.c.body-token.lean#L571) | — |
| <a id="target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin"></a>[actual_fast_preserves_origin](../ZlibF/Spec/InflateFastCallOrigin.lean#L24) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_fast_preserves_origin](../ZlibF/Proof/inffast.c.call-origin.lean#L180); [ZlibF.Proof.Registration.fast_call_origin](../ZlibF/Proof/proof-registrations.lean#L14) | — |
| <a id="target-zlib-inffast-spec-distanceorigin-goal-actual-distance-block-preserves-origin"></a>[actual_distance_block_preserves_origin](../ZlibF/Spec/InflateFastDistanceOrigin.lean#L18) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_distance_block_preserves_origin](../ZlibF/Proof/inffast.c.distance-origin.lean#L327) | — |
| <a id="target-zlib-inffast-spec-distanceresult-goal-actual-distance-refines-lz77"></a>[actual_distance_refines_lz77](../ZlibF/Spec/InflateFastDistanceResult.lean#L101) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_distance_refines_lz77](../ZlibF/Proof/inffast.c.distance-result.lean#L386) | — |
| <a id="target-zlib-inffast-spec-distancesemantics-goal-distance-lookup-matches-format"></a>[distance_lookup_matches_format](../ZlibF/Spec/InflateFastDistanceSemantics.lean#L20) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.distance_lookup_matches_format](../ZlibF/Proof/inffast.c.distance-semantics.lean#L22) | — |
| <a id="target-zlib-inffast-spec-goal-fast-safe"></a>[fast_safe](../ZlibF/Spec/InflateFast.lean#L70) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.inflate_fast_safe](../ZlibF/Proof/inffast.c.final.lean#L253) | — |
| <a id="target-zlib-inffast-spec-goal-step-safe"></a>[step_safe](../ZlibF/Spec/InflateFast.lean#L42) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.inflate_fast_body_step_safe](../ZlibF/Proof/inffast.c.body.lean#L350) | — |
| <a id="target-zlib-inffast-spec-lengthsemantics-goal-length-lookup-matches-format"></a>[length_lookup_matches_format](../ZlibF/Spec/InflateFastLengthSemantics.lean#L34) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.length_lookup_matches_format](../ZlibF/Proof/inffast.c.length-semantics.lean#L22) | — |
| <a id="target-zlib-inffast-spec-lengthtrace-goal-actual-body-retains-selected-length"></a>[actual_body_retains_selected_length](../ZlibF/Spec/InflateFastLengthTrace.lean#L51) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.LengthTraceProof.actual_body_retains_selected_length](../ZlibF/Proof/inffast.c.length-trace.lean#L250); [Zlib.Inffast.Proofs.actual_body_retains_selected_length](../ZlibF/Proof/inffast.c.length-trace.lean#L250) | — |
| <a id="target-zlib-inffast-spec-matchhistory-goal-actual-copy-match-refines-lz77"></a>[actual_copy_match_refines_lz77](../ZlibF/Spec/InflateFastMatchHistory.lean#L39) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_copy_match_refines_lz77](../ZlibF/Proof/inffast.c.match-history.lean#L328) | — |
| <a id="target-zlib-inffast-spec-matchhistory-goal-match-array-refines-lz77"></a>[match_array_refines_lz77](../ZlibF/Spec/InflateFastMatchHistory.lean#L25) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.fast_match_array_refines_lz77](../ZlibF/Math/InflateFastMatchHistory.lean#L56) | — |
| <a id="target-zlib-inffast-spec-origin-goal-actual-drop-preserves-origin"></a>[actual_drop_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L68) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_drop_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L138) | — |
| <a id="target-zlib-inffast-spec-origin-goal-actual-pull-preserves-origin"></a>[actual_pull_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L57) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_pull_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L127) | — |
| <a id="target-zlib-inffast-spec-origin-goal-actual-rollback-preserves-origin"></a>[actual_rollback_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L81) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_rollback_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L150) | — |
| <a id="target-zlib-inffast-spec-origin-goal-drop-preserves-origin"></a>[drop_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L38) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.drop_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L41) | — |
| <a id="target-zlib-inffast-spec-origin-goal-initial-origin"></a>[initial_origin](../ZlibF/Spec/InflateFastOrigin.lean#L27) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.initial_origin](../ZlibF/Proof/inffast.c.origin.lean#L16) | — |
| <a id="target-zlib-inffast-spec-origin-goal-pull-preserves-origin"></a>[pull_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L32) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.pull_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L21) | — |
| <a id="target-zlib-inffast-spec-origin-goal-rollback-preserves-origin"></a>[rollback_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L46) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.rollback_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L83) | — |

<a id="group-tables"></a>

## 解码表的证明义务

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlib-inftrees-spec-decoderejection-goal-decode-table-classifies-input"></a>[decode_table_classifies_input](../ZlibF/Spec/InflateDecodeTableRejection.lean#L19) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_classifies_input](../ZlibF/Proof/inftrees.c.decode.short.lean#L62) | — |
| <a id="target-zlib-inftrees-spec-decodesemantics-goal-decode-table-matches-format"></a>[decode_table_matches_format](../ZlibF/Spec/InflateDecodeTableSemantics.lean#L51) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_matches_format](../ZlibF/Proof/inftrees.c.decode.semantics.lean#L327) | — |
| <a id="target-zlib-inftrees-spec-decodeshort-goal-short-decode-table-leaf-sound"></a>[short_decode_table_leaf_sound](../ZlibF/Spec/InflateDecodeTableShort.lean#L26) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.short_decode_table_leaf_sound](../ZlibF/Proof/inftrees.c.decode.short.lean#L33) | — |
| <a id="target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound"></a>[decode_table_leaf_sound](../ZlibF/Spec/InflateDecodeTableSoundness.lean#L31) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_leaf_sound](../ZlibF/Proof/inftrees.c.decode.soundness.lean#L244) | — |
| <a id="target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved"></a>[decode_table_read_preserved](../ZlibF/Spec/InflateDecodeTableFrame.lean#L20) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_read_preserved](../ZlibF/Proof/inftrees.c.decode.frame.lean#L55) | — |
| <a id="target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant"></a>[constructor_establishes_decode_table_invariant](../ZlibF/Spec/InflateDecodeTableInvariant.lean#L51) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.constructor_establishes_decode_table_invariant](../ZlibF/Proof/inftrees.c.decode.invariant.lean#L13) | — |
| <a id="target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix"></a>[decode_table_invariant_of_prefix](../ZlibF/Spec/InflateDecodeTableInvariant.lean#L68) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_invariant_of_prefix](../ZlibF/Proof/inftrees.c.decode.invariant-prefix.lean#L22) | — |
| <a id="target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability"></a>[constructor_establishes_query_stability](../ZlibF/Spec/InflateDecodeTableStability.lean#L30) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.constructor_establishes_query_stability](../ZlibF/Proof/inftrees.c.decode.stability.lean#L190) | — |
| <a id="target-zlib-inftrees-spec-decodetablestability-goal-query-stability-of-prefix"></a>[query_stability_of_prefix](../ZlibF/Spec/InflateDecodeTableStability.lean#L43) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.query_stability_of_prefix](../ZlibF/Proof/inftrees.c.decode.stability-rejection.lean#L20) | — |
| <a id="target-zlib-inftrees-spec-decodetablestability-goal-short-rejected-leaf-stays-invalid"></a>[short_rejected_leaf_stays_invalid](../ZlibF/Spec/InflateDecodeTableStability.lean#L54) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.short_rejected_leaf_stays_invalid](../ZlibF/Proof/inftrees.c.decode.stability-rejection.lean#L31) | — |
| <a id="target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags"></a>[constructor_establishes_fast_leaf_flags](../ZlibF/Spec/InflateFastTableFlags.lean#L52) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.constructor_establishes_fast_leaf_flags](../ZlibF/Proof/inftrees.c.decode.fast-flags.lean#L125) | — |
| <a id="target-zlib-inftrees-spec-fasttableflags-goal-fast-leaf-flags-of-prefix"></a>[fast_leaf_flags_of_prefix](../ZlibF/Spec/InflateFastTableFlags.lean#L66) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.fast_leaf_flags_of_prefix](../ZlibF/Proof/inftrees.c.decode.fast-flags-frame.lean#L48); [ZlibF.Proof.Registration.fast_leaf_flags_of_prefix](../ZlibF/Proof/proof-registrations.lean#L20) | — |
| <a id="target-zlib-inftrees-spec-fasttableflags-goal-fixed-tables-have-fast-leaf-flags"></a>[fixed_tables_have_fast_leaf_flags](../ZlibF/Spec/InflateFastTableFlags.lean#L76) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.fixed_tables_have_fast_leaf_flags](../ZlibF/Proof/inffixed.h.fast-flags.lean#L55); [ZlibF.Proof.Registration.fixed_tables_fast_leaf_flags](../ZlibF/Proof/proof-registrations.lean#L26) | — |
| <a id="target-zlib-inftrees-spec-fasttableflags-goal-leaf-classification-agrees"></a>[leaf_classification_agrees](../ZlibF/Spec/InflateFastTableFlags.lean#L42) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.leaf_classification_agrees](../ZlibF/Proof/inftrees.c.decode.fast-flags-frame.lean#L9); [ZlibF.Proof.Registration.leaf_classification_agrees](../ZlibF/Proof/proof-registrations.lean#L32) | — |
| <a id="target-zlib-inftrees-spec-goal-inflate-table-content"></a>[inflate_table_content](../ZlibF/Spec/InflateTableContent.lean#L32) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.inflate_table_content](../ZlibF/Proof/inftrees.c.content.lean#L327) | — |
| <a id="target-zlib-inftrees-spec-goal-inflate-table-decoder-safe"></a>[inflate_table_decoder_safe](../ZlibF/Spec/InflateTableSafety.lean#L28) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.inflate_table_decoder_safe](../ZlibF/Proof/inftrees.c.decoder-safe.lean#L143) | — |
| <a id="target-zlib-inftrees-spec-goal-inflate-table-read-extent"></a>[inflate_table_read_extent](../ZlibF/Spec/InflateTableExtent.lean#L28) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.inflate_table_read_extent](../ZlibF/Proof/inftrees.c.read-extent.lean#L139) | — |
| <a id="target-zlib-inftrees-spec-roottable-goal-constructor-root-bits"></a>[constructor_root_bits](../ZlibF/Spec/InflateRootTable.lean#L21) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.constructor_root_bits](../ZlibF/Proof/inftrees.c.decode.bits.lean#L260) | — |
| <a id="target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits"></a>[constructor_subtable_bits](../ZlibF/Spec/InflateSubtable.lean#L26) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.constructor_subtable_bits](../ZlibF/Proof/inftrees.c.decode.bits.lean#L221) | — |

<a id="group-copy"></a>

## 回引用复制

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-math-lz77copy-goal-output-copy-refines-lz77"></a>[output_copy_refines_lz77](../ZlibF/Math/LZ77CopySpec.lean#L22) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77Copy.output_copy_refines_lz77](../ZlibF/Math/LZ77Copy.lean#L65) | — |
| <a id="target-zlibf-math-lz77copy-goal-window-copy-refines-lz77"></a>[window_copy_refines_lz77](../ZlibF/Math/LZ77CopySpec.lean#L32) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77Copy.window_copy_refines_lz77](../ZlibF/Math/LZ77Copy.lean#L124) | — |
| <a id="target-zlibf-math-lz77history-goal-copy-back-compose"></a>[copy_back_compose](../ZlibF/Math/LZ77HistorySpec.lean#L21) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77History.copy_back_compose](../ZlibF/Math/LZ77History.lean#L31) | — |
| <a id="target-zlibf-math-lz77history-goal-copy-back-extends-history"></a>[copy_back_extends_history](../ZlibF/Math/LZ77HistorySpec.lean#L15) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77History.copy_back_extends_history](../ZlibF/Math/LZ77History.lean#L17) | — |
| <a id="target-zlibf-math-lz77history-goal-retained-history-agrees"></a>[retained_history_agrees](../ZlibF/Math/LZ77HistorySpec.lean#L29) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77History.retained_history_agrees](../ZlibF/Math/LZ77History.lean#L59) | — |
| <a id="target-zlibf-math-lz77history-goal-window-distance-check-agrees"></a>[window_distance_check_agrees](../ZlibF/Math/LZ77HistorySpec.lean#L39) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77History.window_distance_check_agrees](../ZlibF/Math/LZ77History.lean#L72) | — |

<a id="group-deflate"></a>

## 压缩流

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-deflatecopy"></a>[deflateCopy](../ZlibF/Spec/Functional/Copy.lean#L46) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/deflate-stream.md#deflatecopy); [输入范围](spec/input-configurations.md#deflate-inputs) | [Zlib.Deflate.Universal.deflate_copy_public](../ZlibF/Proof/public-deflate-copy.lean#L68) | — |
| <a id="target-zlibf-spec-public-goal-deflateinit2"></a>[deflateInit2_](../ZlibF/Spec/Functional/Initialisation.lean#L25) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/deflate-stream.md#deflateinit2_); [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.Proofs.DeflateInit2.deflateInit2_proof](../ZlibF/Proof/public-deflate-init2.lean#L18) | — |
| <a id="target-zlibf-spec-public-goal-deflateinit"></a>[deflateInit_](../ZlibF/Spec/Functional/Initialisation.lean#L32) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/deflate-stream.md#deflateinit_); [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.Proofs.DeflateInit.deflateInit_proof](../ZlibF/Proof/public-deflate-init.lean#L162) | — |
| <a id="target-zlibf-spec-public-goal-deflategetdictionary"></a>[deflateGetDictionary](../ZlibF/Spec/Functional/Lifecycle.lean#L82) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/deflate-stream.md#deflategetdictionary); [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateDictionaryProof.deflate_getdict_public](../ZlibF/Proof/public-deflate-getdict.lean#L12) | — |
| <a id="target-zlibf-spec-public-goal-deflateend"></a>[deflateEnd](../ZlibF/Spec/Functional/Lifecycle.lean#L92) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/deflate-stream.md#deflateend); [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateEndProof.deflate_end_public](../ZlibF/Proof/public-deflate-end.lean#L12) | — |
| <a id="target-zlibf-spec-public-goal-deflateresetkeep"></a>[deflateResetKeep](../ZlibF/Spec/Functional/Lifecycle.lean#L102) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/deflate-stream.md#deflateresetkeep); [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateResetKeepProof.deflate_resetkeep_public](../ZlibF/Proof/public-deflate-reset-keep.lean#L21) | — |
| <a id="target-zlibf-spec-public-goal-deflatereset"></a>[deflateReset](../ZlibF/Spec/Functional/Lifecycle.lean#L105) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/deflate-stream.md#deflatereset); [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateResetProof.deflate_reset_public](../ZlibF/Proof/public-deflate-reset.lean#L54) | — |
| <a id="target-zlibf-spec-public-goal-deflatesetdictionary"></a>[deflateSetDictionary](../ZlibF/Spec/Functional/Lifecycle.lean#L131) | 未证明 / 未证明 | [契约](../docs/spec/api/deflate-stream.md#deflatesetdictionary); [输入范围](spec/input-configurations.md#deflate-inputs) | — | [开始：窗口与哈希](progress.md#readiness-deflatesetdictionary) |
| <a id="target-zlibf-spec-public-goal-deflatepending"></a>[deflatePending](../ZlibF/Spec/Functional/StreamQueries.lean#L75) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/deflate-stream.md#deflatepending); [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateQueryProof.pending_public](../ZlibF/Proof/public-deflate-small-queries.lean#L147) | — |
| <a id="target-zlibf-spec-public-goal-deflateused"></a>[deflateUsed](../ZlibF/Spec/Functional/StreamQueries.lean#L86) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/deflate-stream.md#deflateused); [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateQueryProof.used_public](../ZlibF/Proof/public-deflate-small-queries.lean#L50) | — |
| <a id="target-zlibf-spec-public-goal-deflatetune"></a>[deflateTune](../ZlibF/Spec/Functional/StreamQueries.lean#L94) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/deflate-stream.md#deflatetune); [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateQueryProof.tune_public](../ZlibF/Proof/public-deflate-small-queries.lean#L63) | — |
| <a id="target-zlibf-spec-public-goal-deflatesetheader"></a>[deflateSetHeader](../ZlibF/Spec/Functional/StreamQueries.lean#L107) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/deflate-stream.md#deflatesetheader); [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateQueryProof.header_public](../ZlibF/Proof/public-deflate-small-queries.lean#L76) | — |
| <a id="target-zlibf-spec-public-goal-deflate"></a>[deflate](../ZlibF/Spec/Functional/Streams.lean#L68) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/deflate-stream.md#deflate); [输入范围](spec/input-configurations.md#deflate-inputs) | [Zlib.Deflate.Universal.deflate_safety](../ZlibF/Proof/public-deflate-goals.lean#L21) | — |
| <a id="target-zlibf-spec-public-goal-deflatebound-z"></a>[deflateBound_z](../ZlibF/Spec/Functional/Streams.lean#L105) | 未证明 / 未证明 | [契约](../docs/spec/api/deflate-stream.md#deflatebound_z); [输入范围](spec/input-configurations.md#deflate-inputs) | — | [开始：上界与头部审查](progress.md#readiness-deflatebound-z) |
| <a id="target-zlibf-spec-public-goal-deflatebound"></a>[deflateBound](../ZlibF/Spec/Functional/Streams.lean#L109) | 未证明 / 未证明 | [契约](../docs/spec/api/deflate-stream.md#deflatebound); [输入范围](spec/input-configurations.md#deflate-inputs) | — | [开始：上界与头部审查](progress.md#readiness-deflatebound-z) |
| <a id="target-zlibf-spec-public-goal-deflateprime"></a>[deflatePrime](../ZlibF/Spec/Functional/Streams.lean#L114) | 未证明 / 未证明 | [契约](../docs/spec/api/deflate-stream.md#deflateprime); [输入范围](spec/input-configurations.md#deflate-inputs) | — | [开始：压紧与位操作](progress.md#readiness-deflateprime) |
| <a id="target-zlibf-spec-public-goal-deflateparams"></a>[deflateParams](../ZlibF/Spec/Functional/Streams.lean#L132) | 未证明 / 未证明 | [契约](../docs/spec/api/deflate-stream.md#deflateparams); [输入范围](spec/input-configurations.md#deflate-inputs) | — | [需要：块交付与参数状态](progress.md#readiness-deflateparams) |
| <a id="target-zlibf-spec-public-goal-deflate-sequence-safety"></a>[deflate_sequence_safety](../ZlibF/Spec/Safety/Sequences.lean#L19) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#deflate-inputs) | [Zlib.Deflate.Universal.deflate_sequence_safety](../ZlibF/Proof/public-deflate-goals.lean#L26) | — |
| <a id="target-zlibf-spec-public-goal-deflatecopy-safety"></a>[deflateCopy_safety](../ZlibF/Spec/Safety/Copy.lean#L24) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#deflate-inputs) | [Zlib.Deflate.Universal.deflate_copy_safety](../ZlibF/Proof/public-deflate-copy.lean#L85) | — |
| <a id="target-zlibf-spec-public-goal-deflate-refusal"></a>[deflate_refusal](../ZlibF/Spec/Safety/Refusals.lean#L50) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.RefusalProof.Deflate.deflate_refusal](../ZlibF/Proof/public-stream-refusal.lean#L89) | — |
| <a id="target-zlibf-spec-public-goal-deflate-safety"></a>[deflate_safety](../ZlibF/Spec/Safety/Streams.lean#L149) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflate_safety](../ZlibF/Proof/public-stream-call-safety.lean#L111) | — |
| <a id="target-zlibf-spec-public-goal-deflatesetdictionary-safety"></a>[deflateSetDictionary_safety](../ZlibF/Spec/Safety/Streams.lean#L160) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflateSetDictionary_safety](../ZlibF/Proof/public-stream-call-safety.lean#L116) | — |
| <a id="target-zlibf-spec-public-goal-deflategetdictionary-safety"></a>[deflateGetDictionary_safety](../ZlibF/Spec/Safety/Streams.lean#L171) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflateGetDictionary_safety](../ZlibF/Proof/public-stream-call-safety.lean#L121) | — |
| <a id="target-zlibf-spec-public-goal-deflatereset-safety"></a>[deflateReset_safety](../ZlibF/Spec/Safety/Streams.lean#L183) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflateReset_safety](../ZlibF/Proof/public-stream-call-safety.lean#L126) | — |
| <a id="target-zlibf-spec-public-goal-deflateparams-safety"></a>[deflateParams_safety](../ZlibF/Spec/Safety/Streams.lean#L193) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflateParams_safety](../ZlibF/Proof/public-stream-call-safety.lean#L132) | — |
| <a id="target-zlibf-spec-public-goal-deflatetune-safety"></a>[deflateTune_safety](../ZlibF/Spec/Safety/Streams.lean#L204) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflateTune_safety](../ZlibF/Proof/public-stream-call-safety.lean#L137) | — |
| <a id="target-zlibf-spec-public-goal-deflatebound-safety"></a>[deflateBound_safety](../ZlibF/Spec/Safety/Streams.lean#L217) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflateBound_safety](../ZlibF/Proof/public-stream-call-safety.lean#L142) | — |
| <a id="target-zlibf-spec-public-goal-deflatebound-z-safety"></a>[deflateBound_z_safety](../ZlibF/Spec/Safety/Streams.lean#L229) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflateBound_z_safety](../ZlibF/Proof/public-stream-call-safety.lean#L147) | — |
| <a id="target-zlibf-spec-public-goal-deflatepending-safety"></a>[deflatePending_safety](../ZlibF/Spec/Safety/Streams.lean#L240) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflatePending_safety](../ZlibF/Proof/public-stream-call-safety.lean#L152) | — |
| <a id="target-zlibf-spec-public-goal-deflateused-safety"></a>[deflateUsed_safety](../ZlibF/Spec/Safety/Streams.lean#L252) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflateUsed_safety](../ZlibF/Proof/public-stream-call-safety.lean#L157) | — |
| <a id="target-zlibf-spec-public-goal-deflateprime-safety"></a>[deflatePrime_safety](../ZlibF/Spec/Safety/Streams.lean#L263) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflatePrime_safety](../ZlibF/Proof/public-stream-call-safety.lean#L162) | — |
| <a id="target-zlibf-spec-public-goal-deflatesetheader-safety"></a>[deflateSetHeader_safety](../ZlibF/Spec/Safety/Streams.lean#L274) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflateSetHeader_safety](../ZlibF/Proof/public-stream-call-safety.lean#L167) | — |
| <a id="target-zlibf-spec-public-goal-deflateend-safety"></a>[deflateEnd_safety](../ZlibF/Spec/Safety/Streams.lean#L300) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflateEnd_safety](../ZlibF/Proof/public-stream-call-safety.lean#L183) | — |
| <a id="target-zlibf-spec-public-goal-deflateinit2-safety"></a>[deflateInit2__safety](../ZlibF/Spec/Safety/Initialisation.lean#L70) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.InitSafetyProof.deflateInit2__safety](../ZlibF/Proof/public-init-safety.lean#L175) | — |
| <a id="target-zlibf-spec-public-goal-deflateinit-safety"></a>[deflateInit__safety](../ZlibF/Spec/Safety/Initialisation.lean#L78) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.InitSafetyProof.deflateInit__safety](../ZlibF/Proof/public-init-safety.lean#L195) | — |

<a id="group-back"></a>

## 回调解码

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-inflatebackinit"></a>[inflateBackInit_](../ZlibF/Spec/Public/Back.lean#L22) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-back.md#inflatebackinit_); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.InflateBackInitProof.back_init_public](../ZlibF/Proof/public-infback-init.lean#L136) | — |
| <a id="target-zlibf-spec-public-goal-inflateback"></a>[inflateBack](../ZlibF/Spec/Public/Back.lean#L118) | 未证明 / 未证明 | [契约](../docs/spec/api/inflate-back.md#inflateback); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：表、窗口与回调](progress.md#readiness-inflateback) |
| <a id="target-zlibf-spec-public-goal-inflatebackend"></a>[inflateBackEnd](../ZlibF/Spec/Public/Back.lean#L145) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-back.md#inflatebackend); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.InflateBackEndProof.back_end_public](../ZlibF/Proof/public-infback-end.lean#L21) | — |
| <a id="target-zlibf-spec-public-goal-inflateback-safety"></a>[inflateBack_safety](../ZlibF/Spec/Safety/Back.lean#L46) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.BackSafetyProof.inflateBack_safety](../ZlibF/Proof/public-back-safety.lean#L24) | — |
| <a id="target-zlibf-spec-public-goal-inflatebackend-safety"></a>[inflateBackEnd_safety](../ZlibF/Spec/Safety/Back.lean#L72) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.BackSafetyProof.inflateBackEnd_safety](../ZlibF/Proof/public-back-safety.lean#L32) | — |
| <a id="target-zlibf-spec-public-goal-inflatebackinit-safety"></a>[inflateBackInit__safety](../ZlibF/Spec/Safety/Back.lean#L30) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.BackSafetyProof.inflateBackInit__safety](../ZlibF/Proof/public-back-safety.lean#L47) | — |

<a id="group-gzip"></a>

## gzip 文件

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-gzclose-r"></a>[gzclose_r](../ZlibF/Spec/Public/GzClose.lean#L35) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzclose_r); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：资源归属](progress.md#readiness-gzclose-r) |
| <a id="target-zlibf-spec-public-goal-gzclose-w"></a>[gzclose_w](../ZlibF/Spec/Public/GzClose.lean#L40) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzclose_w); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：交付与清理](progress.md#readiness-gzclose-w) |
| <a id="target-zlibf-spec-public-goal-gzclose"></a>[gzclose](../ZlibF/Spec/Public/GzClose.lean#L44) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzclose); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：交付与清理](progress.md#readiness-gzclose-w) |
| <a id="target-zlibf-spec-public-goal-gzbuffer"></a>[gzbuffer](../ZlibF/Spec/Public/GzControl.lean#L12) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/gz-file.md#gzbuffer); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.gzbuffer_public](../ZlibF/Proof/public-gzbuffer.lean#L50) | — |
| <a id="target-zlibf-spec-public-goal-gzeof"></a>[gzeof](../ZlibF/Spec/Public/GzControl.lean#L22) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/gz-file.md#gzeof); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.gzeof_public](../ZlibF/Proof/public-gzeof.lean#L19) | — |
| <a id="target-zlibf-spec-public-goal-gztell64"></a>[gztell64](../ZlibF/Spec/Public/GzControl.lean#L36) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gztell64); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：位置约束](progress.md#readiness-gztell64) |
| <a id="target-zlibf-spec-public-goal-gztell"></a>[gztell](../ZlibF/Spec/Public/GzControl.lean#L39) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gztell); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：位置约束](progress.md#readiness-gztell64) |
| <a id="target-zlibf-spec-public-goal-gzoffset64"></a>[gzoffset64](../ZlibF/Spec/Public/GzControl.lean#L53) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/gz-file.md#gzoffset64); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.OffsetProof.gzoffset64_public_goal](../ZlibF/Proof/public-gz-offset.lean#L232) | — |
| <a id="target-zlibf-spec-public-goal-gzoffset"></a>[gzoffset](../ZlibF/Spec/Public/GzControl.lean#L56) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/gz-file.md#gzoffset); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.OffsetProof.gzoffset_public_goal](../ZlibF/Proof/public-gz-offset.lean#L245) | — |
| <a id="target-zlibf-spec-public-goal-gzerror"></a>[gzerror](../ZlibF/Spec/Public/GzControl.lean#L63) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/gz-file.md#gzerror); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzErrorProof.gzerror](../ZlibF/Proof/public-gz-error.lean#L207) | — |
| <a id="target-zlibf-spec-public-goal-gzclearerr"></a>[gzclearerr](../ZlibF/Spec/Public/GzControl.lean#L74) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/gz-file.md#gzclearerr); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.gzclearerr](../ZlibF/Proof/gzlib.c.public-clearerr.lean#L29) | — |
| <a id="target-zlibf-spec-public-goal-gzrewind"></a>[gzrewind](../ZlibF/Spec/Public/GzControl.lean#L91) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/gz-file.md#gzrewind); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzRewindProof.rewind_public](../ZlibF/Proof/public-gz-rewind.lean#L76) | — |
| <a id="target-zlibf-spec-public-goal-gzseek64"></a>[gzseek64](../ZlibF/Spec/Public/GzControl.lean#L116) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzseek64); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：定位与状态序列](progress.md#readiness-gzseek64) |
| <a id="target-zlibf-spec-public-goal-gzseek"></a>[gzseek](../ZlibF/Spec/Public/GzControl.lean#L119) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzseek); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：定位与状态序列](progress.md#readiness-gzseek64) |
| <a id="target-zlibf-spec-public-goal-gzopen"></a>[gzopen](../ZlibF/Spec/Public/GzOpen.lean#L65) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzopen); [输入范围](spec/input-configurations.md#entry-inputs) | — | [开始：打开与清理](progress.md#readiness-gzopen) |
| <a id="target-zlibf-spec-public-goal-gzopen64"></a>[gzopen64](../ZlibF/Spec/Public/GzOpen.lean#L70) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzopen64); [输入范围](spec/input-configurations.md#entry-inputs) | — | [开始：打开与清理](progress.md#readiness-gzopen) |
| <a id="target-zlibf-spec-public-goal-gzdopen"></a>[gzdopen](../ZlibF/Spec/Public/GzOpen.lean#L75) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/gz-file.md#gzdopen); [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Gzlib.Proofs.gzdopen_complete](../ZlibF/Proof/gzlib.c.dopen-complete.lean#L28) | — |
| <a id="target-zlibf-spec-public-goal-gzread"></a>[gzread](../ZlibF/Spec/Public/GzRead.lean#L22) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzread); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：读取路径证明](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzfread"></a>[gzfread](../ZlibF/Spec/Public/GzRead.lean#L37) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzfread); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：读取路径证明](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzgetc"></a>[gzgetc](../ZlibF/Spec/Public/GzRead.lean#L58) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzgetc); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：读取路径证明](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzgetc"></a>[gzgetc_](../ZlibF/Spec/Public/GzRead.lean#L61) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzgetc_); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：读取路径证明](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzungetc"></a>[gzungetc](../ZlibF/Spec/Public/GzRead.lean#L66) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzungetc); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：读取路径证明](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzgets"></a>[gzgets](../ZlibF/Spec/Public/GzRead.lean#L80) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzgets); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：读取路径证明](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzdirect"></a>[gzdirect](../ZlibF/Spec/Public/GzRead.lean#L103) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzdirect); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：读取路径证明](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzwrite"></a>[gzwrite](../ZlibF/Spec/Public/GzWrite.lean#L28) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzwrite); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：写入路径证明](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzfwrite"></a>[gzfwrite](../ZlibF/Spec/Public/GzWrite.lean#L43) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzfwrite); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：写入路径证明](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzputc"></a>[gzputc](../ZlibF/Spec/Public/GzWrite.lean#L59) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzputc); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：写入路径证明](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzputs"></a>[gzputs](../ZlibF/Spec/Public/GzWrite.lean#L71) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzputs); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：写入路径证明](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzvprintf"></a>[gzvprintf](../ZlibF/Spec/Public/GzWrite.lean#L108) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzvprintf); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：写入路径证明](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzprintf"></a>[gzprintf](../ZlibF/Spec/Public/GzWrite.lean#L112) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzprintf); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：写入路径证明](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzflush"></a>[gzflush](../ZlibF/Spec/Public/GzWrite.lean#L117) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzflush); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：写入路径证明](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzsetparams"></a>[gzsetparams](../ZlibF/Spec/Public/GzWrite.lean#L134) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzsetparams); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：写入路径证明](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gz-sequence-safety"></a>[gz_sequence_safety](../ZlibF/Spec/Public/GzSafety.lean#L144) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.gz_sequence_safety_public](../ZlibF/Proof/public-gz-sequence-safety.lean#L25) | — |
| <a id="target-zlibf-spec-public-goal-gz-refusal"></a>[gz_refusal](../ZlibF/Spec/Public/GzRefusal.lean#L39) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzRefusalProof.gz_refusal](../ZlibF/Proof/public-gz-refusal.lean#L17) | — |
| <a id="target-zlibf-spec-public-goal-gz-sequence-nonvacuity"></a>[gz_sequence_nonvacuity](../ZlibF/Spec/Public/GzSafety.lean#L179) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.GzNonvacuity.gz_sequence_nonvacuity_public](../ZlibF/Proof/public-gz-sequence-nonvacuity.lean#L268) | — |
| <a id="target-zlibf-spec-public-goal-gzbuffer-safety"></a>[gzbuffer_safety](../ZlibF/Spec/Safety/GzCalls.lean#L45) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzbuffer_safety](../ZlibF/Proof/public-gz-call-safety.lean#L26) | — |
| <a id="target-zlibf-spec-public-goal-gzclearerr-safety"></a>[gzclearerr_safety](../ZlibF/Spec/Safety/GzCalls.lean#L52) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzclearerr_safety](../ZlibF/Proof/public-gz-call-safety.lean#L30) | — |
| <a id="target-zlibf-spec-public-goal-gzclose-safety"></a>[gzclose_safety](../ZlibF/Spec/Safety/GzCalls.lean#L252) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzclose_safety](../ZlibF/Proof/public-gz-call-safety.lean#L130) | — |
| <a id="target-zlibf-spec-public-goal-gzclose-r-safety"></a>[gzclose_r_safety](../ZlibF/Spec/Safety/GzCalls.lean#L260) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzclose_r_safety](../ZlibF/Proof/public-gz-call-safety.lean#L134) | — |
| <a id="target-zlibf-spec-public-goal-gzclose-w-safety"></a>[gzclose_w_safety](../ZlibF/Spec/Safety/GzCalls.lean#L268) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzclose_w_safety](../ZlibF/Proof/public-gz-call-safety.lean#L138) | — |
| <a id="target-zlibf-spec-public-goal-gzdirect-safety"></a>[gzdirect_safety](../ZlibF/Spec/Safety/GzCalls.lean#L59) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzdirect_safety](../ZlibF/Proof/public-gz-call-safety.lean#L34) | — |
| <a id="target-zlibf-spec-public-goal-gzdopen-safety"></a>[gzdopen_safety](../ZlibF/Spec/Safety/GzCalls.lean#L286) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzdopen_safety](../ZlibF/Proof/public-gz-call-safety.lean#L147) | — |
| <a id="target-zlibf-spec-public-goal-gzeof-safety"></a>[gzeof_safety](../ZlibF/Spec/Safety/GzCalls.lean#L66) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzeof_safety](../ZlibF/Proof/public-gz-call-safety.lean#L38) | — |
| <a id="target-zlibf-spec-public-goal-gzerror-safety"></a>[gzerror_safety](../ZlibF/Spec/Safety/GzCalls.lean#L239) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzerror_safety](../ZlibF/Proof/public-gz-call-safety.lean#L126) | — |
| <a id="target-zlibf-spec-public-goal-gzflush-safety"></a>[gzflush_safety](../ZlibF/Spec/Safety/GzCalls.lean#L73) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzflush_safety](../ZlibF/Proof/public-gz-call-safety.lean#L42) | — |
| <a id="target-zlibf-spec-public-goal-gzfread-safety"></a>[gzfread_safety](../ZlibF/Spec/Safety/GzCalls.lean#L81) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzfread_safety](../ZlibF/Proof/public-gz-call-safety.lean#L46) | — |
| <a id="target-zlibf-spec-public-goal-gzfwrite-safety"></a>[gzfwrite_safety](../ZlibF/Spec/Safety/GzCalls.lean#L89) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzfwrite_safety](../ZlibF/Proof/public-gz-call-safety.lean#L50) | — |
| <a id="target-zlibf-spec-public-goal-gzgetc-safety"></a>[gzgetc_safety](../ZlibF/Spec/Safety/GzCalls.lean#L224) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzgetc_safety](../ZlibF/Proof/public-gz-call-safety.lean#L122) | — |
| <a id="target-zlibf-spec-public-goal-gzgetc-safety"></a>[gzgetc__safety](../ZlibF/Spec/Safety/GzCalls.lean#L97) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzgetc__safety](../ZlibF/Proof/public-gz-call-safety.lean#L54) | — |
| <a id="target-zlibf-spec-public-goal-gzgets-safety"></a>[gzgets_safety](../ZlibF/Spec/Safety/GzCalls.lean#L104) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzgets_safety](../ZlibF/Proof/public-gz-call-safety.lean#L58) | — |
| <a id="target-zlibf-spec-public-goal-gzoffset-safety"></a>[gzoffset_safety](../ZlibF/Spec/Safety/GzCalls.lean#L111) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzoffset_safety](../ZlibF/Proof/public-gz-call-safety.lean#L62) | — |
| <a id="target-zlibf-spec-public-goal-gzoffset64-safety"></a>[gzoffset64_safety](../ZlibF/Spec/Safety/GzCalls.lean#L118) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzoffset64_safety](../ZlibF/Proof/public-gz-call-safety.lean#L66) | — |
| <a id="target-zlibf-spec-public-goal-gzopen-safety"></a>[gzopen_safety](../ZlibF/Spec/Safety/GzCalls.lean#L276) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzopen_safety](../ZlibF/Proof/public-gz-call-safety.lean#L141) | — |
| <a id="target-zlibf-spec-public-goal-gzopen64-safety"></a>[gzopen64_safety](../ZlibF/Spec/Safety/GzCalls.lean#L281) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzopen64_safety](../ZlibF/Proof/public-gz-call-safety.lean#L144) | — |
| <a id="target-zlibf-spec-public-goal-gzprintf-safety"></a>[gzprintf_safety](../ZlibF/Spec/Safety/GzCalls.lean#L125) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzprintf_safety](../ZlibF/Proof/public-gz-call-safety.lean#L70) | — |
| <a id="target-zlibf-spec-public-goal-gzvprintf-safety"></a>[gzvprintf_safety](../ZlibF/Spec/Safety/GzCalls.lean#L134) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzvprintf_safety](../ZlibF/Proof/public-gz-call-safety.lean#L74) | — |
| <a id="target-zlibf-spec-public-goal-gzputc-safety"></a>[gzputc_safety](../ZlibF/Spec/Safety/GzCalls.lean#L142) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzputc_safety](../ZlibF/Proof/public-gz-call-safety.lean#L78) | — |
| <a id="target-zlibf-spec-public-goal-gzputs-safety"></a>[gzputs_safety](../ZlibF/Spec/Safety/GzCalls.lean#L149) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzputs_safety](../ZlibF/Proof/public-gz-call-safety.lean#L82) | — |
| <a id="target-zlibf-spec-public-goal-gzread-safety"></a>[gzread_safety](../ZlibF/Spec/Safety/GzCalls.lean#L156) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzread_safety](../ZlibF/Proof/public-gz-call-safety.lean#L86) | — |
| <a id="target-zlibf-spec-public-goal-gzrewind-safety"></a>[gzrewind_safety](../ZlibF/Spec/Safety/GzCalls.lean#L163) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzrewind_safety](../ZlibF/Proof/public-gz-call-safety.lean#L90) | — |
| <a id="target-zlibf-spec-public-goal-gzseek-safety"></a>[gzseek_safety](../ZlibF/Spec/Safety/GzCalls.lean#L170) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzseek_safety](../ZlibF/Proof/public-gz-call-safety.lean#L94) | — |
| <a id="target-zlibf-spec-public-goal-gzseek64-safety"></a>[gzseek64_safety](../ZlibF/Spec/Safety/GzCalls.lean#L178) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzseek64_safety](../ZlibF/Proof/public-gz-call-safety.lean#L98) | — |
| <a id="target-zlibf-spec-public-goal-gzsetparams-safety"></a>[gzsetparams_safety](../ZlibF/Spec/Safety/GzCalls.lean#L186) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzsetparams_safety](../ZlibF/Proof/public-gz-call-safety.lean#L102) | — |
| <a id="target-zlibf-spec-public-goal-gztell-safety"></a>[gztell_safety](../ZlibF/Spec/Safety/GzCalls.lean#L194) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gztell_safety](../ZlibF/Proof/public-gz-call-safety.lean#L106) | — |
| <a id="target-zlibf-spec-public-goal-gztell64-safety"></a>[gztell64_safety](../ZlibF/Spec/Safety/GzCalls.lean#L201) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gztell64_safety](../ZlibF/Proof/public-gz-call-safety.lean#L110) | — |
| <a id="target-zlibf-spec-public-goal-gzungetc-safety"></a>[gzungetc_safety](../ZlibF/Spec/Safety/GzCalls.lean#L208) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzungetc_safety](../ZlibF/Proof/public-gz-call-safety.lean#L114) | — |
| <a id="target-zlibf-spec-public-goal-gzwrite-safety"></a>[gzwrite_safety](../ZlibF/Spec/Safety/GzCalls.lean#L215) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzwrite_safety](../ZlibF/Proof/public-gz-call-safety.lean#L118) | — |

<a id="group-buffers"></a>

## 完整缓冲区操作

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-compress2-z"></a>[compress2_z](../ZlibF/Spec/Functional/Utilities.lean#L43) | 未证明 / 未证明 | [契约](../docs/spec/api/utility.md#compress2_z); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：压缩器执行](progress.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-compress2"></a>[compress2](../ZlibF/Spec/Functional/Utilities.lean#L48) | 未证明 / 未证明 | [契约](../docs/spec/api/utility.md#compress2); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：压缩器执行](progress.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-compress-z"></a>[compress_z](../ZlibF/Spec/Functional/Utilities.lean#L55) | 未证明 / 未证明 | [契约](../docs/spec/api/utility.md#compress_z); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：压缩器执行](progress.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-compress"></a>[compress](../ZlibF/Spec/Functional/Utilities.lean#L60) | 未证明 / 未证明 | [契约](../docs/spec/api/utility.md#compress); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：压缩器执行](progress.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress2-z"></a>[uncompress2_z](../ZlibF/Spec/Functional/Utilities.lean#L101) | 未证明 / 未证明 | [契约](../docs/spec/api/utility.md#uncompress2_z); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：解码器执行](progress.md#readiness-uncompress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress2"></a>[uncompress2](../ZlibF/Spec/Functional/Utilities.lean#L105) | 未证明 / 未证明 | [契约](../docs/spec/api/utility.md#uncompress2); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：解码器执行](progress.md#readiness-uncompress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress-z"></a>[uncompress_z](../ZlibF/Spec/Functional/Utilities.lean#L133) | 未证明 / 未证明 | [契约](../docs/spec/api/utility.md#uncompress_z); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：解码器执行](progress.md#readiness-uncompress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress"></a>[uncompress](../ZlibF/Spec/Functional/Utilities.lean#L137) | 未证明 / 未证明 | [契约](../docs/spec/api/utility.md#uncompress); [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：解码器执行](progress.md#readiness-uncompress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress2-z-safe"></a>[uncompress2_z_safe](../ZlibF/Spec/Safety/Utilities.lean#L34) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.Uncompress.uncompress2_z_safe](../ZlibF/Proof/public-uncompress-safe.lean#L300) | — |
| <a id="target-zlibf-spec-public-goal-uncompress2-safe"></a>[uncompress2_safe](../ZlibF/Spec/Safety/Utilities.lean#L37) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.Uncompress.uncompress2_safe](../ZlibF/Proof/public-uncompress-safe.lean#L304) | — |
| <a id="target-zlibf-spec-public-goal-uncompress-z-safe"></a>[uncompress_z_safe](../ZlibF/Spec/Safety/Utilities.lean#L40) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.Uncompress.uncompress_z_safe](../ZlibF/Proof/public-uncompress-safe.lean#L308) | — |
| <a id="target-zlibf-spec-public-goal-uncompress-safe"></a>[uncompress_safe](../ZlibF/Spec/Safety/Utilities.lean#L43) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.Uncompress.uncompress_safe](../ZlibF/Proof/public-uncompress-safe.lean#L314) | — |
| <a id="target-zlibf-spec-public-goal-compress2-z-safety"></a>[compress2_z_safety](../ZlibF/Spec/Safety/Utilities.lean#L14) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.Compress.compress2_z_safety](../ZlibF/Proof/public-compress-safe-mid.lean#L116) | — |
| <a id="target-zlibf-spec-public-goal-compress2-safety"></a>[compress2_safety](../ZlibF/Spec/Safety/Utilities.lean#L18) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.Compress.compress2_safety](../ZlibF/Proof/public-compress-safe-mid.lean#L124) | — |
| <a id="target-zlibf-spec-public-goal-compress-z-safety"></a>[compress_z_safety](../ZlibF/Spec/Safety/Utilities.lean#L24) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.Compress.compress_z_safety](../ZlibF/Proof/public-compress-safe-mid.lean#L120) | — |
| <a id="target-zlibf-spec-public-goal-compress-safety"></a>[compress_safety](../ZlibF/Spec/Safety/Utilities.lean#L28) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.Compress.compress_safety](../ZlibF/Proof/public-compress-safe-mid.lean#L128) | — |
| <a id="target-zlibf-spec-public-goal-zlibversion-safety"></a>[zlibVersion_safety](../ZlibF/Spec/Safety/Queries.lean#L18) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.zlibVersion_safety](../ZlibF/Proof/public-stateless-safety.lean#L75) | — |
| <a id="target-zlibf-spec-public-goal-zlibcompileflags-safety"></a>[zlibCompileFlags_safety](../ZlibF/Spec/Safety/Queries.lean#L23) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.zlibCompileFlags_safety](../ZlibF/Proof/public-stateless-safety.lean#L80) | — |

<a id="group-models"></a>

## 格式与 API 模型

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-api-goal-format-deterministic"></a>[format_deterministic](../ZlibF/Spec/Functional/Api/Goals.lean#L42) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.format_deterministic](../ZlibF/Proof/Format/Api.lean#L51) | — |
| <a id="target-zlibf-spec-api-goal-format-prefix-free"></a>[format_prefix_free](../ZlibF/Spec/Functional/Api/Goals.lean#L47) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.format_prefix_free](../ZlibF/Proof/Format/Api.lean#L56) | — |
| <a id="target-zlibf-spec-api-goal-inflate-decodes"></a>[inflate_decodes](../ZlibF/Spec/Functional/Api/Goals.lean#L58) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.inflate_decodes](../ZlibF/Proof/Api/Inflate.lean#L346) | — |
| <a id="target-zlibf-spec-api-goal-inflate-completes"></a>[inflate_completes](../ZlibF/Spec/Functional/Api/Goals.lean#L69) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.inflate_completes](../ZlibF/Proof/Api/Inflate.lean#L353) | — |
| <a id="target-zlibf-spec-api-goal-inflate-rejects-invalid"></a>[inflate_rejects_invalid](../ZlibF/Spec/Functional/Api/Goals.lean#L84) | 未证明 / 未证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | — | 前置义务尚未审查 |
| <a id="target-zlibf-spec-api-goal-deflate-valid"></a>[deflate_valid](../ZlibF/Spec/Functional/Api/Goals.lean#L99) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.deflate_valid](../ZlibF/Proof/Api/Deflate.lean#L181) | — |
| <a id="target-zlibf-spec-api-goal-deflate-completes"></a>[deflate_completes](../ZlibF/Spec/Functional/Api/Goals.lean#L106) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.deflate_completes](../ZlibF/Proof/Api/DeflateBounds.lean#L164) | — |
| <a id="target-zlibf-spec-api-goal-deflate-full-flush-resync"></a>[deflate_full_flush_resync](../ZlibF/Spec/Functional/Api/Goals.lean#L116) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.deflate_full_flush_resync](../ZlibF/Proof/Api/DeflateFlush.lean#L169) | — |
| <a id="target-zlibf-spec-api-goal-roundtrip"></a>[roundtrip](../ZlibF/Spec/Functional/Api/Goals.lean#L134) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.roundtrip](../ZlibF/Proof/Api/GzipRoundtrip.lean#L177) | — |
| <a id="target-zlibf-spec-api-goal-roundtrip-completes"></a>[roundtrip_completes](../ZlibF/Spec/Functional/Api/Goals.lean#L143) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.roundtrip_completes](../ZlibF/Proof/Api/GzipRoundtrip.lean#L186) | — |
| <a id="target-zlibf-spec-api-goal-dict-roundtrip"></a>[dict_roundtrip](../ZlibF/Spec/Functional/Api/Goals.lean#L162) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.dict_roundtrip](../ZlibF/Proof/Api/DictionaryRoundtrip.lean#L121) | — |
| <a id="target-zlibf-spec-api-goal-header-roundtrip"></a>[header_roundtrip](../ZlibF/Spec/Functional/Api/Goals.lean#L180) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.header_roundtrip](../ZlibF/Proof/Api/HeaderRoundtrip.lean#L89) | — |
| <a id="target-zlibf-spec-api-goal-deflate-bound-adequate"></a>[deflate_bound_adequate](../ZlibF/Spec/Functional/Api/Goals.lean#L189) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.deflate_bound_adequate](../ZlibF/Proof/Api/DeflateBounds.lean#L103) | — |
| <a id="target-zlibf-spec-api-goal-compress-bound-adequate"></a>[compress_bound_adequate](../ZlibF/Spec/Functional/Api/Goals.lean#L196) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress_bound_adequate](../ZlibF/Proof/Api/Compress.lean#L8) | — |
| <a id="target-zlibf-spec-api-goal-compress-roundtrip"></a>[compress_roundtrip](../ZlibF/Spec/Functional/Api/Goals.lean#L203) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress_roundtrip](../ZlibF/Proof/Api/CompressRoundtrip.lean#L32) | — |
| <a id="target-zlibf-spec-api-goal-gz-roundtrip"></a>[gz_roundtrip](../ZlibF/Spec/Functional/Api/Goals.lean#L214) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.gz_roundtrip](../ZlibF/Proof/Api/GzRoundtrip.lean#L15) | — |
| <a id="target-zlibf-spec-api-goal-gz-seek-read"></a>[gz_seek_read](../ZlibF/Spec/Functional/Api/Goals.lean#L221) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.gz_seek_read](../ZlibF/Proof/Api/GzSeekRead.lean#L15) | — |
| <a id="target-zlibf-spec-api-goal-compress-bound-value"></a>[compress_bound_value](../ZlibF/Spec/Functional/Api/Concrete.lean#L57) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress_bound_value](../ZlibF/Proof/Api/Concrete.lean#L57) | — |
| <a id="target-zlibf-spec-api-goal-compress2-z-first-alloc-failure"></a>[compress2_z_first_alloc_failure](../ZlibF/Spec/Functional/Api/Concrete.lean#L67) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress2_z_first_alloc_failure](../ZlibF/Proof/Api/CompressFailure.lean#L29) | — |
| <a id="target-zlibf-spec-api-goal-inflate-deferred-distance"></a>[inflate_deferred_distance](../ZlibF/Spec/Functional/Api/Inflate.lean#L267) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.inflate_deferred_distance](../ZlibF/Proof/Api/InflateCausality.lean#L244) | — |

<a id="group-lifecycle"></a>

## 生命周期与调用序列

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-inflate-sequence"></a>[inflate_sequence](../ZlibF/Spec/Functional/Sequences.lean#L172) | 未证明 / 未证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#inflate-inputs) | — | [需要：执行与格式](progress.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-deflate-sequence"></a>[deflate_sequence](../ZlibF/Spec/Functional/Sequences.lean#L192) | 未证明 / 未证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#deflate-inputs) | — | [需要：执行与格式](progress.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-inflate-back-sequence"></a>[inflate_back_sequence](../ZlibF/Spec/Public/Sequences.lean#L175) | 未证明 / 未证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：执行与格式](progress.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-gz-sequence"></a>[gz_sequence](../ZlibF/Spec/Public/Sequences.lean#L225) | 未证明 / 未证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | — | [需要：执行与格式](progress.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-inflate-initialisation-domain"></a>[inflate_initialisation_domain](../ZlibF/Spec/Safety/Domains.lean#L15) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.InflateInit.inflate_initialisation_domain_public](../ZlibF/Proof/public-inflate-init.lean#L266) | — |
| <a id="target-zlibf-spec-public-goal-deflate-initialisation-domain"></a>[deflate_initialisation_domain](../ZlibF/Spec/Safety/Domains.lean#L28) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.DeflateInitDomain.deflate_initialisation_domain_public](../ZlibF/Proof/public-deflate-init-domain.lean#L39) | — |
| <a id="target-zlibf-spec-public-goal-inflate-back-initialisation-domain"></a>[inflate_back_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L24) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.InflateBackInitProof.back_init_domain_public](../ZlibF/Proof/public-infback-init.lean#L231) | — |
| <a id="target-zlibf-spec-public-goal-gz-initialisation-domain"></a>[gz_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L50) | 未证明 / 不在计划内 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | — | [不在计划内](#scope) |

<a id="group-internal"></a>

## 内部证明义务

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlib-crc32-spec-byteviews-goal-crc32-z-all-byte-views"></a>[crc32_z_all_byte_views](../ZlibF/Spec/Crc32ByteViews.lean#L17) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Crc32.Proofs.crc32_z_all_byte_views](../ZlibF/Proof/crc32.c.views.lean#L567) | — |
| <a id="target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views"></a>[crc32_all_byte_views](../ZlibF/Spec/Crc32ByteViews.lean#L28) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Crc32.Proofs.crc32_all_byte_views](../ZlibF/Proof/crc32.c.views.lean#L573) | — |
| <a id="target-zlibf-spec-token-goal-rejected-has-no-symbols"></a>[rejected_has_no_symbols](../ZlibF/Spec/Functional/Format/Token.lean#L84) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Token.rejected_has_no_symbols](../ZlibF/Proof/Format/Token.lean#L49) | — |
| <a id="target-zlibf-spec-token-goal-step-composes-symbols"></a>[step_composes_symbols](../ZlibF/Spec/Functional/Format/Token.lean#L62) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Token.step_composes_symbols](../ZlibF/Proof/Format/Token.lean#L15) | — |
| <a id="target-zlibf-spec-token-goal-symbols-exposes-step"></a>[symbols_exposes_step](../ZlibF/Spec/Functional/Format/Token.lean#L73) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Token.symbols_exposes_step](../ZlibF/Proof/Format/Token.lean#L35) | — |

## 已观察到的证明依赖

左列是被复用的来源目标，右列是使用它的目标。右列目标的定理实际使用了左列目标的证明。

| 来源 | 目标 |
| --- | --- |
| [pointer_advance_preserves_low_bits](#target-c-byteaddress-spec-goal-pointer-advance-preserves-low-bits) | [first_aligned_offset](#target-c-byteaddress-spec-goal-first-aligned-offset) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [crc32](#target-zlibf-spec-public-goal-crc32) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [crc32_z_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-z-all-byte-views) | [crc32_z](#target-zlibf-spec-public-goal-crc32-z) |
| [actual_body_preserves_origin](#target-zlib-inffast-spec-bodyorigin-goal-actual-body-preserves-origin) | [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) |
| [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) | [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) |
| [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [actual_distance_block_preserves_origin](#target-zlib-inffast-spec-distanceorigin-goal-actual-distance-block-preserves-origin) | [actual_body_preserves_origin](#target-zlib-inffast-spec-bodyorigin-goal-actual-body-preserves-origin) |
| [actual_distance_refines_lz77](#target-zlib-inffast-spec-distanceresult-goal-actual-distance-refines-lz77) | [actual_body_refines_token](#target-zlib-inffast-spec-bodytoken-goal-actual-body-refines-token) |
| [distance_lookup_matches_format](#target-zlib-inffast-spec-distancesemantics-goal-distance-lookup-matches-format) | [actual_distance_refines_lz77](#target-zlib-inffast-spec-distanceresult-goal-actual-distance-refines-lz77) |
| [fast_safe](#target-zlib-inffast-spec-goal-fast-safe) | [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) |
| [step_safe](#target-zlib-inffast-spec-goal-step-safe) | [actual_body_refines_token](#target-zlib-inffast-spec-bodytoken-goal-actual-body-refines-token) |
| [step_safe](#target-zlib-inffast-spec-goal-step-safe) | [actual_body_retains_selected_length](#target-zlib-inffast-spec-lengthtrace-goal-actual-body-retains-selected-length) |
| [length_lookup_matches_format](#target-zlib-inffast-spec-lengthsemantics-goal-length-lookup-matches-format) | [actual_body_refines_token](#target-zlib-inffast-spec-bodytoken-goal-actual-body-refines-token) |
| [actual_copy_match_refines_lz77](#target-zlib-inffast-spec-matchhistory-goal-actual-copy-match-refines-lz77) | [actual_distance_refines_lz77](#target-zlib-inffast-spec-distanceresult-goal-actual-distance-refines-lz77) |
| [match_array_refines_lz77](#target-zlib-inffast-spec-matchhistory-goal-match-array-refines-lz77) | [actual_copy_match_refines_lz77](#target-zlib-inffast-spec-matchhistory-goal-actual-copy-match-refines-lz77) |
| [actual_drop_preserves_origin](#target-zlib-inffast-spec-origin-goal-actual-drop-preserves-origin) | [actual_body_preserves_origin](#target-zlib-inffast-spec-bodyorigin-goal-actual-body-preserves-origin) |
| [actual_rollback_preserves_origin](#target-zlib-inffast-spec-origin-goal-actual-rollback-preserves-origin) | [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) |
| [drop_preserves_origin](#target-zlib-inffast-spec-origin-goal-drop-preserves-origin) | [actual_distance_block_preserves_origin](#target-zlib-inffast-spec-distanceorigin-goal-actual-distance-block-preserves-origin) |
| [drop_preserves_origin](#target-zlib-inffast-spec-origin-goal-drop-preserves-origin) | [actual_drop_preserves_origin](#target-zlib-inffast-spec-origin-goal-actual-drop-preserves-origin) |
| [initial_origin](#target-zlib-inffast-spec-origin-goal-initial-origin) | [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) |
| [pull_preserves_origin](#target-zlib-inffast-spec-origin-goal-pull-preserves-origin) | [actual_body_preserves_origin](#target-zlib-inffast-spec-bodyorigin-goal-actual-body-preserves-origin) |
| [pull_preserves_origin](#target-zlib-inffast-spec-origin-goal-pull-preserves-origin) | [actual_distance_block_preserves_origin](#target-zlib-inffast-spec-distanceorigin-goal-actual-distance-block-preserves-origin) |
| [pull_preserves_origin](#target-zlib-inffast-spec-origin-goal-pull-preserves-origin) | [actual_pull_preserves_origin](#target-zlib-inffast-spec-origin-goal-actual-pull-preserves-origin) |
| [rollback_preserves_origin](#target-zlib-inffast-spec-origin-goal-rollback-preserves-origin) | [actual_rollback_preserves_origin](#target-zlib-inffast-spec-origin-goal-actual-rollback-preserves-origin) |
| [decode_table_classifies_input](#target-zlib-inftrees-spec-decoderejection-goal-decode-table-classifies-input) | [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) |
| [decode_table_matches_format](#target-zlib-inftrees-spec-decodesemantics-goal-decode-table-matches-format) | [decode_table_classifies_input](#target-zlib-inftrees-spec-decoderejection-goal-decode-table-classifies-input) |
| [short_decode_table_leaf_sound](#target-zlib-inftrees-spec-decodeshort-goal-short-decode-table-leaf-sound) | [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) |
| [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound) | [decode_table_classifies_input](#target-zlib-inftrees-spec-decoderejection-goal-decode-table-classifies-input) |
| [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound) | [short_decode_table_leaf_sound](#target-zlib-inftrees-spec-decodeshort-goal-short-decode-table-leaf-sound) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [query_stability_of_prefix](#target-zlib-inftrees-spec-decodetablestability-goal-query-stability-of-prefix) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [fast_leaf_flags_of_prefix](#target-zlib-inftrees-spec-fasttableflags-goal-fast-leaf-flags-of-prefix) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) | [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) |
| [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) | [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) |
| [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [constructor_establishes_query_stability](#target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [query_stability_of_prefix](#target-zlib-inftrees-spec-decodetablestability-goal-query-stability-of-prefix) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [short_rejected_leaf_stays_invalid](#target-zlib-inftrees-spec-decodetablestability-goal-short-rejected-leaf-stays-invalid) | [distance_lookup_matches_format](#target-zlib-inffast-spec-distancesemantics-goal-distance-lookup-matches-format) |
| [short_rejected_leaf_stays_invalid](#target-zlib-inftrees-spec-decodetablestability-goal-short-rejected-leaf-stays-invalid) | [length_lookup_matches_format](#target-zlib-inffast-spec-lengthsemantics-goal-length-lookup-matches-format) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe) | [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) |
| [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe) | [constructor_root_bits](#target-zlib-inftrees-spec-roottable-goal-constructor-root-bits) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits) | [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) |
| [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits) | [constructor_root_bits](#target-zlib-inftrees-spec-roottable-goal-constructor-root-bits) |
| [output_copy_refines_lz77](#target-zlibf-math-lz77copy-goal-output-copy-refines-lz77) | [match_array_refines_lz77](#target-zlib-inffast-spec-matchhistory-goal-match-array-refines-lz77) |
| [window_copy_refines_lz77](#target-zlibf-math-lz77copy-goal-window-copy-refines-lz77) | [match_array_refines_lz77](#target-zlib-inffast-spec-matchhistory-goal-match-array-refines-lz77) |
| [copy_back_compose](#target-zlibf-math-lz77history-goal-copy-back-compose) | [match_array_refines_lz77](#target-zlib-inffast-spec-matchhistory-goal-match-array-refines-lz77) |
| [retained_history_agrees](#target-zlibf-math-lz77history-goal-retained-history-agrees) | [roundtrip](#target-zlibf-spec-api-goal-roundtrip) |
| [retained_history_agrees](#target-zlibf-math-lz77history-goal-retained-history-agrees) | [roundtrip_completes](#target-zlibf-spec-api-goal-roundtrip-completes) |
| [deflate_valid](#target-zlibf-spec-api-goal-deflate-valid) | [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip) |
| [deflate_valid](#target-zlibf-spec-api-goal-deflate-valid) | [header_roundtrip](#target-zlibf-spec-api-goal-header-roundtrip) |
| [deflate_valid](#target-zlibf-spec-api-goal-deflate-valid) | [roundtrip](#target-zlibf-spec-api-goal-roundtrip) |
| [deflate_valid](#target-zlibf-spec-api-goal-deflate-valid) | [roundtrip_completes](#target-zlibf-spec-api-goal-roundtrip-completes) |
| [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes) | [roundtrip_completes](#target-zlibf-spec-api-goal-roundtrip-completes) |
| [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes) | [roundtrip](#target-zlibf-spec-api-goal-roundtrip) |
| [adler32](#target-zlibf-spec-public-goal-adler32) | [adler32_safety](#target-zlibf-spec-public-goal-adler32-safety) |
| [adler32_combine](#target-zlibf-spec-public-goal-adler32-combine) | [adler32_combine_safety](#target-zlibf-spec-public-goal-adler32-combine-safety) |
| [adler32_combine64](#target-zlibf-spec-public-goal-adler32-combine64) | [adler32_combine64_safety](#target-zlibf-spec-public-goal-adler32-combine64-safety) |
| [adler32_z](#target-zlibf-spec-public-goal-adler32-z) | [adler32](#target-zlibf-spec-public-goal-adler32) |
| [adler32_z](#target-zlibf-spec-public-goal-adler32-z) | [adler32_z_safety](#target-zlibf-spec-public-goal-adler32-z-safety) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [compress_safety](#target-zlibf-spec-public-goal-compress-safety) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [crc32_safety](#target-zlibf-spec-public-goal-crc32-safety) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [deflate](#target-zlibf-spec-public-goal-deflate) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [crc32_combine](#target-zlibf-spec-public-goal-crc32-combine) | [crc32_combine_safety](#target-zlibf-spec-public-goal-crc32-combine-safety) |
| [crc32_combine64](#target-zlibf-spec-public-goal-crc32-combine64) | [crc32_combine64_safety](#target-zlibf-spec-public-goal-crc32-combine64-safety) |
| [crc32_combine_gen](#target-zlibf-spec-public-goal-crc32-combine-gen) | [crc32_combine_gen_safety](#target-zlibf-spec-public-goal-crc32-combine-gen-safety) |
| [crc32_combine_gen](#target-zlibf-spec-public-goal-crc32-combine-gen) | [crc32_combine_op_safety](#target-zlibf-spec-public-goal-crc32-combine-op-safety) |
| [crc32_combine_gen64](#target-zlibf-spec-public-goal-crc32-combine-gen64) | [crc32_combine_gen64_safety](#target-zlibf-spec-public-goal-crc32-combine-gen64-safety) |
| [crc32_combine_gen64](#target-zlibf-spec-public-goal-crc32-combine-gen64) | [crc32_combine_op_safety](#target-zlibf-spec-public-goal-crc32-combine-op-safety) |
| [crc32_combine_op](#target-zlibf-spec-public-goal-crc32-combine-op) | [crc32_combine_op_safety](#target-zlibf-spec-public-goal-crc32-combine-op-safety) |
| [crc32_z](#target-zlibf-spec-public-goal-crc32-z) | [crc32_z_safety](#target-zlibf-spec-public-goal-crc32-z-safety) |
| [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy) | [deflateCopy_safety](#target-zlibf-spec-public-goal-deflatecopy-safety) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [compress_safety](#target-zlibf-spec-public-goal-compress-safety) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [deflateInit2__safety](#target-zlibf-spec-public-goal-deflateinit2-safety) |
| [deflateInit2__safety](#target-zlibf-spec-public-goal-deflateinit2-safety) | [deflateInit__safety](#target-zlibf-spec-public-goal-deflateinit-safety) |
| [deflatePending](#target-zlibf-spec-public-goal-deflatepending) | [deflatePending_safety](#target-zlibf-spec-public-goal-deflatepending-safety) |
| [deflateSetHeader](#target-zlibf-spec-public-goal-deflatesetheader) | [deflateSetHeader_safety](#target-zlibf-spec-public-goal-deflatesetheader-safety) |
| [deflateTune](#target-zlibf-spec-public-goal-deflatetune) | [deflateTune_safety](#target-zlibf-spec-public-goal-deflatetune-safety) |
| [deflateUsed](#target-zlibf-spec-public-goal-deflateused) | [deflateUsed_safety](#target-zlibf-spec-public-goal-deflateused-safety) |
| [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) | [deflateCopy_safety](#target-zlibf-spec-public-goal-deflatecopy-safety) |
| [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) | [deflateGetDictionary_safety](#target-zlibf-spec-public-goal-deflategetdictionary-safety) |
| [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) | [deflateParams_safety](#target-zlibf-spec-public-goal-deflateparams-safety) |
| [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) | [deflateSetDictionary_safety](#target-zlibf-spec-public-goal-deflatesetdictionary-safety) |
| [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) | [deflate_safety](#target-zlibf-spec-public-goal-deflate-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflateBound_safety](#target-zlibf-spec-public-goal-deflatebound-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflateBound_z_safety](#target-zlibf-spec-public-goal-deflatebound-z-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflateEnd_safety](#target-zlibf-spec-public-goal-deflateend-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflateGetDictionary_safety](#target-zlibf-spec-public-goal-deflategetdictionary-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflateParams_safety](#target-zlibf-spec-public-goal-deflateparams-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflatePending_safety](#target-zlibf-spec-public-goal-deflatepending-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflatePrime_safety](#target-zlibf-spec-public-goal-deflateprime-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflateReset_safety](#target-zlibf-spec-public-goal-deflatereset-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflateSetDictionary_safety](#target-zlibf-spec-public-goal-deflatesetdictionary-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflateSetHeader_safety](#target-zlibf-spec-public-goal-deflatesetheader-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflateTune_safety](#target-zlibf-spec-public-goal-deflatetune-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflateUsed_safety](#target-zlibf-spec-public-goal-deflateused-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflate_safety](#target-zlibf-spec-public-goal-deflate-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzbuffer_safety](#target-zlibf-spec-public-goal-gzbuffer-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzclearerr_safety](#target-zlibf-spec-public-goal-gzclearerr-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzclose_r_safety](#target-zlibf-spec-public-goal-gzclose-r-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzclose_safety](#target-zlibf-spec-public-goal-gzclose-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzclose_w_safety](#target-zlibf-spec-public-goal-gzclose-w-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzdirect_safety](#target-zlibf-spec-public-goal-gzdirect-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzdopen_safety](#target-zlibf-spec-public-goal-gzdopen-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzeof_safety](#target-zlibf-spec-public-goal-gzeof-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzerror_safety](#target-zlibf-spec-public-goal-gzerror-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzflush_safety](#target-zlibf-spec-public-goal-gzflush-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzfread_safety](#target-zlibf-spec-public-goal-gzfread-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzfwrite_safety](#target-zlibf-spec-public-goal-gzfwrite-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzgetc__safety](#target-zlibf-spec-public-goal-gzgetc-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzgetc_safety](#target-zlibf-spec-public-goal-gzgetc-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzgets_safety](#target-zlibf-spec-public-goal-gzgets-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzoffset64_safety](#target-zlibf-spec-public-goal-gzoffset64-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzoffset_safety](#target-zlibf-spec-public-goal-gzoffset-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzopen64_safety](#target-zlibf-spec-public-goal-gzopen64-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzopen_safety](#target-zlibf-spec-public-goal-gzopen-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzprintf_safety](#target-zlibf-spec-public-goal-gzprintf-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzputc_safety](#target-zlibf-spec-public-goal-gzputc-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzputs_safety](#target-zlibf-spec-public-goal-gzputs-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzread_safety](#target-zlibf-spec-public-goal-gzread-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzrewind_safety](#target-zlibf-spec-public-goal-gzrewind-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzseek64_safety](#target-zlibf-spec-public-goal-gzseek64-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzseek_safety](#target-zlibf-spec-public-goal-gzseek-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzsetparams_safety](#target-zlibf-spec-public-goal-gzsetparams-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gztell64_safety](#target-zlibf-spec-public-goal-gztell64-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gztell_safety](#target-zlibf-spec-public-goal-gztell-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzungetc_safety](#target-zlibf-spec-public-goal-gzungetc-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzvprintf_safety](#target-zlibf-spec-public-goal-gzvprintf-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzwrite_safety](#target-zlibf-spec-public-goal-gzwrite-safety) |
| [gzeof](#target-zlibf-spec-public-goal-gzeof) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [inflateBackEnd](#target-zlibf-spec-public-goal-inflatebackend) | [inflateBackEnd_safety](#target-zlibf-spec-public-goal-inflatebackend-safety) |
| [inflateBackEnd](#target-zlibf-spec-public-goal-inflatebackend) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [inflateBackInit_](#target-zlibf-spec-public-goal-inflatebackinit) | [inflateBackInit__safety](#target-zlibf-spec-public-goal-inflatebackinit-safety) |
| [inflateBackInit_](#target-zlibf-spec-public-goal-inflatebackinit) | [inflate_back_initialisation_domain](#target-zlibf-spec-public-goal-inflate-back-initialisation-domain) |
| [inflateBackInit_](#target-zlibf-spec-public-goal-inflatebackinit) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) | [inflateCopy_safety](#target-zlibf-spec-public-goal-inflatecopy-safety) |
| [inflateEnd](#target-zlibf-spec-public-goal-inflateend) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [inflateInit2__safety](#target-zlibf-spec-public-goal-inflateinit2-safety) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [inflateInit2__safety](#target-zlibf-spec-public-goal-inflateinit2-safety) | [inflateInit__safety](#target-zlibf-spec-public-goal-inflateinit-safety) |
| [inflateMark](#target-zlibf-spec-public-goal-inflatemark) | [inflateMark_safety](#target-zlibf-spec-public-goal-inflatemark-safety) |
| [inflatePrime](#target-zlibf-spec-public-goal-inflateprime) | [inflatePrime_safety](#target-zlibf-spec-public-goal-inflateprime-safety) |
| [inflateSetDictionary](#target-zlibf-spec-public-goal-inflatesetdictionary) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) | [inflateBackEnd_safety](#target-zlibf-spec-public-goal-inflatebackend-safety) |
| [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) | [inflateBack_safety](#target-zlibf-spec-public-goal-inflateback-safety) |
| [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) | [inflateCopy_safety](#target-zlibf-spec-public-goal-inflatecopy-safety) |
| [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) | [inflateEnd_safety](#target-zlibf-spec-public-goal-inflateend-safety) |
| [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) | [inflateGetDictionary_safety](#target-zlibf-spec-public-goal-inflategetdictionary-safety) |
| [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) | [inflateReset2_safety](#target-zlibf-spec-public-goal-inflatereset2-safety) |
| [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) | [inflateReset_safety](#target-zlibf-spec-public-goal-inflatereset-safety) |
| [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) | [inflateSetDictionary_safety](#target-zlibf-spec-public-goal-inflatesetdictionary-safety) |
| [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) | [inflate_safety](#target-zlibf-spec-public-goal-inflate-safety) |
| [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) | [inflateEnd_safety](#target-zlibf-spec-public-goal-inflateend-safety) |
| [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) | [inflateGetDictionary_safety](#target-zlibf-spec-public-goal-inflategetdictionary-safety) |
| [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) | [inflateGetHeader_safety](#target-zlibf-spec-public-goal-inflategetheader-safety) |
| [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) | [inflateMark_safety](#target-zlibf-spec-public-goal-inflatemark-safety) |
| [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) | [inflatePrime_safety](#target-zlibf-spec-public-goal-inflateprime-safety) |
| [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) | [inflateReset2_safety](#target-zlibf-spec-public-goal-inflatereset2-safety) |
| [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) | [inflateReset_safety](#target-zlibf-spec-public-goal-inflatereset-safety) |
| [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) | [inflateSetDictionary_safety](#target-zlibf-spec-public-goal-inflatesetdictionary-safety) |
| [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) | [inflateSync_safety](#target-zlibf-spec-public-goal-inflatesync-safety) |
| [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) | [inflate_safety](#target-zlibf-spec-public-goal-inflate-safety) |
| [zlibCompileFlags](#target-zlibf-spec-public-goal-zlibcompileflags) | [zlibCompileFlags_safety](#target-zlibf-spec-public-goal-zlibcompileflags-safety) |
| [zlibVersion](#target-zlibf-spec-public-goal-zlibversion) | [zlibVersion_safety](#target-zlibf-spec-public-goal-zlibversion-safety) |

## C 函数调用

右列目标对应的实现调用左列入口。这种调用关系不意味着，证明时必须把左列入口的完整契约作为前提。

| 来源 | 目标 |
| --- | --- |
| [adler32](#target-zlibf-spec-public-goal-adler32) | [deflate](#target-zlibf-spec-public-goal-deflate) |
| [adler32](#target-zlibf-spec-public-goal-adler32) | [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep) |
| [adler32](#target-zlibf-spec-public-goal-adler32) | [deflateSetDictionary](#target-zlibf-spec-public-goal-deflatesetdictionary) |
| [adler32](#target-zlibf-spec-public-goal-adler32) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [adler32](#target-zlibf-spec-public-goal-adler32) | [inflateSetDictionary](#target-zlibf-spec-public-goal-inflatesetdictionary) |
| [adler32_z](#target-zlibf-spec-public-goal-adler32-z) | [adler32](#target-zlibf-spec-public-goal-adler32) |
| [compress2](#target-zlibf-spec-public-goal-compress2) | [compress](#target-zlibf-spec-public-goal-compress) |
| [compress2_z](#target-zlibf-spec-public-goal-compress2-z) | [compress2](#target-zlibf-spec-public-goal-compress2) |
| [compress2_z](#target-zlibf-spec-public-goal-compress2-z) | [compress_z](#target-zlibf-spec-public-goal-compress-z) |
| [compressBound_z](#target-zlibf-spec-public-goal-compressbound-z) | [compressBound](#target-zlibf-spec-public-goal-compressbound) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [deflate](#target-zlibf-spec-public-goal-deflate) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [deflateSetDictionary](#target-zlibf-spec-public-goal-deflatesetdictionary) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [crc32_combine64](#target-zlibf-spec-public-goal-crc32-combine64) | [crc32_combine](#target-zlibf-spec-public-goal-crc32-combine) |
| [crc32_combine_gen64](#target-zlibf-spec-public-goal-crc32-combine-gen64) | [crc32_combine64](#target-zlibf-spec-public-goal-crc32-combine64) |
| [crc32_combine_gen64](#target-zlibf-spec-public-goal-crc32-combine-gen64) | [crc32_combine_gen](#target-zlibf-spec-public-goal-crc32-combine-gen) |
| [crc32_combine_op](#target-zlibf-spec-public-goal-crc32-combine-op) | [crc32_combine64](#target-zlibf-spec-public-goal-crc32-combine64) |
| [crc32_z](#target-zlibf-spec-public-goal-crc32-z) | [crc32](#target-zlibf-spec-public-goal-crc32) |
| [crc32_z](#target-zlibf-spec-public-goal-crc32-z) | [deflate](#target-zlibf-spec-public-goal-deflate) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [compress2_z](#target-zlibf-spec-public-goal-compress2-z) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [deflateParams](#target-zlibf-spec-public-goal-deflateparams) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzclose_w](#target-zlibf-spec-public-goal-gzclose-w) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzflush](#target-zlibf-spec-public-goal-gzflush) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzfwrite](#target-zlibf-spec-public-goal-gzfwrite) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzputc](#target-zlibf-spec-public-goal-gzputc) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzputs](#target-zlibf-spec-public-goal-gzputs) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzsetparams](#target-zlibf-spec-public-goal-gzsetparams) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzvprintf](#target-zlibf-spec-public-goal-gzvprintf) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzwrite](#target-zlibf-spec-public-goal-gzwrite) |
| [deflateBound_z](#target-zlibf-spec-public-goal-deflatebound-z) | [deflateBound](#target-zlibf-spec-public-goal-deflatebound) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [compress2_z](#target-zlibf-spec-public-goal-compress2-z) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [gzclose_w](#target-zlibf-spec-public-goal-gzclose-w) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [deflateInit_](#target-zlibf-spec-public-goal-deflateinit) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzclose_w](#target-zlibf-spec-public-goal-gzclose-w) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzflush](#target-zlibf-spec-public-goal-gzflush) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzfwrite](#target-zlibf-spec-public-goal-gzfwrite) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzputc](#target-zlibf-spec-public-goal-gzputc) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzputs](#target-zlibf-spec-public-goal-gzputs) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzsetparams](#target-zlibf-spec-public-goal-gzsetparams) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzvprintf](#target-zlibf-spec-public-goal-gzvprintf) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzwrite](#target-zlibf-spec-public-goal-gzwrite) |
| [deflateInit_](#target-zlibf-spec-public-goal-deflateinit) | [compress2_z](#target-zlibf-spec-public-goal-compress2-z) |
| [deflateParams](#target-zlibf-spec-public-goal-deflateparams) | [gzsetparams](#target-zlibf-spec-public-goal-gzsetparams) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzclose_w](#target-zlibf-spec-public-goal-gzclose-w) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzflush](#target-zlibf-spec-public-goal-gzflush) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzfwrite](#target-zlibf-spec-public-goal-gzfwrite) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzputc](#target-zlibf-spec-public-goal-gzputc) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzputs](#target-zlibf-spec-public-goal-gzputs) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzsetparams](#target-zlibf-spec-public-goal-gzsetparams) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzvprintf](#target-zlibf-spec-public-goal-gzvprintf) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzwrite](#target-zlibf-spec-public-goal-gzwrite) |
| [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep) | [deflateReset](#target-zlibf-spec-public-goal-deflatereset) |
| [gzclose_r](#target-zlibf-spec-public-goal-gzclose-r) | [gzclose](#target-zlibf-spec-public-goal-gzclose) |
| [gzclose_w](#target-zlibf-spec-public-goal-gzclose-w) | [gzclose](#target-zlibf-spec-public-goal-gzclose) |
| [gzgetc](#target-zlibf-spec-public-goal-gzgetc) | [gzgetc_](#target-zlibf-spec-public-goal-gzgetc) |
| [gzoffset64](#target-zlibf-spec-public-goal-gzoffset64) | [gzoffset](#target-zlibf-spec-public-goal-gzoffset) |
| [gzrewind](#target-zlibf-spec-public-goal-gzrewind) | [gzseek64](#target-zlibf-spec-public-goal-gzseek64) |
| [gzseek64](#target-zlibf-spec-public-goal-gzseek64) | [gzseek](#target-zlibf-spec-public-goal-gzseek) |
| [gztell64](#target-zlibf-spec-public-goal-gztell64) | [gztell](#target-zlibf-spec-public-goal-gztell) |
| [gzvprintf](#target-zlibf-spec-public-goal-gzvprintf) | [gzprintf](#target-zlibf-spec-public-goal-gzprintf) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [gzfread](#target-zlibf-spec-public-goal-gzfread) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [gzgetc](#target-zlibf-spec-public-goal-gzgetc) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [gzgets](#target-zlibf-spec-public-goal-gzgets) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [gzread](#target-zlibf-spec-public-goal-gzread) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [gzungetc](#target-zlibf-spec-public-goal-gzungetc) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [uncompress2_z](#target-zlibf-spec-public-goal-uncompress2-z) |
| [inflateEnd](#target-zlibf-spec-public-goal-inflateend) | [gzclose_r](#target-zlibf-spec-public-goal-gzclose-r) |
| [inflateEnd](#target-zlibf-spec-public-goal-inflateend) | [uncompress2_z](#target-zlibf-spec-public-goal-uncompress2-z) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gzdirect](#target-zlibf-spec-public-goal-gzdirect) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gzfread](#target-zlibf-spec-public-goal-gzfread) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gzgetc](#target-zlibf-spec-public-goal-gzgetc) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gzgets](#target-zlibf-spec-public-goal-gzgets) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gzread](#target-zlibf-spec-public-goal-gzread) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gzungetc](#target-zlibf-spec-public-goal-gzungetc) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [inflateInit_](#target-zlibf-spec-public-goal-inflateinit) |
| [inflateInit_](#target-zlibf-spec-public-goal-inflateinit) | [uncompress2_z](#target-zlibf-spec-public-goal-uncompress2-z) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [gzdirect](#target-zlibf-spec-public-goal-gzdirect) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [gzfread](#target-zlibf-spec-public-goal-gzfread) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [gzgetc](#target-zlibf-spec-public-goal-gzgetc) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [gzgets](#target-zlibf-spec-public-goal-gzgets) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [gzread](#target-zlibf-spec-public-goal-gzread) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [gzungetc](#target-zlibf-spec-public-goal-gzungetc) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [inflateReset2](#target-zlibf-spec-public-goal-inflatereset2) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [inflateSync](#target-zlibf-spec-public-goal-inflatesync) |
| [inflateReset2](#target-zlibf-spec-public-goal-inflatereset2) | [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) |
| [inflateResetKeep](#target-zlibf-spec-public-goal-inflateresetkeep) | [inflateReset](#target-zlibf-spec-public-goal-inflatereset) |
| [uncompress2](#target-zlibf-spec-public-goal-uncompress2) | [uncompress](#target-zlibf-spec-public-goal-uncompress) |
| [uncompress2_z](#target-zlibf-spec-public-goal-uncompress2-z) | [uncompress2](#target-zlibf-spec-public-goal-uncompress2) |
| [uncompress2_z](#target-zlibf-spec-public-goal-uncompress2-z) | [uncompress_z](#target-zlibf-spec-public-goal-uncompress-z) |
| [zError](#target-zlibf-spec-public-goal-zerror) | [deflate](#target-zlibf-spec-public-goal-deflate) |
| [zError](#target-zlibf-spec-public-goal-zerror) | [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) |
| [zlibVersion](#target-zlibf-spec-public-goal-zlibversion) | [compress2_z](#target-zlibf-spec-public-goal-compress2-z) |

## 规格中的引用

右列目标的定义引用左列目标或实现。这里记录的是定义中的引用，不是证明依赖。

| 来源 | 目标 |
| --- | --- |
| [adler32](#target-zlibf-spec-public-goal-adler32) | [adler32_safety](#target-zlibf-spec-public-goal-adler32-safety) |
| [adler32_combine](#target-zlibf-spec-public-goal-adler32-combine) | [adler32_combine_safety](#target-zlibf-spec-public-goal-adler32-combine-safety) |
| [adler32_combine64](#target-zlibf-spec-public-goal-adler32-combine64) | [adler32_combine64_safety](#target-zlibf-spec-public-goal-adler32-combine64-safety) |
| [adler32_z](#target-zlibf-spec-public-goal-adler32-z) | [adler32_z_safety](#target-zlibf-spec-public-goal-adler32-z-safety) |
| [compress](#target-zlibf-spec-public-goal-compress) | [compress_safety](#target-zlibf-spec-public-goal-compress-safety) |
| [compress2](#target-zlibf-spec-public-goal-compress2) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety) |
| [compress2_z](#target-zlibf-spec-public-goal-compress2-z) | [compress2_z_first_alloc_failure](#target-zlibf-spec-api-goal-compress2-z-first-alloc-failure) |
| [compress2_z](#target-zlibf-spec-public-goal-compress2-z) | [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety) |
| [compressBound](#target-zlibf-spec-public-goal-compressbound) | [compress_bound_value](#target-zlibf-spec-api-goal-compress-bound-value) |
| [compressBound_z](#target-zlibf-spec-public-goal-compressbound-z) | [compress_bound_value](#target-zlibf-spec-api-goal-compress-bound-value) |
| [compress_z](#target-zlibf-spec-public-goal-compress-z) | [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [crc32_safety](#target-zlibf-spec-public-goal-crc32-safety) |
| [crc32_combine](#target-zlibf-spec-public-goal-crc32-combine) | [crc32_combine_safety](#target-zlibf-spec-public-goal-crc32-combine-safety) |
| [crc32_combine64](#target-zlibf-spec-public-goal-crc32-combine64) | [crc32_combine64_safety](#target-zlibf-spec-public-goal-crc32-combine64-safety) |
| [crc32_combine_gen](#target-zlibf-spec-public-goal-crc32-combine-gen) | [crc32_combine_gen_safety](#target-zlibf-spec-public-goal-crc32-combine-gen-safety) |
| [crc32_combine_gen](#target-zlibf-spec-public-goal-crc32-combine-gen) | [crc32_combine_op_safety](#target-zlibf-spec-public-goal-crc32-combine-op-safety) |
| [crc32_combine_gen64](#target-zlibf-spec-public-goal-crc32-combine-gen64) | [crc32_combine_gen64_safety](#target-zlibf-spec-public-goal-crc32-combine-gen64-safety) |
| [crc32_combine_gen64](#target-zlibf-spec-public-goal-crc32-combine-gen64) | [crc32_combine_op_safety](#target-zlibf-spec-public-goal-crc32-combine-op-safety) |
| [crc32_combine_op](#target-zlibf-spec-public-goal-crc32-combine-op) | [crc32_combine_op_safety](#target-zlibf-spec-public-goal-crc32-combine-op-safety) |
| [crc32_z](#target-zlibf-spec-public-goal-crc32-z) | [crc32_z_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-z-all-byte-views) |
| [crc32_z](#target-zlibf-spec-public-goal-crc32-z) | [crc32_z_safety](#target-zlibf-spec-public-goal-crc32-z-safety) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [deflate_safety](#target-zlibf-spec-public-goal-deflate-safety) |
| [deflateBound](#target-zlibf-spec-public-goal-deflatebound) | [deflateBound_safety](#target-zlibf-spec-public-goal-deflatebound-safety) |
| [deflateBound](#target-zlibf-spec-public-goal-deflatebound) | [deflate_sequence](#target-zlibf-spec-public-goal-deflate-sequence) |
| [deflateBound_z](#target-zlibf-spec-public-goal-deflatebound-z) | [deflateBound_z_safety](#target-zlibf-spec-public-goal-deflatebound-z-safety) |
| [deflateBound_z](#target-zlibf-spec-public-goal-deflatebound-z) | [deflate_sequence](#target-zlibf-spec-public-goal-deflate-sequence) |
| [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy) | [deflateCopy_safety](#target-zlibf-spec-public-goal-deflatecopy-safety) |
| [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy) | [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [deflateEnd_safety](#target-zlibf-spec-public-goal-deflateend-safety) |
| [deflateGetDictionary](#target-zlibf-spec-public-goal-deflategetdictionary) | [deflateGetDictionary_safety](#target-zlibf-spec-public-goal-deflategetdictionary-safety) |
| [deflateGetDictionary](#target-zlibf-spec-public-goal-deflategetdictionary) | [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [deflateInit2__safety](#target-zlibf-spec-public-goal-deflateinit2-safety) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [deflate_initialisation_domain](#target-zlibf-spec-public-goal-deflate-initialisation-domain) |
| [deflateInit_](#target-zlibf-spec-public-goal-deflateinit) | [deflateInit__safety](#target-zlibf-spec-public-goal-deflateinit-safety) |
| [deflateParams](#target-zlibf-spec-public-goal-deflateparams) | [deflateParams_safety](#target-zlibf-spec-public-goal-deflateparams-safety) |
| [deflateParams](#target-zlibf-spec-public-goal-deflateparams) | [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) |
| [deflatePending](#target-zlibf-spec-public-goal-deflatepending) | [deflatePending_safety](#target-zlibf-spec-public-goal-deflatepending-safety) |
| [deflatePrime](#target-zlibf-spec-public-goal-deflateprime) | [deflatePrime_safety](#target-zlibf-spec-public-goal-deflateprime-safety) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [deflateReset_safety](#target-zlibf-spec-public-goal-deflatereset-safety) |
| [deflateSetDictionary](#target-zlibf-spec-public-goal-deflatesetdictionary) | [deflateSetDictionary_safety](#target-zlibf-spec-public-goal-deflatesetdictionary-safety) |
| [deflateSetDictionary](#target-zlibf-spec-public-goal-deflatesetdictionary) | [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) |
| [deflateSetHeader](#target-zlibf-spec-public-goal-deflatesetheader) | [deflateSetHeader_safety](#target-zlibf-spec-public-goal-deflatesetheader-safety) |
| [deflateTune](#target-zlibf-spec-public-goal-deflatetune) | [deflateTune_safety](#target-zlibf-spec-public-goal-deflatetune-safety) |
| [deflateUsed](#target-zlibf-spec-public-goal-deflateused) | [deflateUsed_safety](#target-zlibf-spec-public-goal-deflateused-safety) |
| [gzbuffer](#target-zlibf-spec-public-goal-gzbuffer) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzbuffer](#target-zlibf-spec-public-goal-gzbuffer) | [gzbuffer_safety](#target-zlibf-spec-public-goal-gzbuffer-safety) |
| [gzclearerr](#target-zlibf-spec-public-goal-gzclearerr) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzclearerr](#target-zlibf-spec-public-goal-gzclearerr) | [gzclearerr_safety](#target-zlibf-spec-public-goal-gzclearerr-safety) |
| [gzclose](#target-zlibf-spec-public-goal-gzclose) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzclose](#target-zlibf-spec-public-goal-gzclose) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzclose](#target-zlibf-spec-public-goal-gzclose) | [gzclose_safety](#target-zlibf-spec-public-goal-gzclose-safety) |
| [gzclose_r](#target-zlibf-spec-public-goal-gzclose-r) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzclose_r](#target-zlibf-spec-public-goal-gzclose-r) | [gzclose_r_safety](#target-zlibf-spec-public-goal-gzclose-r-safety) |
| [gzclose_w](#target-zlibf-spec-public-goal-gzclose-w) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzclose_w](#target-zlibf-spec-public-goal-gzclose-w) | [gzclose_w_safety](#target-zlibf-spec-public-goal-gzclose-w-safety) |
| [gzdirect](#target-zlibf-spec-public-goal-gzdirect) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzdirect](#target-zlibf-spec-public-goal-gzdirect) | [gzdirect_safety](#target-zlibf-spec-public-goal-gzdirect-safety) |
| [gzdopen](#target-zlibf-spec-public-goal-gzdopen) | [gz_sequence_nonvacuity](#target-zlibf-spec-public-goal-gz-sequence-nonvacuity) |
| [gzeof](#target-zlibf-spec-public-goal-gzeof) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzeof](#target-zlibf-spec-public-goal-gzeof) | [gzeof_safety](#target-zlibf-spec-public-goal-gzeof-safety) |
| [gzerror](#target-zlibf-spec-public-goal-gzerror) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzerror](#target-zlibf-spec-public-goal-gzerror) | [gzerror_safety](#target-zlibf-spec-public-goal-gzerror-safety) |
| [gzflush](#target-zlibf-spec-public-goal-gzflush) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzflush](#target-zlibf-spec-public-goal-gzflush) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzflush](#target-zlibf-spec-public-goal-gzflush) | [gzflush_safety](#target-zlibf-spec-public-goal-gzflush-safety) |
| [gzfread](#target-zlibf-spec-public-goal-gzfread) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzfread](#target-zlibf-spec-public-goal-gzfread) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzfread](#target-zlibf-spec-public-goal-gzfread) | [gzfread_safety](#target-zlibf-spec-public-goal-gzfread-safety) |
| [gzfwrite](#target-zlibf-spec-public-goal-gzfwrite) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzfwrite](#target-zlibf-spec-public-goal-gzfwrite) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzfwrite](#target-zlibf-spec-public-goal-gzfwrite) | [gzfwrite_safety](#target-zlibf-spec-public-goal-gzfwrite-safety) |
| [gzgetc](#target-zlibf-spec-public-goal-gzgetc) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzgetc](#target-zlibf-spec-public-goal-gzgetc) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzgetc](#target-zlibf-spec-public-goal-gzgetc) | [gzgetc_safety](#target-zlibf-spec-public-goal-gzgetc-safety) |
| [gzgetc_](#target-zlibf-spec-public-goal-gzgetc) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzgetc_](#target-zlibf-spec-public-goal-gzgetc) | [gzgetc__safety](#target-zlibf-spec-public-goal-gzgetc-safety) |
| [gzgets](#target-zlibf-spec-public-goal-gzgets) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzgets](#target-zlibf-spec-public-goal-gzgets) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzgets](#target-zlibf-spec-public-goal-gzgets) | [gzgets_safety](#target-zlibf-spec-public-goal-gzgets-safety) |
| [gzoffset](#target-zlibf-spec-public-goal-gzoffset) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzoffset](#target-zlibf-spec-public-goal-gzoffset) | [gzoffset_safety](#target-zlibf-spec-public-goal-gzoffset-safety) |
| [gzoffset64](#target-zlibf-spec-public-goal-gzoffset64) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzoffset64](#target-zlibf-spec-public-goal-gzoffset64) | [gzoffset64_safety](#target-zlibf-spec-public-goal-gzoffset64-safety) |
| [gzopen](#target-zlibf-spec-public-goal-gzopen) | [gz_initialisation_domain](#target-zlibf-spec-public-goal-gz-initialisation-domain) |
| [gzopen](#target-zlibf-spec-public-goal-gzopen) | [gz_sequence_nonvacuity](#target-zlibf-spec-public-goal-gz-sequence-nonvacuity) |
| [gzopen](#target-zlibf-spec-public-goal-gzopen) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [gzopen](#target-zlibf-spec-public-goal-gzopen) | [gzopen_safety](#target-zlibf-spec-public-goal-gzopen-safety) |
| [gzopen64](#target-zlibf-spec-public-goal-gzopen64) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [gzopen64](#target-zlibf-spec-public-goal-gzopen64) | [gzopen64_safety](#target-zlibf-spec-public-goal-gzopen64-safety) |
| [gzprintf](#target-zlibf-spec-public-goal-gzprintf) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzprintf](#target-zlibf-spec-public-goal-gzprintf) | [gzprintf_safety](#target-zlibf-spec-public-goal-gzprintf-safety) |
| [gzputc](#target-zlibf-spec-public-goal-gzputc) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzputc](#target-zlibf-spec-public-goal-gzputc) | [gzputc_safety](#target-zlibf-spec-public-goal-gzputc-safety) |
| [gzputs](#target-zlibf-spec-public-goal-gzputs) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzputs](#target-zlibf-spec-public-goal-gzputs) | [gzputs_safety](#target-zlibf-spec-public-goal-gzputs-safety) |
| [gzread](#target-zlibf-spec-public-goal-gzread) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzread](#target-zlibf-spec-public-goal-gzread) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzread](#target-zlibf-spec-public-goal-gzread) | [gzread_safety](#target-zlibf-spec-public-goal-gzread-safety) |
| [gzrewind](#target-zlibf-spec-public-goal-gzrewind) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzrewind](#target-zlibf-spec-public-goal-gzrewind) | [gzrewind_safety](#target-zlibf-spec-public-goal-gzrewind-safety) |
| [gzseek](#target-zlibf-spec-public-goal-gzseek) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzseek](#target-zlibf-spec-public-goal-gzseek) | [gzseek_safety](#target-zlibf-spec-public-goal-gzseek-safety) |
| [gzseek64](#target-zlibf-spec-public-goal-gzseek64) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzseek64](#target-zlibf-spec-public-goal-gzseek64) | [gzseek64_safety](#target-zlibf-spec-public-goal-gzseek64-safety) |
| [gzsetparams](#target-zlibf-spec-public-goal-gzsetparams) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzsetparams](#target-zlibf-spec-public-goal-gzsetparams) | [gzsetparams_safety](#target-zlibf-spec-public-goal-gzsetparams-safety) |
| [gztell](#target-zlibf-spec-public-goal-gztell) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gztell](#target-zlibf-spec-public-goal-gztell) | [gztell_safety](#target-zlibf-spec-public-goal-gztell-safety) |
| [gztell64](#target-zlibf-spec-public-goal-gztell64) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gztell64](#target-zlibf-spec-public-goal-gztell64) | [gztell64_safety](#target-zlibf-spec-public-goal-gztell64-safety) |
| [gzungetc](#target-zlibf-spec-public-goal-gzungetc) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzungetc](#target-zlibf-spec-public-goal-gzungetc) | [gzungetc_safety](#target-zlibf-spec-public-goal-gzungetc-safety) |
| [gzvprintf](#target-zlibf-spec-public-goal-gzvprintf) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzvprintf](#target-zlibf-spec-public-goal-gzvprintf) | [gzvprintf_safety](#target-zlibf-spec-public-goal-gzvprintf-safety) |
| [gzwrite](#target-zlibf-spec-public-goal-gzwrite) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzwrite](#target-zlibf-spec-public-goal-gzwrite) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzwrite](#target-zlibf-spec-public-goal-gzwrite) | [gzwrite_safety](#target-zlibf-spec-public-goal-gzwrite-safety) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [inflate_safety](#target-zlibf-spec-public-goal-inflate-safety) |
| [inflateBack](#target-zlibf-spec-public-goal-inflateback) | [inflateBack_safety](#target-zlibf-spec-public-goal-inflateback-safety) |
| [inflateBack](#target-zlibf-spec-public-goal-inflateback) | [inflate_back_sequence](#target-zlibf-spec-public-goal-inflate-back-sequence) |
| [inflateBack](#target-zlibf-spec-public-goal-inflateback) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [inflateBackEnd](#target-zlibf-spec-public-goal-inflatebackend) | [inflateBackEnd_safety](#target-zlibf-spec-public-goal-inflatebackend-safety) |
| [inflateBackEnd](#target-zlibf-spec-public-goal-inflatebackend) | [inflate_back_sequence](#target-zlibf-spec-public-goal-inflate-back-sequence) |
| [inflateBackEnd](#target-zlibf-spec-public-goal-inflatebackend) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [inflateBackInit_](#target-zlibf-spec-public-goal-inflatebackinit) | [inflateBackInit__safety](#target-zlibf-spec-public-goal-inflatebackinit-safety) |
| [inflateBackInit_](#target-zlibf-spec-public-goal-inflatebackinit) | [inflate_back_initialisation_domain](#target-zlibf-spec-public-goal-inflate-back-initialisation-domain) |
| [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) | [inflateCopy_safety](#target-zlibf-spec-public-goal-inflatecopy-safety) |
| [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) | [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) |
| [inflateEnd](#target-zlibf-spec-public-goal-inflateend) | [inflateEnd_safety](#target-zlibf-spec-public-goal-inflateend-safety) |
| [inflateEnd](#target-zlibf-spec-public-goal-inflateend) | [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) |
| [inflateGetDictionary](#target-zlibf-spec-public-goal-inflategetdictionary) | [inflateGetDictionary_safety](#target-zlibf-spec-public-goal-inflategetdictionary-safety) |
| [inflateGetDictionary](#target-zlibf-spec-public-goal-inflategetdictionary) | [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) |
| [inflateGetHeader](#target-zlibf-spec-public-goal-inflategetheader) | [inflateGetHeader_safety](#target-zlibf-spec-public-goal-inflategetheader-safety) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [inflateInit2__safety](#target-zlibf-spec-public-goal-inflateinit2-safety) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [inflate_initialisation_domain](#target-zlibf-spec-public-goal-inflate-initialisation-domain) |
| [inflateInit_](#target-zlibf-spec-public-goal-inflateinit) | [inflateInit__safety](#target-zlibf-spec-public-goal-inflateinit-safety) |
| [inflateMark](#target-zlibf-spec-public-goal-inflatemark) | [inflateMark_safety](#target-zlibf-spec-public-goal-inflatemark-safety) |
| [inflatePrime](#target-zlibf-spec-public-goal-inflateprime) | [inflatePrime_safety](#target-zlibf-spec-public-goal-inflateprime-safety) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [inflateReset_safety](#target-zlibf-spec-public-goal-inflatereset-safety) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) |
| [inflateReset2](#target-zlibf-spec-public-goal-inflatereset2) | [inflateReset2_safety](#target-zlibf-spec-public-goal-inflatereset2-safety) |
| [inflateReset2](#target-zlibf-spec-public-goal-inflatereset2) | [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) |
| [inflateSetDictionary](#target-zlibf-spec-public-goal-inflatesetdictionary) | [inflateSetDictionary_safety](#target-zlibf-spec-public-goal-inflatesetdictionary-safety) |
| [inflateSetDictionary](#target-zlibf-spec-public-goal-inflatesetdictionary) | [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) |
| [inflateSync](#target-zlibf-spec-public-goal-inflatesync) | [inflateSync_safety](#target-zlibf-spec-public-goal-inflatesync-safety) |
| [uncompress](#target-zlibf-spec-public-goal-uncompress) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [uncompress2](#target-zlibf-spec-public-goal-uncompress2) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [uncompress2_z](#target-zlibf-spec-public-goal-uncompress2-z) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [uncompress_z](#target-zlibf-spec-public-goal-uncompress-z) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [zlibCompileFlags](#target-zlibf-spec-public-goal-zlibcompileflags) | [zlibCompileFlags_safety](#target-zlibf-spec-public-goal-zlibcompileflags-safety) |
| [zlibVersion](#target-zlibf-spec-public-goal-zlibversion) | [zlibVersion_safety](#target-zlibf-spec-public-goal-zlibversion-safety) |

## 辅助证明的引用关系

这里把已观察到的定理引用按来源类别分组。一个分组不表示对应文件已经整体证明。
本表保留分组之间的全部直接连接，包括总览图为简化显示而省去的箭头。

| 辅助证明来源 | 直接引用它的目标 |
| --- | --- |
| API 模型引理 | dict_roundtrip, gz_roundtrip, gz_seek_read, inflate_completes, inflate_deferred_distance, roundtrip_completes, gzdopen, API 模型证明, gz.inv-open 的证明, gz.inv-open-fresh 的证明, gz.inv-open-path 的证明, gzlib.c 的证明, 不涉及堆的数学证明 |
| ByteAddress 字节地址模型证明 | first_aligned_offset, mask_refines_base_plus_offset, pointer_advance_preserves_low_bits |
| LibcBorrow 的证明 | LibcBorrowLoops 的证明, LibcBorrowPrimitives 的证明, PlatformMemory 的证明, borrowed-byte-frame 的证明, checksum.borrow-stable 的证明, deflate 生命周期证明, deflate 窗口与匹配证明, gz.inv-open 的证明, gzfs.borrow-stable 的证明, gzlib.c 的证明, inflate 模式与退出证明, inflate 存储与读位证明, libc-errno-cstring 的证明, 公开入口组合证明, 编码树构造与输出证明 |
| LibcBorrowLoops 的证明 | checksum.borrow-stable 的证明, deflate 生命周期证明, inflate 存储与读位证明, 编码树构造与输出证明 |
| LibcBorrowPrimitives 的证明 | checksum.borrow-stable 的证明, deflate 生命周期证明, gzfs.borrow-stable 的证明, gzlib.c 的证明, inflate 存储与读位证明, 公开入口组合证明, 编码树构造与输出证明 |
| LibcStrings 的证明 | LibcBorrow 的证明, gzfs.error-message-store 的证明, gzlib.c 的证明, 不涉及堆的数学证明, libc-errno-cstring 的证明 |
| PlatformMemory 的证明 | gz.inv-frame 的证明, gz.read-avail 的证明, gz.read-gzread 的证明, gz.read-load-error 的证明, gz.read-look 的证明, gz.read-store 的证明, gzread.c 的证明, gzwrite.c 的证明, inffast.c 的证明, inflate 存储与读位证明 |
| crc32_all_byte_views | inflate 存储与读位证明 |
| actual_body_preserves_origin | inffast.c 的证明 |
| actual_fast_preserves_origin | inffast.c 的证明 |
| actual_distance_block_preserves_origin | inffast.c 的证明 |
| actual_copy_match_refines_lz77 | inffast.c 的证明 |
| actual_drop_preserves_origin | inffast.c 的证明 |
| actual_rollback_preserves_origin | inffast.c 的证明 |
| drop_preserves_origin | inffast.c 的证明 |
| pull_preserves_origin | inffast.c 的证明 |
| decode_table_read_preserved | inftrees.c 的证明 |
| constructor_establishes_decode_table_invariant | infback.c 的证明, inflate 存储与读位证明, inftrees.c 的证明 |
| decode_table_invariant_of_prefix | infback.c 的证明, inftrees.c 的证明 |
| constructor_establishes_query_stability | infback.c 的证明 |
| query_stability_of_prefix | infback.c 的证明 |
| inflate_table_content | inftrees.c 的证明 |
| inflate_table_read_extent | infback.c 的证明, inflate 存储与读位证明 |
| retained_history_agrees | 格式证明 |
| deflate_valid | API 模型证明 |
| inflate_completes | API 模型证明 |
| inflate_decodes | API 模型证明 |
| crc32 | deflate 生命周期证明 |
| deflateEnd | deflate 生命周期证明, 公开入口组合证明 |
| deflateInit2_ | 公开入口组合证明 |
| gz_sequence_safety | 公开入口组合证明 |
| gzeof | gz.inv-queries 的证明 |
| inflate | gz.read-decomp 的证明, 公开入口组合证明 |
| inflateBackEnd | infback.c 的证明 |
| inflateBackInit_ | infback.c 的证明, 公开入口组合证明 |
| inflateEnd | inflate 存储与读位证明 |
| inflateInit2_ | inflate 存储与读位证明, 公开入口组合证明 |
| inflateSetDictionary | inflate 存储与读位证明 |
| adler32.c 的证明 | inflateSetDictionary, deflate 生命周期证明, inflate 入口组合证明, inflate 存储与读位证明, 公开入口组合证明 |
| API 模型证明 | compress2_z_first_alloc_failure, compress_bound_adequate, compress_bound_value, compress_roundtrip, deflate_bound_adequate, deflate_completes, deflate_full_flush_resync, deflate_valid, dict_roundtrip, gz_roundtrip, gz_seek_read, header_roundtrip, inflate_completes, inflate_decodes, inflate_deferred_distance, roundtrip, roundtrip_completes, inflateCodesUsed, gzlib.c 的证明 |
| borrowed-byte-frame 的证明 | inflate 存储与读位证明 |
| checksum.borrow-stable 的证明 | deflate 生命周期证明, inflate 存储与读位证明, 编码树构造与输出证明 |
| crc32.c 的证明 | crc32_all_byte_views, crc32_z_all_byte_views, crc32, crc32_z, deflate 生命周期证明, inflate 存储与读位证明, 公开入口组合证明 |
| deflate 状态构造证明 | deflateInit2_, deflateInit_, deflate_initialisation_domain, deflate 生命周期证明, deflate 窗口与匹配证明, gzwrite.c 的证明, 公开入口组合证明 |
| deflate 入口组合证明 | deflate, deflateCopy, deflateEnd, deflateEnd_safety, deflateGetDictionary, deflatePending, deflateReset, deflateResetKeep, deflateReset_safety, deflateSetHeader, deflateTune, deflateUsed, deflate_refusal, deflate_sequence_safety, deflate 生命周期证明, 公开入口组合证明 |
| deflate 生命周期证明 | deflateCopy, deflateCopy_safety, deflateEnd, deflateEnd_safety, deflateGetDictionary, deflateInit_, deflatePending, deflatePrime_safety, deflateReset, deflateResetKeep, deflateReset_safety, deflateSetHeader, deflateTune, deflateUsed, deflate_refusal, deflate 状态构造证明, deflate 入口组合证明, deflate 窗口与匹配证明, gzwrite.c 的证明, inffast.c 的证明, inflate 存储与读位证明, 公开入口组合证明, 编码树构造与输出证明 |
| deflate 窗口与匹配证明 | deflate, deflate_sequence_safety, deflate 状态构造证明, deflate 入口组合证明, deflate 生命周期证明, gz.read-read 的证明, gz.read-store 的证明, gzfs.error-message-store 的证明, gzfs.format-error-message 的证明, gzlib.c 的证明, gzwrite.c 的证明, inflate 存储与读位证明, 编码树构造与输出证明 |
| deflate_base.c 的证明 | deflateBound_safety, deflateBound_z_safety, deflateCopy_safety, deflateEnd_safety, deflateGetDictionary_safety, deflateParams_safety, deflatePending_safety, deflatePrime_safety, deflateReset_safety, deflateSetDictionary_safety, deflateSetHeader_safety, deflateTune_safety, deflateUsed_safety, deflate_refusal, deflate_safety, gz_refusal, gzbuffer_safety, gzclearerr_safety, gzclose_r_safety, gzclose_safety, gzclose_w_safety, gzdirect_safety, gzdopen_safety, gzeof_safety, gzerror_safety, gzflush_safety, gzfread_safety, gzfwrite_safety, gzgetc__safety, gzgetc_safety, gzgets_safety, gzoffset64_safety, gzoffset_safety, gzopen64_safety, gzopen_safety, gzprintf_safety, gzputc_safety, gzputs_safety, gzread_safety, gzrewind_safety, gzseek64_safety, gzseek_safety, gzsetparams_safety, gztell64_safety, gztell_safety, gzungetc_safety, gzvprintf_safety, gzwrite_safety, inflateEnd_safety, inflateGetDictionary_safety, inflateGetHeader_safety, inflateMark_safety, inflatePrime_safety, inflateReset2_safety, inflateReset_safety, inflateSetDictionary_safety, inflateSync_safety, inflate_safety, deflate 生命周期证明, gz.inv-clearerr 的证明, gz.inv-close 的证明, gz.inv-frame 的证明, gz.inv-offset-rewind 的证明, gz.inv-queries 的证明, gz.inv-seek 的证明, gz.read-close 的证明, gz.read-decomp 的证明, gz.read-direct-step 的证明, gz.read-getc-step 的证明, gz.read-gets-step 的证明, gz.read-gzread 的证明, gz.read-look 的证明, gz.sequence-safety 的证明, gzread.c 的证明, gzwrite.c 的证明, inflate 存储与读位证明, 公开入口组合证明, zlib.h.gzgetc-macro 的证明 |
| 格式证明 | short_decode_table_leaf_sound, short_rejected_leaf_stays_invalid, compress_roundtrip, format_deterministic, format_prefix_free, header_roundtrip, inflate_completes, rejected_has_no_symbols, API 模型证明, 不涉及堆的数学证明, infback.c 的证明, inffast.c 的证明, inffixed.h.input-meaning 的证明, inflate 存储与读位证明, inftrees.c 的证明, 编码树构造与输出证明 |
| 格式模型引理 | inflate 存储与读位证明 |
| gz.inv-clearerr 的证明 | gz.inv-seek 的证明, gz.read-store 的证明, gz.sequence-safety 的证明, gzlib.c 的证明, gzread.c 的证明, gzwrite.c 的证明 |
| gz.inv-close 的证明 | gz.sequence-safety 的证明 |
| gz.inv-frame 的证明 | gz.inv-clearerr 的证明, gz.read-decomp 的证明, gz.read-gzread 的证明, gz.read-load-error 的证明, gz.read-look 的证明, gz.read-read 的证明, gz.read-store 的证明, gz.sequence-safety 的证明, gzlib.c 的证明, gzread.c 的证明, gzwrite.c 的证明 |
| gz.inv-model 的证明 | gz.inv-clearerr 的证明, gz.inv-close 的证明, gz.inv-frame 的证明, gz.inv-offset-rewind 的证明, gz.inv-open 的证明, gz.inv-put-scalars 的证明, gz.inv-queries 的证明, gz.inv-reset 的证明, gz.inv-seek 的证明, gz.read-avail 的证明, gz.read-close 的证明, gz.read-decomp 的证明, gz.read-direct-step 的证明, gz.read-fetch 的证明, gz.read-getc-step 的证明, gz.read-gets-step 的证明, gz.read-gzread 的证明, gz.read-leaf-common 的证明, gz.read-load-error 的证明, gz.read-look 的证明, gz.read-read 的证明, gz.read-store 的证明, gz.sequence-safety 的证明, gzlib.c 的证明, gzread.c 的证明, gzwrite.c 的证明, 公开入口组合证明, zlib.h.gzgetc-macro 的证明 |
| gz.inv-offset-rewind 的证明 | gz.sequence-safety 的证明 |
| gz.inv-open 的证明 | gz.inv-open-fresh 的证明, gz.sequence-safety 的证明, 公开入口组合证明 |
| gz.inv-open-fd 的证明 | gz.inv-open-fresh 的证明 |
| gz.inv-open-fresh 的证明 | gz.sequence-safety 的证明, 公开入口组合证明 |
| gz.inv-open-path 的证明 | gz.inv-open-fresh 的证明 |
| gz.inv-put-scalars 的证明 | gz.inv-clearerr 的证明, gz.inv-queries 的证明, gz.inv-reset 的证明, gz.inv-seek 的证明, gz.read-avail 的证明, gz.read-decomp 的证明, gz.read-fetch 的证明, gz.read-gets-step 的证明, gz.read-leaf-common 的证明, gz.read-load-error 的证明, gz.read-look 的证明, gz.read-read 的证明, gz.read-store 的证明, gzlib.c 的证明, gzread.c 的证明, gzwrite.c 的证明 |
| gz.inv-queries 的证明 | gz.inv-close 的证明, gz.inv-seek 的证明, gz.sequence-safety 的证明 |
| gz.inv-reset 的证明 | gz.inv-seek 的证明 |
| gz.inv-seek 的证明 | gz.inv-offset-rewind 的证明, gz.inv-open 的证明, gz.sequence-safety 的证明 |
| gz.read-assembly 的证明 | gz.read-getc-step 的证明, gz.read-gets-step 的证明, 公开入口组合证明 |
| gz.read-avail 的证明 | gz.read-budget 的证明, gz.read-decomp 的证明, gz.read-fetch 的证明, gz.read-look 的证明 |
| gz.read-budget 的证明 | gz.read-decomp 的证明, gz.read-fetch 的证明, gz.read-look 的证明, gz.read-read 的证明 |
| gz.read-close 的证明 | gz.inv-close 的证明, gz.sequence-safety 的证明, gzwrite.c 的证明 |
| gz.read-decomp 的证明 | gz.read-assembly 的证明, gz.read-fetch 的证明, gz.read-gets-step 的证明, gz.read-gzread 的证明, gz.read-leaf-common 的证明, gz.read-read 的证明 |
| gz.read-direct-step 的证明 | 公开入口组合证明 |
| gz.read-fetch 的证明 | gz.read-assembly 的证明, gz.read-gets-step 的证明, gz.read-leaf-common 的证明, gz.read-read 的证明 |
| gz.read-getc-step 的证明 | gz.read-direct-step 的证明, 公开入口组合证明 |
| gz.read-gets-step 的证明 | 公开入口组合证明 |
| gz.read-gzread 的证明 | gz.read-assembly 的证明, gzread.c 的证明 |
| gz.read-leaf-common 的证明 | gz.read-direct-step 的证明, gz.read-getc-step 的证明, gz.read-gets-step 的证明 |
| gz.read-load-error 的证明 | gz.read-avail 的证明, gz.read-fetch 的证明, gz.read-read 的证明 |
| gz.read-look 的证明 | gz.read-assembly 的证明, gz.read-close 的证明, gz.read-getc-step 的证明, gz.read-gets-step 的证明, gz.read-leaf-common 的证明 |
| gz.read-read 的证明 | gz.read-assembly 的证明, gz.read-gzread 的证明, gzread.c 的证明 |
| gz.read-store 的证明 | gz.read-avail 的证明, gz.read-close 的证明, gz.read-decomp 的证明, gz.read-fetch 的证明, gz.read-load-error 的证明, gz.read-look 的证明, gz.read-read 的证明, gzread.c 的证明, gzwrite.c 的证明 |
| gz.sequence-safety 的证明 | gz_sequence_safety |
| gzfs 的证明 | gz.inv-open-path 的证明, gzfs.format-error-message 的证明, gzlib.c 的证明 |
| gzfs.borrow-stable 的证明 | LibcBorrowLoops 的证明, checksum.borrow-stable 的证明, deflate 生命周期证明, gzlib.c 的证明, inflate 存储与读位证明, 编码树构造与输出证明 |
| gzfs.borrowed-error 的证明 | gz.read-gzread 的证明, gz.read-load-error 的证明, gzwrite.c 的证明, libc-errno-cstring 的证明 |
| gzfs.error-message-store 的证明 | gzlib.c 的证明 |
| gzfs.format-error-message 的证明 | gzlib.c 的证明, gzwrite.c 的证明 |
| gzfs.oracle 的证明 | gz.inv-open-fd 的证明, gzlib.c 的证明, gzread.c 的证明, 公开入口组合证明 |
| gzfs.read-contract 的证明 | gz.read-avail 的证明, gz.read-decomp 的证明, gz.read-fetch 的证明, gz.read-look 的证明, gz.read-read 的证明, gz.read-store 的证明, gzwrite.c 的证明 |
| gzlib.c 的证明 | gzclearerr, gzdopen, gz.inv-clearerr 的证明, gz.inv-offset-rewind 的证明, gz.inv-open 的证明, gz.inv-open-fd 的证明, gz.inv-open-fresh 的证明, gz.inv-open-path 的证明, gz.inv-queries 的证明, gz.inv-seek 的证明, gz.read-avail 的证明, gz.read-close 的证明, gz.read-decomp 的证明, gz.read-direct-step 的证明, gz.read-fetch 的证明, gz.read-getc-step 的证明, gz.read-gets-step 的证明, gz.read-gzread 的证明, gz.read-leaf-common 的证明, gz.read-load-error 的证明, gz.read-look 的证明, gz.read-read 的证明, gz.read-store 的证明, gzfs.error-message-store 的证明, gzfs.oracle 的证明, gzfs.read-contract 的证明, gzread.c 的证明, gzwrite.c 的证明, 公开入口组合证明, zlib.h.gzgetc-macro 的证明 |
| gzread.c 的证明 | gz.inv-offset-rewind 的证明, gz.inv-seek 的证明, gz.read-assembly 的证明, gz.read-close 的证明, gz.read-decomp 的证明, gz.read-direct-step 的证明, gz.read-fetch 的证明, gz.read-getc-step 的证明, gz.read-gets-step 的证明, gz.read-gzread 的证明, gz.read-leaf-common 的证明, gz.read-read 的证明, gzwrite.c 的证明, zlib.h.gzgetc-macro 的证明 |
| gzwrite.c 的证明 | gz.inv-close 的证明, gz.read-close 的证明, gz.read-gzread 的证明, gz.read-look 的证明, gz.sequence-safety 的证明, gzread.c 的证明 |
| 不涉及堆的数学证明 | match_array_refines_lz77, output_copy_refines_lz77, window_copy_refines_lz77, copy_back_compose, retained_history_agrees, window_distance_check_agrees, API 模型证明, deflate 状态构造证明, deflate 生命周期证明, deflate 窗口与匹配证明, gzlib.c 的证明, infback.c 的证明, inffixed.h.input-meaning 的证明, inflate 存储与读位证明, inftrees.c 的证明, libc-errno-cstring 的证明, 编码树构造与输出证明 |
| infback.c 的证明 | inflateBackEnd, inflateBackInit_, inflateBack_safety, inflate_back_sequence_safety, gz.read-decomp 的证明, gz.read-read 的证明, gzlib.c 的证明, gzread.c 的证明, 公开入口组合证明 |
| inffast.c 的证明 | actual_body_preserves_origin, actual_body_refines_token, actual_fast_preserves_origin, actual_distance_block_preserves_origin, actual_distance_refines_lz77, distance_lookup_matches_format, fast_safe, step_safe, length_lookup_matches_format, actual_body_retains_selected_length, actual_copy_match_refines_lz77, match_array_refines_lz77, actual_drop_preserves_origin, actual_pull_preserves_origin, actual_rollback_preserves_origin, drop_preserves_origin, initial_origin, pull_preserves_origin, rollback_preserves_origin, output_copy_refines_lz77, gzfs.error-message-store 的证明, gzlib.c 的证明, 不涉及堆的数学证明, infback.c 的证明, inffixed.h.input-meaning 的证明, inflate 存储与读位证明, inftrees.c 的证明 |
| inffixed.h.fast-flags 的证明 | fixed_tables_have_fast_leaf_flags |
| inffixed.h.input-meaning 的证明 | inflate 存储与读位证明 |
| inffixed.h.meaning 的证明 | inffixed.h.input-meaning 的证明 |
| inflate 入口组合证明 | deflate_initialisation_domain, inflateCopy, inflateEnd, inflateGetDictionary, inflateGetHeader, inflateGetHeader_safety, inflateInit2_, inflateInit_, inflateMark, inflatePrime, inflateReset, inflateReset2, inflateSetDictionary, inflateSyncPoint, inflateUndermine, inflateValidate, inflate_initialisation_domain, inflate_refusal, gz.read-look 的证明, inflate 存储与读位证明, 公开入口组合证明 |
| inflate 模式与退出证明 | gzlib.c 的证明, infback.c 的证明, inffast.c 的证明, inflate 存储与读位证明 |
| inflate 存储与读位证明 | deflateReset, deflateResetKeep, inflate, inflateBackEnd, inflateBackInit_, inflateCopy, inflateCopy_safety, inflateEnd, inflateGetDictionary, inflateGetHeader_safety, inflateInit2_, inflateInit_, inflateMark, inflateReset, inflateReset2, inflateResetKeep, inflateSetDictionary, inflateSyncPoint, inflateUndermine, inflateValidate, inflate_refusal, inflate_sequence_safety, API 模型证明, deflate 生命周期证明, deflate 窗口与匹配证明, gz.inv-frame 的证明, gz.read-assembly 的证明, gz.read-avail 的证明, gz.read-close 的证明, gz.read-decomp 的证明, gz.read-getc-step 的证明, gz.read-gets-step 的证明, gz.read-gzread 的证明, gz.read-load-error 的证明, gz.read-look 的证明, gz.read-read 的证明, gzlib.c 的证明, gzread.c 的证明, gzwrite.c 的证明, infback.c 的证明, inffast.c 的证明, inflate 入口组合证明, inflate 模式与退出证明, inftrees.c 的证明, 公开入口组合证明 |
| inflate.c 的证明 | inflate 模式与退出证明, inflate 存储与读位证明 |
| inftrees.c 的证明 | decode_table_matches_format, short_decode_table_leaf_sound, decode_table_leaf_sound, decode_table_read_preserved, constructor_establishes_decode_table_invariant, decode_table_invariant_of_prefix, constructor_establishes_query_stability, short_rejected_leaf_stays_invalid, constructor_establishes_fast_leaf_flags, leaf_classification_agrees, inflate_table_content, inflate_table_decoder_safe, inflate_table_read_extent, constructor_root_bits, constructor_subtable_bits, 不涉及堆的数学证明, infback.c 的证明, inffixed.h.input-meaning 的证明, inflate 存储与读位证明, 编码树构造与输出证明 |
| libc-errno-cstring 的证明 | gz.read-gzread 的证明, gz.read-load-error 的证明, gzwrite.c 的证明 |
| 公开入口组合证明 | adler32_combine, adler32_combine64, adler32_z, compress2_safety, compress2_z_safety, compressBound, compressBound_z, compress_safety, compress_z_safety, crc32_combine, crc32_combine64, crc32_combine_gen, crc32_combine_gen64, crc32_combine_op, deflateBound_safety, deflateBound_z_safety, deflateInit2__safety, get_crc_table, gz_sequence_nonvacuity, gz_sequence_safety, gzbuffer, gzbuffer_safety, gzclearerr_safety, gzclose_r_safety, gzclose_safety, gzclose_w_safety, gzdirect_safety, gzdopen, gzeof, gzeof_safety, gzerror, gzerror_safety, gzflush_safety, gzfread_safety, gzfwrite_safety, gzgetc__safety, gzgetc_safety, gzgets_safety, gzoffset, gzoffset64, gzoffset64_safety, gzoffset_safety, gzprintf_safety, gzputc_safety, gzputs_safety, gzread_safety, gzrewind, gzrewind_safety, gzseek64_safety, gzseek_safety, gzsetparams_safety, gztell64_safety, gztell_safety, gzungetc_safety, gzvprintf_safety, gzwrite_safety, inflateBackEnd, inflateBackInit_, inflateBackInit__safety, inflateInit2__safety, inflateSync_safety, inflate_back_initialisation_domain, inflate_refusal, uncompress2_safe, uncompress2_z_safe, uncompress_safe, uncompress_z_safe, zError, zlibVersion, adler32.c 的证明, deflate 生命周期证明, gz.inv-frame 的证明, gz.inv-offset-rewind 的证明, gz.inv-open 的证明, gz.inv-open-path 的证明, gz.inv-queries 的证明, gz.read-look 的证明, gz.read-store 的证明, gzfs.error-message-store 的证明, gzlib.c 的证明, gzread.c 的证明, inflate 存储与读位证明 |
| 运行时对象与算术引理 | byte_modifies_preserve_bases, byte_stores_preserve_bases, every_layout_is_representable, LibcBorrow 的证明, LibcBorrowLoops 的证明, LibcBorrowPrimitives 的证明, PlatformMemory 的证明, crc32_all_byte_views, crc32_z_all_byte_views, actual_body_preserves_origin, actual_body_refines_token, actual_fast_preserves_origin, actual_distance_block_preserves_origin, actual_distance_refines_lz77, fast_safe, actual_body_retains_selected_length, actual_copy_match_refines_lz77, actual_pull_preserves_origin, actual_rollback_preserves_origin, decode_table_classifies_input, decode_table_matches_format, short_decode_table_leaf_sound, decode_table_leaf_sound, constructor_establishes_decode_table_invariant, constructor_establishes_query_stability, constructor_establishes_fast_leaf_flags, inflate_table_content, inflate_table_decoder_safe, inflate_table_read_extent, constructor_root_bits, constructor_subtable_bits, compress2_z_first_alloc_failure, adler32, adler32_safety, adler32_z, adler32_z_safety, crc32, crc32_combine64_safety, crc32_combine_gen64_safety, crc32_combine_gen_safety, crc32_combine_op_safety, crc32_combine_safety, crc32_safety, crc32_z, crc32_z_safety, deflateBound_safety, deflateBound_z_safety, deflateCopy, deflateCopy_safety, deflateEnd, deflateEnd_safety, deflateGetDictionary, deflateGetDictionary_safety, deflateInit2_, deflateInit2__safety, deflateInit_, deflateInit__safety, deflateParams_safety, deflatePending, deflatePending_safety, deflatePrime_safety, deflateReset, deflateResetKeep, deflateReset_safety, deflateSetDictionary_safety, deflateSetHeader, deflateSetHeader_safety, deflateTune, deflateTune_safety, deflateUsed, deflateUsed_safety, deflate_initialisation_domain, deflate_refusal, deflate_safety, get_crc_table, gz_refusal, gz_sequence_nonvacuity, gzbuffer_safety, gzclearerr, gzclearerr_safety, gzclose_r_safety, gzclose_safety, gzclose_w_safety, gzdirect_safety, gzdopen, gzdopen_safety, gzeof_safety, gzerror, gzerror_safety, gzflush_safety, gzfread_safety, gzfwrite_safety, gzgetc__safety, gzgetc_safety, gzgets_safety, gzoffset, gzoffset64, gzoffset64_safety, gzoffset_safety, gzopen64_safety, gzopen_safety, gzprintf_safety, gzputc_safety, gzputs_safety, gzread_safety, gzrewind, gzrewind_safety, gzseek64_safety, gzseek_safety, gzsetparams_safety, gztell64_safety, gztell_safety, gzungetc_safety, gzvprintf_safety, gzwrite_safety, inflate, inflateBackEnd, inflateBackEnd_safety, inflateBackInit_, inflateBackInit__safety, inflateBack_safety, inflateCodesUsed, inflateCopy, inflateCopy_safety, inflateEnd, inflateEnd_safety, inflateGetDictionary, inflateGetDictionary_safety, inflateGetHeader, inflateGetHeader_safety, inflateInit2_, inflateInit2__safety, inflateInit_, inflateInit__safety, inflateMark, inflateMark_safety, inflatePrime, inflatePrime_safety, inflateReset, inflateReset2, inflateReset2_safety, inflateResetKeep, inflateReset_safety, inflateSetDictionary, inflateSetDictionary_safety, inflateSyncPoint, inflateSync_safety, inflateUndermine, inflateValidate, inflate_back_initialisation_domain, inflate_back_sequence_safety, inflate_initialisation_domain, inflate_refusal, inflate_safety, uncompress2_safe, uncompress2_z_safe, uncompress_safe, uncompress_z_safe, zError, zlibVersion, zlibVersion_safety, adler32.c 的证明, API 模型证明, borrowed-byte-frame 的证明, checksum.borrow-stable 的证明, crc32.c 的证明, deflate 状态构造证明, deflate 入口组合证明, deflate 生命周期证明, deflate 窗口与匹配证明, gz.inv-clearerr 的证明, gz.inv-close 的证明, gz.inv-frame 的证明, gz.inv-offset-rewind 的证明, gz.inv-open 的证明, gz.inv-open-fd 的证明, gz.inv-open-fresh 的证明, gz.inv-open-path 的证明, gz.inv-put-scalars 的证明, gz.inv-queries 的证明, gz.inv-reset 的证明, gz.inv-seek 的证明, gz.read-assembly 的证明, gz.read-avail 的证明, gz.read-budget 的证明, gz.read-close 的证明, gz.read-decomp 的证明, gz.read-direct-step 的证明, gz.read-fetch 的证明, gz.read-getc-step 的证明, gz.read-gets-step 的证明, gz.read-gzread 的证明, gz.read-leaf-common 的证明, gz.read-load-error 的证明, gz.read-look 的证明, gz.read-read 的证明, gz.read-store 的证明, gz.sequence-safety 的证明, gzfs 的证明, gzfs.borrow-stable 的证明, gzfs.error-message-store 的证明, gzfs.format-error-message 的证明, gzlib.c 的证明, gzread.c 的证明, gzwrite.c 的证明, 不涉及堆的数学证明, infback.c 的证明, inffast.c 的证明, inflate 入口组合证明, inflate 模式与退出证明, inflate 存储与读位证明, inftrees.c 的证明, libc-errno-cstring 的证明, 公开入口组合证明, 规格引理, 编码树构造与输出证明, zlib.h.gzgetc-macro 的证明, zutil.c 的证明 |
| 规格引理 | every_existing_heap_accepts_layout, actual_body_preserves_origin, actual_body_refines_token, distance_lookup_matches_format, length_lookup_matches_format, actual_body_retains_selected_length, drop_preserves_origin, pull_preserves_origin, rollback_preserves_origin, decode_table_invariant_of_prefix, short_rejected_leaf_stays_invalid, compress_bound_adequate, compress_roundtrip, deflate_bound_adequate, deflate_completes, deflate_full_flush_resync, deflate_valid, dict_roundtrip, header_roundtrip, inflate_completes, inflate_decodes, inflate_deferred_distance, roundtrip, roundtrip_completes, deflateInit2_, deflateInit2__safety, deflateInit_, deflate_initialisation_domain, gzdopen, API 模型证明, deflate 状态构造证明, deflate 生命周期证明, gz.inv-open 的证明, gzlib.c 的证明, gzwrite.c 的证明, infback.c 的证明, inffast.c 的证明, inflate 存储与读位证明, 公开入口组合证明 |
| 编码树构造与输出证明 | deflate 状态构造证明, deflate 入口组合证明, deflate 生命周期证明, deflate 窗口与匹配证明, gzwrite.c 的证明, 不涉及堆的数学证明, 公开入口组合证明 |
| zlib.h.gzgetc-macro 的证明 | gz.sequence-safety 的证明 |
| zutil.c 的证明 | inflate_table_content, deflate 状态构造证明, deflate 生命周期证明, gzfs.error-message-store 的证明, gzlib.c 的证明, gzwrite.c 的证明, infback.c 的证明, inflate 入口组合证明, inflate 模式与退出证明, inflate 存储与读位证明, inftrees.c 的证明 |

## 其他已登记定理

这些声明是已经登记的辅助执行结果、引理或见证。
它们不是额外的固定目标，也不能单凭这些声明就为调用者标记某种输入覆盖状态。

| 声明 | 被固定目标的证明使用 |
| --- | --- |
| [Zlib.Adler32.Proofs.adler32_combine64_safe](../ZlibF/Proof/adler32.c.lean#L977) | 未记录到固定目标的组合关系 |
| [Zlib.Adler32.Proofs.adler32_combine_c_safe](../ZlibF/Proof/adler32.c.lean#L982) | [adler32_combine](#target-zlibf-spec-public-goal-adler32-combine), [adler32_combine64](#target-zlibf-spec-public-goal-adler32-combine64) |
| [Zlib.Adler32.Proofs.adler32_combine_correct](../ZlibF/Proof/adler32.c.lean#L953) | 未记录到固定目标的组合关系 |
| [Zlib.Adler32.Proofs.adler32_combine_safe](../ZlibF/Proof/adler32.c.lean#L941) | [adler32_combine](#target-zlibf-spec-public-goal-adler32-combine), [adler32_combine64](#target-zlibf-spec-public-goal-adler32-combine64) |
| [Zlib.Adler32.Proofs.adler32_safe](../ZlibF/Proof/adler32.c.lean#L987) | 未记录到固定目标的组合关系 |
| [Zlib.Adler32.Proofs.adler32_z_correct](../ZlibF/Proof/adler32.c.lean#L786) | 未记录到固定目标的组合关系 |
| [Zlib.Adler32.Proofs.adler32_z_correct_ne_one](../ZlibF/Proof/adler32.c.lean#L798) | 未记录到固定目标的组合关系 |
| [Zlib.Adler32.Proofs.adler32_z_safe](../ZlibF/Proof/adler32.c.lean#L809) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.addrOf_safe](../ZlibF/Proof/crc32.c.lean#L2471) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.blockLittle_safe](../ZlibF/Proof/crc32.c.lean#L2465) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.braidTab_safe](../ZlibF/Proof/crc32.c.lean#L2461) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_combine64_correct](../ZlibF/Proof/crc32.c.lean#L2384) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_combine64_safe](../ZlibF/Proof/crc32.c.lean#L2378) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_combine_correct](../ZlibF/Proof/crc32.c.lean#L2399) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_combine_gen64_correct](../ZlibF/Proof/crc32.c.lean#L2334) | [crc32_combine_gen](#target-zlibf-spec-public-goal-crc32-combine-gen), [crc32_combine_gen64](#target-zlibf-spec-public-goal-crc32-combine-gen64), [crc32_combine_op](#target-zlibf-spec-public-goal-crc32-combine-op) |
| [Zlib.Crc32.Proofs.crc32_combine_gen64_safe](../ZlibF/Proof/crc32.c.lean#L2324) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_combine_gen_correct](../ZlibF/Proof/crc32.c.lean#L2353) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_combine_gen_safe](../ZlibF/Proof/crc32.c.lean#L2347) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_combine_op_correct](../ZlibF/Proof/crc32.c.lean#L2407) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_combine_op_diverges](../ZlibF/Proof/crc32.c.lean#L2372) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_combine_op_safe](../ZlibF/Proof/crc32.c.lean#L2363) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_combine_safe](../ZlibF/Proof/crc32.c.lean#L2394) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_correct](../ZlibF/Proof/crc32.c.lean#L2227) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Crc32.Proofs.crc32_null](../ZlibF/Proof/crc32.c.lean#L2223) | [crc32](#target-zlibf-spec-public-goal-crc32), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Crc32.Proofs.crc32_safe](../ZlibF/Proof/crc32.c.lean#L2236) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_z_correct](../ZlibF/Proof/crc32.c.lean#L2203) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Crc32.Proofs.crc32_z_null](../ZlibF/Proof/crc32.c.lean#L2190) | [crc32](#target-zlibf-spec-public-goal-crc32), [crc32_z](#target-zlibf-spec-public-goal-crc32-z), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Crc32.Proofs.crc32_z_safe](../ZlibF/Proof/crc32.c.lean#L2217) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crcByte_safe](../ZlibF/Proof/crc32.c.lean#L2449) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crcTab_safe](../ZlibF/Proof/crc32.c.lean#L2440) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc_word_big_safe](../ZlibF/Proof/crc32.c.lean#L2489) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc_word_correct](../ZlibF/Proof/crc32.c.lean#L2423) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc_word_safe](../ZlibF/Proof/crc32.c.lean#L2418) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.get_crc_table_correct](../ZlibF/Proof/crc32.c.lean#L2249) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.get_crc_table_safe](../ZlibF/Proof/crc32.c.lean#L2244) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.loadWord_safe](../ZlibF/Proof/crc32.c.lean#L2435) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.multmodp_correct](../ZlibF/Proof/crc32.c.lean#L2283) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.multmodp_diverges](../ZlibF/Proof/crc32.c.lean#L986) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.multmodp_safe](../ZlibF/Proof/crc32.c.lean#L2276) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.shr64_safe](../ZlibF/Proof/crc32.c.lean#L2475) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.wordAt_safe](../ZlibF/Proof/crc32.c.lean#L2456) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.x2nTab_safe](../ZlibF/Proof/crc32.c.lean#L2444) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.x2nmodp_correct](../ZlibF/Proof/crc32.c.lean#L2307) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.x2nmodp_safe](../ZlibF/Proof/crc32.c.lean#L2299) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.cleanup](../ZlibF/Proof/deflate.c.engine.common-initialized-history-environment.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.completed](../ZlibF/Proof/deflate.c.engine.common-initialized-data-history.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.completes](../ZlibF/Proof/deflate.c.engine.common-initialized-history-completes.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.completes_post](../ZlibF/Proof/deflate.c.engine.common-initialized-history-completes.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.encoding](../ZlibF/Proof/deflate.c.engine.common-initialized-data-history.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.environment](../ZlibF/Proof/deflate.c.engine.common-initialized-history-environment.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.finish_continuation](../ZlibF/Proof/deflate.c.engine.common-initialized-history-completes.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedEncodingState.ordinary_encoding_request](../ZlibF/Proof/deflate.c.engine.common-initialized-request.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonNoFlushDataTrace.cleanup](../ZlibF/Proof/deflate.c.engine.common-no-flush-history-environment.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonNoFlushDataTrace.completed](../ZlibF/Proof/deflate.c.engine.common-no-flush-data-history.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonNoFlushDataTrace.completes](../ZlibF/Proof/deflate.c.engine.common-no-flush-history-completes.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonNoFlushDataTrace.encoding](../ZlibF/Proof/deflate.c.engine.common-no-flush-data-history.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonNoFlushDataTrace.environment](../ZlibF/Proof/deflate.c.engine.common-no-flush-history-environment.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonNoFlushDataTrace.finish_continuation](../ZlibF/Proof/deflate.c.engine.common-no-flush-history-completes.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonOrdinaryDataTrace.cleanup](../ZlibF/Proof/deflate.c.engine.common-ordinary-history-environment.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonOrdinaryDataTrace.completed](../ZlibF/Proof/deflate.c.engine.common-ordinary-data-history.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonOrdinaryDataTrace.completes](../ZlibF/Proof/deflate.c.engine.common-ordinary-history-completes.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonOrdinaryDataTrace.encoding](../ZlibF/Proof/deflate.c.engine.common-ordinary-data-history.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonOrdinaryDataTrace.environment](../ZlibF/Proof/deflate.c.engine.common-ordinary-history-environment.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonOrdinaryDataTrace.finish_continuation](../ZlibF/Proof/deflate.c.engine.common-ordinary-history-completes.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.DefaultEncodingState.generic_basic_full_request](../ZlibF/Proof/deflate.c.engine.generic-basic-full-contract.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.DefaultFinishBoundary.follow_finish_continuation_end_status](../ZlibF/Proof/deflate.c.engine.generic-continuation-end-status.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.GenericDefaultRequestTrace.completes_with_original_birth_cleanup](../ZlibF/Proof/deflate.c.engine.generic-completion-lifetime.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.GenericDefaultRequestTrace.full_next_request_contract](../ZlibF/Proof/deflate.c.engine.generic-basic-history-full-contract.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.INSERT_STRING_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L177) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.UPDATE_HASH_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L147) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.chain_ok_of_chains](../ZlibF/Proof/deflate.c.engine.chains.lean#L194) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.chains_insert](../ZlibF/Proof/deflate.c.engine.chains.lean#L76) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.chains_slide](../ZlibF/Proof/deflate.c.engine.chains.lean#L138) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.common_initialized_level_four_complete_witness](../ZlibF/Proof/deflate.c.engine.common-initialized-data-history.lean#L93) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.common_no_flush_level_four_complete_witness](../ZlibF/Proof/deflate.c.engine.common-no-flush-history-witness.lean#L41) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.common_observed_initialization_encoding_state](../ZlibF/Proof/deflate.c.engine.common-initialized-state-init.lean#L15) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.common_observed_initialization_first_ordinary_encoding](../ZlibF/Proof/deflate.c.engine.common-initial-first-ordinary-encoding.lean#L15) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.common_observed_initialization_no_flush_encoding](../ZlibF/Proof/deflate.c.engine.common-initial-no-flush-encoding.lean#L14) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.common_ordinary_level_four_complete_witness](../ZlibF/Proof/deflate.c.engine.common-ordinary-history-witness.lean#L50) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.default_init_all_scalar_full_request_contract](../ZlibF/Proof/deflate.c.engine.all-scalar-full-contract.lean#L14) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.default_public_full_contract_witness](../ZlibF/Proof/deflate.c.engine.full-contract-witness.lean#L15) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.fill_fit](../ZlibF/Proof/deflate.c.engine.window.lean#L45) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.fill_post_room](../ZlibF/Proof/deflate.c.engine.window.lean#L40) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.form_init](../ZlibF/Proof/deflate.c.engine.hash.lean#L126) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.generic_default_public_contract](../ZlibF/Proof/deflate.c.default-public-contract.lean#L19) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.generic_default_request_trace_witness](../ZlibF/Proof/deflate.c.default-public-contract.lean#L62) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.header_ref_bound_128w](../ZlibF/Proof/deflate.c.engine.overlay-header-ref.lean#L290) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.header_ref_bound_256](../ZlibF/Proof/deflate.c.engine.overlay-header-ref.lean#L245) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.hkey_third](../ZlibF/Proof/deflate.c.engine.hash.lean#L139) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.lm_body_ok](../ZlibF/Proof/deflate.c.engine.lmbody.lean#L102) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.lm_inner_loop](../ZlibF/Proof/deflate.c.engine.lminner.lean#L114) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.lm_loop_ok](../ZlibF/Proof/deflate.c.engine.lmmain.lean#L77) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.longest_match_ok](../ZlibF/Proof/deflate.c.engine.lmmain.lean#L212) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.matchLen_agree](../ZlibF/Proof/deflate.c.engine.match.lean#L100) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.memory_fast_initialization_witness](../ZlibF/Proof/deflate.c.engine.memory-fast-initial.lean#L51) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.memory_fast_observed_initialization](../ZlibF/Proof/deflate.c.engine.memory-fast-observed-initial.lean#L49) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.memory_slow_initialized_state](../ZlibF/Proof/deflate.c.engine.memory-slow-initialized-state.lean#L62) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.memory_slow_observed_initialization](../ZlibF/Proof/deflate.c.engine.memory-slow-observed-initial.lean#L55) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.public_common_first_finish_encoding_input](../ZlibF/Proof/deflate.c.engine.common-first-finish-encoding.lean#L16) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.public_common_first_finish_encoding_state](../ZlibF/Proof/deflate.c.engine.common-first-finish-state.lean#L15) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.public_common_first_no_flush_encoding_input](../ZlibF/Proof/deflate.c.engine.common-first-input.lean#L16) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.public_common_first_no_flush_encoding_state](../ZlibF/Proof/deflate.c.engine.common-first-encoding-state.lean#L14) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.putShortMSB_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L119) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.put_byte_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L96) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.read_buf_ok](../ZlibF/Proof/deflate.c.engine.readbuf.lean#L99) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.read_buf_zero](../ZlibF/Proof/deflate.c.engine.readbuf.lean#L75) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.slide_copy](../ZlibF/Proof/deflate.c.engine.window.lean#L52) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.slide_hash_ok](../ZlibF/Proof/deflate.c.engine.slide.lean#L166) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.tinyOverlay](../ZlibF/Proof/deflate.c.engine.overlay-header-ref.lean#L352) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.tinyOverlayAt_128](../ZlibF/Proof/deflate.c.engine.overlay-header-ref.lean#L347) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.tinyOverlayAt_256](../ZlibF/Proof/deflate.c.engine.overlay-header-ref.lean#L342) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.upd3_indep](../ZlibF/Proof/deflate.c.engine.hash.lean#L45) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Proofs.MemoryInit.public_valid_memory_init_lifecycle](../ZlibF/Proof/deflate.c.init.memory-lifecycle.lean#L13) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.MemoryInit.public_valid_memory_init_total](../ZlibF/Proof/deflate.c.init.memory-total.lean#L16) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.deflateBound_nostate](../ZlibF/Proof/deflate.c.life.bound.lean#L330) | [deflateBound_safety](#target-zlibf-spec-public-goal-deflatebound-safety) |
| [Zlib.Deflate.Proofs.deflateBound_safe](../ZlibF/Proof/deflate.c.life.bound.lean#L319) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Proofs.deflateBound_z_nostate](../ZlibF/Proof/deflate.c.life.bound.lean#L312) | [deflateBound_safety](#target-zlibf-spec-public-goal-deflatebound-safety), [deflateBound_z_safety](#target-zlibf-spec-public-goal-deflatebound-z-safety) |
| [Zlib.Deflate.Proofs.deflateBound_z_safe](../ZlibF/Proof/deflate.c.life.bound.lean#L302) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Proofs.deflateEnd_reject](../ZlibF/Proof/deflate.c.life.end.lean#L321) | [deflateEnd_safety](#target-zlibf-spec-public-goal-deflateend-safety) |
| [Zlib.Deflate.Proofs.deflateEnd_safe](../ZlibF/Proof/deflate.c.life.end.lean#L270) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflateEnd](#target-zlibf-spec-public-goal-deflateend), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Proofs.deflateGetDictionary_reject](../ZlibF/Proof/deflate.c.life.getdict.lean#L202) | [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) |
| [Zlib.Deflate.Proofs.deflatePending_reject](../ZlibF/Proof/deflate.c.life.check.lean#L173) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.deflatePending_safe](../ZlibF/Proof/deflate.c.life.check.lean#L146) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.deflatePrime_invalid_count](../ZlibF/Proof/deflate.c.prime.lean#L24) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Proofs.deflatePrime_refused](../ZlibF/Proof/deflate.c.prime.lean#L15) | [deflatePrime_safety](#target-zlibf-spec-public-goal-deflateprime-safety) |
| [Zlib.Deflate.Proofs.deflateResetKeep_reject](../ZlibF/Proof/deflate.c.life.reset.lean#L424) | [deflateReset_safety](#target-zlibf-spec-public-goal-deflatereset-safety) |
| [Zlib.Deflate.Proofs.deflateResetKeep_safe](../ZlibF/Proof/deflate.c.life.reset.lean#L367) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflateReset](#target-zlibf-spec-public-goal-deflatereset), [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Proofs.deflateReset_reject](../ZlibF/Proof/deflate.c.life.reset.lean#L430) | [deflateReset_safety](#target-zlibf-spec-public-goal-deflatereset-safety) |
| [Zlib.Deflate.Proofs.deflateReset_safe](../ZlibF/Proof/deflate.c.life.reset.lean#L401) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflateReset](#target-zlibf-spec-public-goal-deflatereset), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Proofs.deflateSetHeader_not_gzip](../ZlibF/Proof/deflate.c.life.check.lean#L92) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.deflateSetHeader_reject](../ZlibF/Proof/deflate.c.life.check.lean#L98) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.deflateSetHeader_safe](../ZlibF/Proof/deflate.c.life.check.lean#L83) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Proofs.deflateStateCheck_total](../ZlibF/Proof/deflate.c.base.lean#L731) | [deflateBound_safety](#target-zlibf-spec-public-goal-deflatebound-safety), [deflateBound_z_safety](#target-zlibf-spec-public-goal-deflatebound-z-safety), [deflateEnd_safety](#target-zlibf-spec-public-goal-deflateend-safety), [deflatePending](#target-zlibf-spec-public-goal-deflatepending), [deflatePrime_safety](#target-zlibf-spec-public-goal-deflateprime-safety), [deflateReset_safety](#target-zlibf-spec-public-goal-deflatereset-safety), [deflateSetHeader](#target-zlibf-spec-public-goal-deflatesetheader), [deflateTune](#target-zlibf-spec-public-goal-deflatetune), [deflateUsed](#target-zlibf-spec-public-goal-deflateused), [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Proofs.deflateTune_reject](../ZlibF/Proof/deflate.c.life.check.lean#L54) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.deflateTune_safe](../ZlibF/Proof/deflate.c.life.check.lean#L44) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Proofs.deflateUsed_reject](../ZlibF/Proof/deflate.c.life.check.lean#L119) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.deflateUsed_safe](../ZlibF/Proof/deflate.c.life.check.lean#L113) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.lm_init_safe](../ZlibF/Proof/deflate.c.life.reset.lean#L151) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflateReset](#target-zlibf-spec-public-goal-deflatereset), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Universal.Call.flush_pending_cursor](../ZlibF/Proof/deflate.c.universal-flush-cursor.lean#L157) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Universal.copy_callfacts](../ZlibF/Proof/deflate.c.universal-ops-copy.lean#L868) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Universal.copy_header](../ZlibF/Proof/deflate.c.universal-ops-copy.lean#L857) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Universal.copy_inv](../ZlibF/Proof/deflate.c.universal-ops-copy.lean#L848) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Universal.prime_callfacts](../ZlibF/Proof/deflate.c.universal-ops-callfacts.lean#L99) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Universal.resetKeep_refuse](../ZlibF/Proof/deflate.c.universal-ops-resetkeep.lean#L64) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Universal.resetKeep_single](../ZlibF/Proof/deflate.c.universal-ops-resetkeep.lean#L31) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Universal.reset_callfacts](../ZlibF/Proof/deflate.c.universal-ops-callfacts.lean#L43) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Universal.setDictionary_callfacts](../ZlibF/Proof/deflate.c.universal-ops-dictionary-slid.lean#L158) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Universal.setDictionary_header](../ZlibF/Proof/deflate.c.universal-ops-dictionary-slid.lean#L135) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Universal.setHeader_callfacts](../ZlibF/Proof/deflate.c.universal-ops-callfacts.lean#L77) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Universal.step_prime](../ZlibF/Proof/deflate.c.universal-ops-prime.lean#L565) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Universal.step_reset](../ZlibF/Proof/deflate.c.universal-ops-reset.lean#L85) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Universal.step_setDictionary](../ZlibF/Proof/deflate.c.universal-ops-dictionary-slid.lean#L121) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Universal.tune_callfacts](../ZlibF/Proof/deflate.c.universal-ops-callfacts.lean#L64) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Gzclose.Proofs.gzclose_dispatch](../ZlibF/Proof/gzclose.c.lean#L22) | 未记录到固定目标的组合关系 |
| [Zlib.Gzclose.Proofs.gzclose_null](../ZlibF/Proof/gzclose.c.lean#L17) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.GT_OFF_run](../ZlibF/Proof/gzlib.c.simple.lean#L46) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Gzlib.Proofs.gz_error_null_run](../ZlibF/Proof/gzlib.c.error.lean#L134) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gz_intmax_run](../ZlibF/Proof/gzlib.c.simple.lean#L43) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gz_open_alloc_failure](../ZlibF/Proof/gzlib.c.open.lean#L36) | [gz_sequence_nonvacuity](#target-zlibf-spec-public-goal-gz-sequence-nonvacuity), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [gzdopen](#target-zlibf-spec-public-goal-gzdopen) |
| [Zlib.Gzlib.Proofs.gz_open_null](../ZlibF/Proof/gzlib.c.open.lean#L18) | [gz_sequence_nonvacuity](#target-zlibf-spec-public-goal-gz-sequence-nonvacuity), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [gzdopen](#target-zlibf-spec-public-goal-gzdopen) |
| [Zlib.Gzlib.Proofs.gz_reset_run](../ZlibF/Proof/gzlib.c.error.lean#L145) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gz_reset_safe](../ZlibF/Proof/gzlib.c.error.lean#L168) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzbuffer_null](../ZlibF/Proof/gzlib.c.simple.lean#L52) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzbuffer_run](../ZlibF/Proof/gzlib.c.simple.lean#L67) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzbuffer_safe](../ZlibF/Proof/gzlib.c.simple.lean#L84) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzclearerr_null](../ZlibF/Proof/gzlib.c.simple.lean#L191) | [gzclearerr](#target-zlibf-spec-public-goal-gzclearerr) |
| [Zlib.Gzlib.Proofs.gzclearerr_run](../ZlibF/Proof/gzlib.c.simple.lean#L199) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzclearerr_safe](../ZlibF/Proof/gzlib.c.simple.lean#L210) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzdopen_alloc_failure](../ZlibF/Proof/gzlib.c.open.lean#L62) | [gz_sequence_nonvacuity](#target-zlibf-spec-public-goal-gz-sequence-nonvacuity), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [gzdopen](#target-zlibf-spec-public-goal-gzdopen) |
| [Zlib.Gzlib.Proofs.gzdopen_joint_witness](../ZlibF/Proof/gzlib.c.dopen-joint-witness.lean#L92) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzdopen_negative](../ZlibF/Proof/gzlib.c.open.lean#L55) | [gz_sequence_nonvacuity](#target-zlibf-spec-public-goal-gz-sequence-nonvacuity), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [gzdopen](#target-zlibf-spec-public-goal-gzdopen) |
| [Zlib.Gzlib.Proofs.gzeof_null](../ZlibF/Proof/gzlib.c.simple.lean#L108) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzeof_run](../ZlibF/Proof/gzlib.c.simple.lean#L111) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzerror_null_file](../ZlibF/Proof/gzlib.c.simple.lean#L159) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzerror_run](../ZlibF/Proof/gzlib.c.simple.lean#L163) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzoffset64_null](../ZlibF/Proof/gzlib.c.rewind.lean#L103) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzoffset64_run](../ZlibF/Proof/gzlib.c.rewind.lean#L107) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzoffset_eq](../ZlibF/Proof/gzlib.c.rewind.lean#L129) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Gzlib.Proofs.gzopen64_alloc_failure](../ZlibF/Proof/gzlib.c.open.lean#L49) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzopen64_null](../ZlibF/Proof/gzlib.c.open.lean#L30) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzopen_alloc_failure](../ZlibF/Proof/gzlib.c.open.lean#L43) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzopen_null](../ZlibF/Proof/gzlib.c.open.lean#L25) | [gz_sequence_nonvacuity](#target-zlibf-spec-public-goal-gz-sequence-nonvacuity), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Gzlib.Proofs.gzrewind_null](../ZlibF/Proof/gzlib.c.rewind.lean#L73) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzrewind_spec](../ZlibF/Proof/gzlib.c.rewind.lean#L78) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzseek64_dangling_next_ok](../ZlibF/Proof/gzlib.c.seek.lean#L1053) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzseek64_head](../ZlibF/Proof/gzlib.c.seek.lean#L375) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Gzlib.Proofs.gzseek64_head_any](../ZlibF/Proof/gzlib.c.seek.lean#L232) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Gzlib.Proofs.gzseek64_null](../ZlibF/Proof/gzlib.c.seek.lean#L924) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzseek64_refuse](../ZlibF/Proof/gzlib.c.seek.lean#L956) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Gzlib.Proofs.gzseek64_safe](../ZlibF/Proof/gzlib.c.seek.lean#L931) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzseek64_set_negpos_refuse](../ZlibF/Proof/gzlib.c.seek.lean#L987) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzseek64_write_run](../ZlibF/Proof/gzlib.c.seek.lean#L388) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Gzlib.Proofs.gzseek_eq](../ZlibF/Proof/gzlib.c.seek.lean#L969) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Gzlib.Proofs.gztell64_null](../ZlibF/Proof/gzlib.c.simple.lean#L122) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gztell64_spec](../ZlibF/Proof/gzlib.c.simple.lean#L143) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gztell_null](../ZlibF/Proof/gzlib.c.simple.lean#L154) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gztell_run](../ZlibF/Proof/gzlib.c.simple.lean#L148) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.seekTail_back](../ZlibF/Proof/gzlib.c.seek.lean#L593) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Gzlib.Proofs.seekTail_copy](../ZlibF/Proof/gzlib.c.seek.lean#L429) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Gzlib.Proofs.seekTail_copy_ub](../ZlibF/Proof/gzlib.c.seek.lean#L1064) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.seekTail_fwd](../ZlibF/Proof/gzlib.c.seek.lean#L491) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Gzlib.Proofs.seekTail_fwd_empty](../ZlibF/Proof/gzlib.c.seek.lean#L1004) | 未记录到固定目标的组合关系 |
| [Zlib.Gzread.Proofs.gzclose_r_null](../ZlibF/Proof/gzread.c.close.lean#L44) | 未记录到固定目标的组合关系 |
| [Zlib.Gzread.Proofs.gzclose_r_unbuffered](../ZlibF/Proof/gzread.c.close.lean#L58) | 未记录到固定目标的组合关系 |
| [Zlib.Gzread.Proofs.gzclose_r_unbuffered_frame](../ZlibF/Proof/gzread.c.close.lean#L80) | 未记录到固定目标的组合关系 |
| [Zlib.Gzread.Proofs.gzclose_r_wrong_mode](../ZlibF/Proof/gzread.c.close.lean#L48) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Infback.Proofs.NEEDBITS_run](../ZlibF/Proof/infback.c.macros.lean#L240) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.PULLBYTE_run](../ZlibF/Proof/infback.c.macros.lean#L156) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.PULL_run](../ZlibF/Proof/infback.c.pull.lean#L16) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.ROOM_inv](../ZlibF/Proof/infback.c.stored.lean#L35) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.ROOM_run](../ZlibF/Proof/infback.c.room.lean#L27) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.TYPE_last](../ZlibF/Proof/infback.c.inv.lean#L87) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.TYPE_more](../ZlibF/Proof/infback.c.inv.lean#L145) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.backInit_witness](../ZlibF/Proof/infback.c.callbacks.lean#L143) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.badMode_run](../ZlibF/Proof/infback.c.inv.lean#L127) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [Zlib.Infback.Proofs.inFinite_eof](../ZlibF/Proof/infback.c.macros.lean#L304) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.inflateBackEnd_nullstream](../ZlibF/Proof/infback.c.end.lean#L23) | [inflateBackEnd](#target-zlibf-spec-public-goal-inflatebackend) |
| [Zlib.Infback.Proofs.inflateBackEnd_ok](../ZlibF/Proof/infback.c.end.lean#L35) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.inflateBackEnd_refused](../ZlibF/Proof/infback.c.end.lean#L27) | [inflateBackEnd](#target-zlibf-spec-public-goal-inflatebackend) |
| [Zlib.Infback.Proofs.inflateBackInit__nullstream](../ZlibF/Proof/infback.c.init.lean#L239) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.inflateBackInit__ok](../ZlibF/Proof/infback.c.init.lean#L147) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.inflateBackInit__safe](../ZlibF/Proof/infback.c.init.lean#L203) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.inflateBack_eof](../ZlibF/Proof/infback.c.back.lean#L134) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.inflateBack_eof_witness](../ZlibF/Proof/infback.c.back.lean#L175) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.inflateBack_nostate](../ZlibF/Proof/infback.c.back.lean#L124) | [inflateBack_safety](#target-zlibf-spec-public-goal-inflateback-safety) |
| [Zlib.Infback.Proofs.inflateBack_nullstream](../ZlibF/Proof/infback.c.back.lean#L119) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [Zlib.Infback.Proofs.order_inj](../ZlibF/Proof/infback.c.pure.lean#L17) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.order_lt](../ZlibF/Proof/infback.c.pure.lean#L14) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.order_surj](../ZlibF/Proof/infback.c.pure.lean#L21) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.storedTail_run](../ZlibF/Proof/infback.c.stored.lean#L125) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.stored_body_run](../ZlibF/Proof/infback.c.stored.lean#L285) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.stored_check](../ZlibF/Proof/infback.c.pure.lean#L35) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.stored_len_toNat](../ZlibF/Proof/infback.c.pure.lean#L58) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.stored_loop_run](../ZlibF/Proof/infback.c.stored.lean#L406) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.stored_run](../ZlibF/Proof/infback.c.stored.lean#L459) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.xwhileBrk_wf](../ZlibF/Proof/infback.c.wf.lean#L16) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [Zlib.Inffast.Proofs.distfix_tableSafe](../ZlibF/Proof/inffast.c.tableok.lean#L98) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inffast.Proofs.lenfix_tableSafe](../ZlibF/Proof/inffast.c.tableok.lean#L84) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.BITS_run](../ZlibF/Proof/inflate.c.main.macros.lean#L224) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.BITS_toNat](../ZlibF/Proof/inflate.c.main.macros.lean#L234) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.BYTEBITS_inv](../ZlibF/Proof/inflate.c.main.macros.lean#L293) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.BYTEBITS_run](../ZlibF/Proof/inflate.c.main.macros.lean#L283) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.DROPBITS_inv](../ZlibF/Proof/inflate.c.main.macros.lean#L251) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.DROPBITS_run](../ZlibF/Proof/inflate.c.main.macros.lean#L241) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.INITBITS_inv](../ZlibF/Proof/inflate.c.main.macros.lean#L304) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.NEEDBITS_run](../ZlibF/Proof/inflate.c.main.macros.lean#L150) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.PULLBYTE_succ](../ZlibF/Proof/inflate.c.main.macros.lean#L89) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.PULLBYTE_zero](../ZlibF/Proof/inflate.c.main.macros.lean#L44) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.UPDATE_CHECK_run](../ZlibF/Proof/inflate.c.main.check.lean#L21) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.bytesBits_eq_bytesToBits](../ZlibF/Proof/inflate.c.main.bits.lean#L107) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateCodesUsed_spec](../ZlibF/Proof/inflate.c.misc.lean#L180) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateEnd_safe](../ZlibF/Proof/inflate.c.end.lean#L119) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflateEnd](#target-zlibf-spec-public-goal-inflateend), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateGetDictionary_spec](../ZlibF/Proof/inflate.c.dict.lean#L82) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateGetHeader_check](../ZlibF/Proof/inflate.c.hdr.lean#L54) | [inflateGetHeader_safety](#target-zlibf-spec-public-goal-inflategetheader-safety) |
| [Zlib.Inflate.Proofs.inflateGetHeader_nogzip](../ZlibF/Proof/inflate.c.hdr.lean#L64) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateGetHeader_null_faults](../ZlibF/Proof/inflate.c.hdr.lean#L114) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateGetHeader_ok](../ZlibF/Proof/inflate.c.hdr.lean#L80) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateInit2_ok](../ZlibF/Proof/inflate.c.start.lean#L237) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2), [inflateInit_](#target-zlibf-spec-public-goal-inflateinit), [inflate_initialisation_domain](#target-zlibf-spec-public-goal-inflate-initialisation-domain), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateInit2_safe](../ZlibF/Proof/inflate.c.start.lean#L324) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateInit__ok](../ZlibF/Proof/inflate.c.hdr.lean#L160) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateInit__safe](../ZlibF/Proof/inflate.c.hdr.lean#L134) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateMark_spec](../ZlibF/Proof/inflate.c.misc.lean#L140) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflatePrime_spec](../ZlibF/Proof/inflate.c.misc2.lean#L28) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateReset2_safe](../ZlibF/Proof/inflate.c.init.lean#L395) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateResetKeep_safe](../ZlibF/Proof/inflate.c.base.lean#L521) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateReset_safe](../ZlibF/Proof/inflate.c.reset.lean#L160) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateSetDictionary_dataerr](../ZlibF/Proof/inflate.c.dict.lean#L222) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateSetDictionary_safe](../ZlibF/Proof/inflate.c.dict.lean#L146) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateSetDictionary_streamerr](../ZlibF/Proof/inflate.c.dict.lean#L209) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateStateCheck_total](../ZlibF/Proof/inflate.c.base.lean#L445) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflateCodesUsed](#target-zlibf-spec-public-goal-inflatecodesused), [inflateEnd](#target-zlibf-spec-public-goal-inflateend), [inflateGetHeader_safety](#target-zlibf-spec-public-goal-inflategetheader-safety), [inflateMark](#target-zlibf-spec-public-goal-inflatemark), [inflatePrime](#target-zlibf-spec-public-goal-inflateprime), [inflateSyncPoint](#target-zlibf-spec-public-goal-inflatesyncpoint), [inflateSync_safety](#target-zlibf-spec-public-goal-inflatesync-safety), [inflateUndermine](#target-zlibf-spec-public-goal-inflateundermine), [inflateValidate](#target-zlibf-spec-public-goal-inflatevalidate), [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateSyncPoint_spec](../ZlibF/Proof/inflate.c.misc.lean#L121) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateSync_buf_error](../ZlibF/Proof/inflate.c.sync2.lean#L131) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateSync_check](../ZlibF/Proof/inflate.c.sync2.lean#L113) | [inflateSync_safety](#target-zlibf-spec-public-goal-inflatesync-safety) |
| [Zlib.Inflate.Proofs.inflateUndermine_safe](../ZlibF/Proof/inflate.c.misc.lean#L109) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateValidate_safe](../ZlibF/Proof/inflate.c.misc.lean#L95) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_CHECK_nowrap](../ZlibF/Proof/inflate.c.main.check.lean#L137) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_CHECK_run](../ZlibF/Proof/inflate.c.main.check.lean#L157) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_COPY__eq](../ZlibF/Proof/inflate.c.main.stored2.lean#L82) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_COPY_done](../ZlibF/Proof/inflate.c.main.stored.lean#L22) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_COPY_leave](../ZlibF/Proof/inflate.c.main.stored2.lean#L75) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_COPY_run](../ZlibF/Proof/inflate.c.main.stored2.lean#L57) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_DONE_run](../ZlibF/Proof/inflate.c.main.simple.lean#L25) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_LENGTH_run](../ZlibF/Proof/inflate.c.main.check.lean#L80) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_LENGTH_skip](../ZlibF/Proof/inflate.c.main.check.lean#L66) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_LENLENS_eq](../ZlibF/Proof/inflate.c.main.table3.lean#L82) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_LENLENS_run](../ZlibF/Proof/inflate.c.main.table6.lean#L41) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_LIT_full](../ZlibF/Proof/inflate.c.main.simple.lean#L29) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_LIT_run](../ZlibF/Proof/inflate.c.main.simple.lean#L37) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_STORED_bad](../ZlibF/Proof/inflate.c.main.stored2.lean#L97) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_STORED_ok](../ZlibF/Proof/inflate.c.main.stored2.lean#L116) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_STORED_wait](../ZlibF/Proof/inflate.c.main.stored2.lean#L88) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_TABLE_run](../ZlibF/Proof/inflate.c.main.table.lean#L52) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_TYPEDO_head](../ZlibF/Proof/inflate.c.main.type.lean#L61) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_TYPEDO_last](../ZlibF/Proof/inflate.c.main.type.lean#L26) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_TYPEDO_wait](../ZlibF/Proof/inflate.c.main.type.lean#L37) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_TYPE_go](../ZlibF/Proof/inflate.c.main.type.lean#L19) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_TYPE_leave](../ZlibF/Proof/inflate.c.main.type.lean#L11) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.ll1_run](../ZlibF/Proof/inflate.c.main.table4.lean#L69) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.llBody_run](../ZlibF/Proof/inflate.c.main.table3.lean#L95) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.llTail_run](../ZlibF/Proof/inflate.c.main.table5.lean#L46) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.lzBody_run](../ZlibF/Proof/inflate.c.main.table4.lean#L225) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.lz_run](../ZlibF/Proof/inflate.c.main.table4.lean#L244) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.noRet_NEEDBITS](../ZlibF/Proof/inflate.c.main.table2.lean#L321) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.ring_spec](../ZlibF/Proof/inflate.c.ring.lean#L116) | [inflateSetDictionary](#target-zlibf-spec-public-goal-inflatesetdictionary) |
| [Zlib.Inflate.Proofs.syncDone_good](../ZlibF/Proof/inflate.c.sync2.lean#L372) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.syncDone_owns](../ZlibF/Proof/inflate.c.sync2.lean#L423) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.syncDone_run](../ZlibF/Proof/inflate.c.sync2.lean#L248) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.syncScan_found_iff](../ZlibF/Proof/inflate.c.sync.lean#L342) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.syncScan_spec](../ZlibF/Proof/inflate.c.sync.lean#L300) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.syncStep_spec](../ZlibF/Proof/inflate.c.sync.lean#L202) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.syncTail_run](../ZlibF/Proof/inflate.c.sync2.lean#L543) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.syncsearch_null](../ZlibF/Proof/inflate.c.sync.lean#L450) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [Zlib.Inflate.Proofs.syncsearch_run](../ZlibF/Proof/inflate.c.sync.lean#L381) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.syncsearch_spec](../ZlibF/Proof/inflate.c.sync.lean#L485) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.typedoTail_bad](../ZlibF/Proof/inflate.c.main.type.lean#L154) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.typedoTail_fixed](../ZlibF/Proof/inflate.c.main.type.lean#L116) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.typedoTail_fixed_trees](../ZlibF/Proof/inflate.c.main.type.lean#L132) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.typedoTail_stored](../ZlibF/Proof/inflate.c.main.type.lean#L92) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.typedoTail_table](../ZlibF/Proof/inflate.c.main.type.lean#L104) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.updatewindow_ring](../ZlibF/Proof/inflate.c.ring.lean#L197) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.updatewindow_safe](../ZlibF/Proof/inflate.c.uw.lean#L558) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.uwPost_counts](../ZlibF/Proof/inflate.c.ring.lean#L170) | [inflateSetDictionary](#target-zlibf-spec-public-goal-inflatesetdictionary) |
| [Zlib.Inflate.Proofs.uw_null_ok](../ZlibF/Proof/inflate.c.uw.lean#L492) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.uw_post](../ZlibF/Proof/inflate.c.uw.lean#L423) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.xwhileBrk_run](../ZlibF/Proof/inflate.c.main.xloop.lean#L36) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Witness.init_witness](../ZlibF/Proof/inflate.c.witness.lean#L50) | 未记录到固定目标的组合关系 |
| [Zlib.Inftrees.Proofs.Cover.bits_add_drop](../ZlibF/Proof/inftrees.c.cover.leaf.lean#L80) | 未记录到固定目标的组合关系 |
| [Zlib.Inftrees.Proofs.Cover.cell_lt_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L210) | 未记录到固定目标的组合关系 |
| [Zlib.Inftrees.Proofs.Cover.distLeaf_of](../ZlibF/Proof/inftrees.c.cover.leaf.lean#L56) | [decode_table_matches_format](#target-zlib-inftrees-spec-decodesemantics-goal-decode-table-matches-format), [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound), [constructor_establishes_query_stability](#target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability), [constructor_establishes_fast_leaf_flags](#target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags), [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inftrees.Proofs.Cover.group_cover](../ZlibF/Proof/inftrees.c.cover.group.lean#L64) | [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inftrees.Proofs.Cover.group_cover_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L163) | 未记录到固定目标的组合关系 |
| [Zlib.Inftrees.Proofs.Cover.group_cover_idx](../ZlibF/Proof/inftrees.c.cover.group.lean#L161) | [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inftrees.Proofs.Cover.group_cover_idx_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L185) | 未记录到固定目标的组合关系 |
| [Zlib.Inftrees.Proofs.Cover.invalid_leaf](../ZlibF/Proof/inftrees.c.cover.leaf.lean#L66) | [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inftrees.Proofs.Cover.lenLeaf_of](../ZlibF/Proof/inftrees.c.cover.leaf.lean#L40) | [decode_table_matches_format](#target-zlib-inftrees-spec-decodesemantics-goal-decode-table-matches-format), [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound), [constructor_establishes_query_stability](#target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability), [constructor_establishes_fast_leaf_flags](#target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags), [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inftrees.Proofs.Cover.root_cover](../ZlibF/Proof/inftrees.c.cover.root.lean#L90) | [decode_table_matches_format](#target-zlib-inftrees-spec-decodesemantics-goal-decode-table-matches-format), [short_decode_table_leaf_sound](#target-zlib-inftrees-spec-decodeshort-goal-short-decode-table-leaf-sound), [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound), [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant), [constructor_establishes_query_stability](#target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability), [constructor_establishes_fast_leaf_flags](#target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags), [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content), [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inftrees.Proofs.Cover.root_cover_complete_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L140) | [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inftrees.Proofs.Cover.root_cover_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L130) | 未记录到固定目标的组合关系 |
| [Zlib.Inftrees.Proofs.Cover.root_single_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L226) | 未记录到固定目标的组合关系 |
| [Zlib.Inftrees.Proofs.inflate_fixed_ok](../ZlibF/Proof/inftrees.c.fixed.lean#L21) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [Zlib.Inftrees.Proofs.inflate_table_correct_ret](../ZlibF/Proof/inftrees.c.lean#L65) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inftrees.Proofs.inflate_table_safe](../ZlibF/Proof/inftrees.c.lean#L34) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.GB.kraft_clamped](../ZlibF/Proof/trees.c.heap.gbtree.lean#L132) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Trees.Proofs.Out.bi_flush_spec](../ZlibF/Proof/trees.c.bits.lean#L548) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Trees.Proofs.Out.bi_reverse_correct](../ZlibF/Proof/trees.c.reverse.lean#L91) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Trees.Proofs.Out.bi_reverse_safe](../ZlibF/Proof/trees.c.reverse.lean#L51) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.Out.bi_windup_spec](../ZlibF/Proof/trees.c.bits.lean#L731) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Trees.Proofs.Out.init_block_spec](../ZlibF/Proof/trees.c.block.lean#L217) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.Out.init_block_spec0](../ZlibF/Proof/trees.c.block.lean#L102) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2), [deflateInit_](#target-zlibf-spec-public-goal-deflateinit), [deflateReset](#target-zlibf-spec-public-goal-deflatereset), [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep), [deflate_initialisation_domain](#target-zlibf-spec-public-goal-deflate-initialisation-domain), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Trees.Proofs.Out.send_bits_spec](../ZlibF/Proof/trees.c.bits.lean#L411) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Trees.Proofs.Out.tr_align_emit](../ZlibF/Proof/trees.c.align.lean#L42) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Trees.Proofs.Out.tr_flush_bits_emit](../ZlibF/Proof/trees.c.align.lean#L30) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.Out.tr_init_spec](../ZlibF/Proof/trees.c.block.lean#L245) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflateInit_](#target-zlibf-spec-public-goal-deflateinit), [deflateReset](#target-zlibf-spec-public-goal-deflatereset), [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Trees.Proofs.Out.tr_tally_spec](../ZlibF/Proof/trees.c.tally.lean#L327) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.gen_bitlen_correct](../ZlibF/Proof/trees.c.heap.gbtop.lean#L403) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.gen_bitlen_safe](../ZlibF/Proof/trees.c.heap.gbtop.lean#L421) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.pqdownheap_correct](../ZlibF/Proof/trees.c.heap.pqrun.lean#L313) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.pqdownheap_safe](../ZlibF/Proof/trees.c.heap.pqrun.lean#L330) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.pqremove_correct](../ZlibF/Proof/trees.c.heap.pqrun.lean#L342) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.pqremove_safe](../ZlibF/Proof/trees.c.heap.pqrun.lean#L359) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zError_correct](../ZlibF/Proof/zutil.c.lean#L125) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zError_safe](../ZlibF/Proof/zutil.c.lean#L117) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zcalloc_correct_none](../ZlibF/Proof/zutil.c.lean#L271) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zcalloc_correct_size](../ZlibF/Proof/zutil.c.lean#L262) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zcalloc_correct_some](../ZlibF/Proof/zutil.c.lean#L248) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zcalloc_safe](../ZlibF/Proof/zutil.c.lean#L234) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zcalloc_zcfree_no_leak](../ZlibF/Proof/zutil.c.lean#L316) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zcfree_correct](../ZlibF/Proof/zutil.c.lean#L290) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zcfree_correct_null](../ZlibF/Proof/zutil.c.lean#L308) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zcfree_safe](../ZlibF/Proof/zutil.c.lean#L280) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zlibCompileFlags_correct](../ZlibF/Proof/zutil.c.lean#L175) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zlibCompileFlags_safe](../ZlibF/Proof/zutil.c.lean#L169) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zlibVersion_correct](../ZlibF/Proof/zutil.c.lean#L159) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zlibVersion_safe](../ZlibF/Proof/zutil.c.lean#L134) | 未记录到固定目标的组合关系 |
| [ZlibF.Spec.Api.Proofs.Layer.ext](../ZlibF/Proof/Format/Api.lean) | [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Api.Proofs.inflate_deferred_distance_rejects_legacy_consistency](../ZlibF/Proof/Api/InflateCausality.lean#L229) | 未记录到固定目标的组合关系 |
| [ZlibF.Spec.Blocks.append](../ZlibF/Proof/Format/Deflate.lean) | [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Blocks.det](../ZlibF/Proof/Format/Deflate.lean) | [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Gzip.ext](../ZlibF/Proof/Format/Wrapper.lean) | [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Prefix.det](../ZlibF/Proof/Format/Deflate.lean) | 未记录到固定目标的组合关系 |
| [ZlibF.Spec.Prefix.ext](../ZlibF/Proof/Format/Deflate.lean) | [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Proofs.prefixFree](../ZlibF/Proof/Format/Huffman.lean#L105) | [short_decode_table_leaf_sound](#target-zlib-inftrees-spec-decodeshort-goal-short-decode-table-leaf-sound), [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound), [constructor_establishes_query_stability](#target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability), [short_rejected_leaf_stays_invalid](#target-zlib-inftrees-spec-decodetablestability-goal-short-rejected-leaf-stays-invalid), [constructor_establishes_fast_leaf_flags](#target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags), [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance), [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [ZlibF.Spec.Public.Proofs.DeflateCore.completes](../ZlibF/Proof/deflate.c.default-core-completes.lean#L89) | 未记录到固定目标的组合关系 |
| [ZlibF.Spec.Public.Proofs.DeflateCore.correct](../ZlibF/Proof/deflate.c.default-core-completes.lean#L140) | 未记录到固定目标的组合关系 |
| [ZlibF.Spec.Public.Proofs.DeflateCore.safe_encoding_and_cleanup](../ZlibF/Proof/deflate.c.default-core.lean#L182) | 未记录到固定目标的组合关系 |
| [ZlibF.Spec.Public.Proofs.DeflateInit.default_init_witness](../ZlibF/Proof/public-deflate-init.lean#L283) | 未记录到固定目标的组合关系 |
| [ZlibF.Spec.Public.Proofs.free_writable_matches_dropWindow](../ZlibF/Proof/Api/HeapCleanup.lean#L56) | 未记录到固定目标的组合关系 |
| [ZlibF.Spec.Public.Proofs.legacy_codes_used_impossible](../ZlibF/Proof/Api/QueryLayout.lean#L125) | 未记录到固定目标的组合关系 |
| [ZlibF.Spec.Zlib.ext](../ZlibF/Proof/Format/Wrapper.lean) | [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |

## 更新记录

证明或登记表发生变化后，需要重新生成本页。生成过程会编译并检查
定理的精确类型，不会修改证明、目标或登记表。生成器同时写出英文页和本页。
结果是否通过项目验收，仍须依据[检查规则](checking/README.md)。
只有当本页展示的内容发生变化时（目标、登记、证明状态、链接或行锚点），本页才算过期。在此之前，
链接保持生成时的修订版本。
<!-- proof-progress:end -->

## 剩余工作

98 个必需目标都已登记；每项结论的层级和各次验收运行见[范围](#scope)。没有任何目标存在记录在案的阻碍。剩下的工作列在[按顺序的下一步工作](#ordered-next-work)中。

以下各节只保留事实和未完成的事项。已经结束的工作记录原样保存在 `docs/history/` 下；其中的状态、工时和数字描述的是写作当时的情况：

- 证明骨架：[inflate](history/skeleton-inflate.md)、[deflate](history/skeleton-deflate.md)、[gz](history/skeleton-gz.md)、[inflateBack](history/skeleton-inflate-back.md)。
- [早先的工作顺序与准备情况说明](history/next-work-and-readiness.md)。
- [规格审查记录](history/specification-review.md)。
- [覆盖情况：审查记录](history/coverage-review-record.md)和[覆盖情况：早先的未完成事项](history/coverage-open-items.md)。
- [进度检查点](history/progress-checkpoints.md)和[总览变更记录](history/overview-changelog.md)：更早的叙述性记录。

### 核心证明骨架

骨架是一项核心证明自顶向下的计划：用一组具名引理证明目标，引理本身的证明先在一个分支上空着。所有骨架都已完成。它们各自针对的目标都已登记，所以必需目标所需要的引理没有一条还空着。引理表、途中对命题所作的更正和工作记录都属于历史。

| 骨架 | 它完成的目标（均已登记） | 分支 | 记录 |
| --- | --- | --- | --- |
| inflate | `Goal.inflate`、`Goal.inflate_sequence_safety`、`Goal.uncompress*_safe` | `skeleton/inflate` | [inflate 骨架](history/skeleton-inflate.md) |
| deflate | `Goal.deflateInit2_`、`Goal.deflate`、`Goal.deflate_sequence_safety`、`Goal.compress*_safety` | `skeleton/deflate` | [deflate 骨架](history/skeleton-deflate.md) |
| gz | `Goal.gz_sequence_safety`、`Goal.gz_sequence_nonvacuity`、`Goal.gz_refusal` | `skeleton/gz` | [gz 骨架](history/skeleton-gz.md) |
| inflateBack | `Goal.inflate_back_sequence_safety` | `skeleton/inflate-back` | [inflateBack 骨架](history/skeleton-inflate-back.md) |

归档的表格里仍有一些行写着“未完成”。必需目标都不需要它们：

- 功能性的行：inflate 的格式含义、deflate 的账本、`completes` 和 `bound_before_output`。哪些功能性工作在计划内，见[范围](#scope)。
- 清理类的行，是可选的，是否已经做完没有确认：删除没有任何已登记定理使用的 inflate 快速路径证明和固定配置证明，合并 `deflate.c.quiet-*` 中重述的副本。
- gz 的辅助行：循环规则 `gwhile_partial` 和 `gdoWhile_partial`，以及内部读取辅助引理（`gz_load_safe` 到 `gz_skip_safe`）与骨架文本的对齐。目标是用 `dev` 上的辅助命题证明的，这两者都用不着。
- 归档的 deflate 表“尚未完成的工作”为策略导出、`step_params` 和 `deflate` 的 `HeaderInv` 引理列着工时。`Goal.deflate_sequence_safety` 登记之后，这些行里哪些已经证明、哪些不再需要，归档里没有记录。

### zlib.h 函数的无故障覆盖

“`zlib.h` 中每个有文档的函数一行”的那张表，现在单独成页：[按函数查覆盖情况](coverage.md)。每行写明安全目标、类型就是该目标的已登记定理、证明文件、定义域，以及覆盖 `NULL` 流或不一致的流的定理。功能定理另占一列。

每个有文档的函数，都在其所在行写明的定义域上有一条已登记的安全定理。有三类事项尚未完成，或比 `zlib.h` 更窄：

1. **拒绝子句。** 这里没有未完成的事项。对 `NULL` 流或不一致的流的拒绝，是除四个初始化函数之外每个流函数的安全目标的子句，也是两个复制目标的子句（提交 `71188823`）。拒绝的定义域所不包括的情形，只在[偏离记录，注 2](deviations.md#note-2-refused-streams)所说的意义上比 `zlib.h` 更窄：分配器已设置、而 `state` 指针是垃圾指针、悬空指针或属于另一种流的记录。这些目标的层级见[范围](#scope)。
2. **比 `zlib.h` 更窄的定义域**，每一条在[偏离记录](deviations.md)中都有对应的行：`inflateBack`（`inputBound < 2^48`；窗口和每个输入片段都在堆字节块中）；`inflateCopy` 与 `deflateCopy`（`source ≠ dest`）；`adler32` 与 `adler32_z`（只有 `len = 0` 时 `buf` 才可以是 `NULL`：`len = 1` 是 C 中真实的故障，`buf` 为 `NULL` 且 `len ≥ 2` 在 C 中安全，但没有证明）。
3. **作为值传递的结果单元。** 有八个公开函数的翻译把一个标量输出参数当作值接收，并把写入的值作为另一个结果返回：`compress`、`compress2` 及其 `_z` 形式的 `destLen`；`inflateGetDictionary` 和 `deflateGetDictionary` 的 `dictLength`；`deflatePending` 的 `pending` 和 `bits`；`deflateUsed` 的 `bits`。因此这些函数的安全目标对结果单元的内存什么都没说（[偏离记录](deviations.md#stream-calls-inflate-and-deflate)的“结果单元”和“整缓冲区压缩”两行）。工作规则只对内部函数的输出参数采纳这种表示。这些翻译是否改为像 `uncompress*` 和 `gzerror` 那样把单元当作内存，所有者尚未决定。

`deflateParams`、`deflateSetDictionary`、`deflatePrime`、`deflateBound`、`deflateBound_z` 和 `inflateSync` 的功能目标没有定理，也不在计划内。它们的安全目标已登记。

### 按顺序的下一步工作

每个必需目标都已登记：98 个安全目标和非空性目标，没有未完成的（`tests/audit/public-api.json`）。验收套件在哪个提交上全部通过、此后有什么变化，见[范围](#scope)。剩下的工作按顺序是：

1. **验收** `bde170e9` 之后登记或改动的目标：gz 函数和回调解码器的 35 个单函数安全目标、范围扩大后的初始化目标、回调解码器序列目标的现行形式，以及带拒绝子句的 25 个流目标和复制目标（第 2 项）。它们已经登记，只差验收套件在某个具名提交上全部通过：公理关卡、精确目标匹配、自测和差分测试。这不需要变异体运行。那个提交记入[范围](#next-acceptance-run)。
2. **拒绝子句。** 命题和证明已经完成：23 个单函数流安全目标和两个复制目标都陈述了拒绝（[覆盖情况](#no-fault-coverage-of-zlibh-functions)第 1 条）。它们的定理沿用已登记的名字。对它们来说，剩下的是第 1 项的验收运行。
3. **默认 zlib 流的往返**，排在安全结论之后（[范围](#scope)）。
4. **把本地补丁提交上游**：0004 和 0005（[补丁](../patches/README.md)）。补丁 0001 至 0003 与已经提交上游的拉取请求一致。
5. **尚未结束的审查和决定**：[翻译审查](#translation-review)、[待复查的历史报告](#historical-reports-to-recheck)，以及所有者对八个公开函数结果单元的决定（[覆盖情况](#no-fault-coverage-of-zlibh-functions)第 3 条）。
6. **可选的清理**：删除没有任何已登记定理使用的证明（[核心证明骨架](#core-proof-skeletons)）。

[范围](#scope)列为不在计划内的各组不投入工作。早先的有序工作表（13 行，每一行不是已登记就是不在计划内）见[早先的工作顺序](history/next-work-and-readiness.md)。

### 公开 API 的证明准备情况

生成的索引把每个未登记的公开目标链接到下表中的一行。生成器要读这张表，所以表中的标签和锚点保持不变。表中的每个目标都是功能目标：未证明，也不在计划内（见[范围](#scope)）。同一批函数的安全性已经登记（[按函数查覆盖情况](coverage.md)）。

表中的说明写的是：证明这个功能目标需要什么。其中大多数写于功能正确性还是计划内结论的时候，每一条与确切目标是否相符都**尚未由证明确认**。它们不是工作计划。任何一行都不授予“已检查”状态，也不假设被调用函数的规格。

本节早先的内容已归入历史：已经停止的、按位置表述的哈希链工作（[deflate 骨架](history/skeleton-deflate.md)）、inflateBack 的引理表（[inflateBack 骨架](history/skeleton-inflate-back.md)），以及打开、查询与关闭操作的前置事项和后来已登记目标的各行（[准备情况说明](history/next-work-and-readiness.md)）。

#### 每个未完成公开目标的下一步

“开始”表示不必等待完整的引擎定理就能着手的工作。“组合”指出彻底完成目标所需的前置事项。

<!-- proof-readiness:start -->
| 公开目标 | 图中所示证明工作 | 下一步与缺少的前置事项 |
| --- | --- | --- |
| `gzopen`, `gzopen64`, `gz_initialisation_domain` | 开始：打开与清理 | <a id="readiness-gzopen"></a> **命题已更正：**见 [gzip 打开路径长度](history/specification-review.md#gzip-open-path-length)。**开始：**`gz_open` 按路径打开的分支（`fsOpen` 的各种结果、追加定位和读取定位），复用已登记的 `gzdopen` 模式循环、分配和 `OpenState` 的组合。入口分支和失败分支已在上文经过本地检查。 |
| `gztell64`, `gztell` | 需要：位置约束 | <a id="readiness-gztell64"></a> **组合：**从读取、写入、定位和字节回退推出 `PosInv`，再复用现有的算术执行证明。 |
| `gzclose_r` | 需要：资源归属 | <a id="readiness-gzclose-r"></a> **开始：**已初始化缓冲区的清理，以及在历史上建立其所有权的证明。无缓冲的执行和帧性质已经过本地检查；单有 `inflateEnd` 还不够。 |
| `gzclose_w`, `gzclose` | 需要：交付与清理 | <a id="readiness-gzclose-w"></a> **组合：**实际的补零、最终压缩和文件写入，所有清理路径和错误路径，然后用两个完整的关闭结果完成分派。 |
| `gzseek64`, `gzseek` | 需要：定位与状态序列 | <a id="readiness-gzseek64"></a> **开始：**位置与指针的历史不变量、有缓冲的路径和透明路径、精确的错误帧性质。负位置的可达性和历史上的溢出报告**尚未由证明确认**。 |
| `gzdirect`, `gzread`, `gzfread`, `gzgetc`, `gzgetc_`, `gzgets`, `gzungetc` | 需要：读取路径证明 | <a id="readiness-gzdirect"></a> **开始：**公共的延迟准备、透明读取，以及缓冲区与历史不变量。**组合：**压缩路径上实际的解码器执行，然后是 EOF、计数、字节回退和错误各子句。`gzdirect` 需要格式探测和初始化，不需要完整的数据解码循环。 |
| `gzwrite`, `gzfwrite`, `gzputc`, `gzputs`, `gzvprintf`, `gzprintf`, `gzflush`, `gzsetparams` | 需要：写入路径证明 | <a id="readiness-gzwrite"></a> **开始：**缓冲、格式化、透明写入和各种失败。**组合：**压缩输出和参数变更中实际的压缩器执行。 |
| `deflatePrime` | 开始：压紧与位操作 | <a id="readiness-deflateprime"></a> **开始：**待输出字节的紧缩、带检查的移位、位的插入与刷新，以及不变量和帧性质的保持。拒绝分支已经过本地检查；被接受的位数情形仍未完成。 |
| `deflateBound_z`, `deflateBound` | 开始：上界与头部审查 | <a id="readiness-deflatebound-z"></a> **开始：**把现有的执行公式与带饱和的数学上界联系起来，包括头部字符串和 extra 字段长度。extra 字段长度的报告已在固定的 C 上复现：`extra_len` 为 `2^32 - 2` 或 `2^32 - 1` 时，C 按 32 位计算 `2 + extra_len` 并发生回绕，而关于数值的目标照现在的写法没有回绕（[发现](findings/deflatebound-extra-len/README.md)）。开始证明之前，这两个目标的命题需要先更正。 |
| `deflateSetDictionary` | 开始：窗口与哈希 | <a id="readiness-deflatesetdictionary"></a> **开始：**填充窗口、插入哈希链、恢复保存的输入，然后是校验和以及精确的状态效果和帧效果。已通过检查的校验和调用只覆盖校验和这一部分。 |
| `deflateParams` | 需要：块交付与参数状态 | <a id="readiness-deflateparams"></a> **组合：**实际刷新旧块、处理返回码，以及更新规范的调参表行。在彻底完成之前，先核对拒绝时状态是否原样保持。 |
| `inflateSync` | 需要：扫描与状态序列 | <a id="readiness-inflatesync"></a> **开始：**组合现有的首次扫描与恢复扫描、暂存的位、标记搜索、重置，以及记账结果和帧结果。从历史推出窗口与重置前提。 |
| `compress2_z`, `compress2`, `compress_z`, `compress` | 需要：压缩器执行 | <a id="readiness-compress2-z"></a> **开始：**参数、标量长度和清理。**组合：**实际的初始化、压缩和结束，连同精确的输出，然后是各包装函数。抽象的往返性质还不够。 |
| `uncompress2_z`, `uncompress2`, `uncompress_z`, `uncompress` | 需要：解码器执行 | <a id="readiness-uncompress2-z"></a> **开始：**标量结果、空间不足和清理。**组合：**实际的初始化、解压和结束，精确的消耗量和输出，然后是各包装函数。 |
| `inflate_sequence`, `deflate_sequence`, `inflate_back_sequence`, `gz_sequence` | 需要：执行与格式 | <a id="readiness-inflate-sequence"></a> **组合：**每次调用实际的安全性、历史的保持、独立的格式细化，以及跨输入输出切分的完成性质。 |
| `inflateBack` | 需要：表、窗口与回调 | <a id="readiness-inflateback"></a> **组合：**压缩块的 TABLE/LEN 执行、落在窗口之内的输出、公开回调的所有权、循环终止，以及精确的输入输出记账。现有的存储块路径和入口路径可以独立推进。 |
<!-- proof-readiness:end -->

### 规格审查

本节的六条记录都已结束，保存在[规格审查记录](history/specification-review.md)中：gzip 定位模式、inflate 初始化的清理、解压实用函数的清理、gzip 打开路径的长度、带本地修复的 gzip 库问题，以及系统调用预言下的 gzip 偏移与倒回。两个 gz 位置溢出问题写在根目录的 `README.md` 中；补丁见[补丁说明](../patches/README.md)。

未完成，并且不在计划内，因为它们是仅关于模型的命题（见[范围](#scope)）：

- `Api.Goal.inflate_rejects_invalid` 依赖 `detectLag = 8`。一个经过检查的反例表明这个常数是错的（[API 模型](design/api-model.md)）。
- `Api.Goal.gz_seek_read` 已经改正，并已[在本地检查](../ZlibF/Proof/Api/GzSeekRead.lean)。它没有登记。

本节早先的文字里有两件事，是否已经做完没有确认：对改正后的共用关系 `Uncompress2` 的独立审查，以及补全较早的抽象 gz 模型和字典模型。具体的公开目标不假设这些模型中被调用函数的契约。

### 翻译审查

对照 C 审查翻译的工作还没有做完。未完成的事项：

- **NULL 指针算术。** 所选构建依赖哪个 C 语言版本和哪些实现扩展，可达的“NULL 加零”和“NULL 减 NULL”操作是否有定义，都还没有确立。模型允许其中一些操作：`Ptr.add` 对 `NULL + 0` 返回 `NULL`，辅助函数 `Zlib.Compress.ptrDiff` 对 `NULL - NULL` 返回零。`Ptr.diff` 本身在 `NULL - NULL` 上产生故障；它在源码中的注释说，C17 和 C23 都没有定义这种减法，而 C++ 把它定义为 0。[对照表](spec/safety.md#null-pointers-and-pointer-differences)记录了实际的定义和语言依据。这里并不断言存在可达的上游缺陷。
- **逐条语句的审查。** 压缩器的自动存储已经审查并改正。其余部分的审查有待继续。
- **压缩器的窗口滑动。** 滑动按源码的顺序检查有符号减法。它的[内部状态回归](../tests/regression/deflate-slide/README.md)比较三个有定义的边界情形，并在 C 和 Lean 中都拒绝一个人为构造的溢出。恢复不带检查的减法，只会改变溢出情形下观察到的结果。这里不断言那个人为构造的状态是可达的；有符号运算的界还没有从合法的调用历史中推出来。
- **树合并中对深度的重新读取。** 翻译像源码那样重新读取选中的深度，配有[六例回归](../tests/regression/trees-depth-read/README.md)和一项必需的结构检查，后者会拒绝缓存表达式的写法。内部深度读取之前的初始化先后关系还没有证明。
- **标量与指针的别名，以及 NULL 减 NULL 的特殊情形**（在压缩器的指针相减中）**尚未由证明确认**。

### 观察记录

**`write` 返回 0 时 `gz_comp` 会空转。** 在 `gz_comp` 的两个写循环中（`gzwrite.c`：透明模式的循环 `while (strm->avail_in)` 和写出循环 `while (strm->next_out > state->x.next)`），对非空缓冲区返回 0 的 `write` 不推进任何东西，也不算错误，所以循环重复同一次调用。如果系统一直返回 0，C 就永远不返回。这是对代码的解读；没有实际运行过永远返回 0 的 `write`。目前不知道 Linux 会对普通文件、管道或套接字上的非零计数返回 0（其他文件类型尚未确认），所以 gz 安全证明假设它不会发生（[偏离记录](deviations.md#gzip-file-interface)，“Gz 操作系统事实”一行）。gz 安全研究的故障注入测试平台检查了另一面：让 `write` 对 10% 的非空调用返回 0（40 段历史，ASan 和 UBSan），每段历史结束时都没有报告，也没有泄漏，因为每个循环最终都会得到一个正的结果。这是库的行为，不是安全问题；只有在已知某个平台会返回 0 时，才值得向上游说明。范围：`gzwrite`、`gzfwrite`、`gzputc`、`gzputs`、`gzprintf`、`gzflush`、`gzsetparams`、`gzclose_w`。

**`gzerror` 返回的字符串会被下一次到达 `gz_error` 的调用释放。** 这是一条未确认的发现，属于文档缺口，不是代码缺陷。`zlib.h` 只说之后对 `gzerror` 的调用可能使返回的字符串失效。实际上 `gzerror` 返回的是 `state->msg`，而每个到达 `gz_error` 的调用都会释放它。写入的入口函数（`gzwrite`、`gzfwrite`、`gzputc`、`gzputs`、`gzprintf`、`gzvprintf`、`gzflush`、`gzsetparams`）在检查模式和错误之后、使用参数之前，用 `gz_error(state, Z_OK, NULL)` 重置错误。读取的入口函数（`gzread`、`gzfread`、`gzgetc`、`gzungetc`、`gzgets`）只在上一次读取停滞时才这样做（表见[偏离记录](deviations.md#why-the-handles-own-strings-are-excluded)）。调用者把这个字符串再传回同一个句柄，就可能遇到释放后使用：写入停滞之后的 `gzprintf(f, "%s", gzerror(f, &e))` 在 `vsnprintf` 中读取已释放的内存（[复现](../tests/regression/gzprintf-error-string/README.md)，ASan）。没有补丁。已证明的定义域让调用者的字符串和缓冲区与句柄的块分开（`GzRange`，以及 `GzArguments` 中针对 `gzprintf` 和 `gzvprintf` 的分离子句；[偏离记录](deviations.md)）。

**`deflateBound` 在两种情形下偏小。** 两者都是 `zlib.h` 关于大小的承诺没有兑现，不是内存错误，并且都在固定版本的 C 上复现了。`Z_FIXED` 策略、压缩级别 1 到 3、`windowBits` 为 15 且 `memLevel` 为 8 时，给出 `deflateBound` 字节的空间，一次 `deflate(Z_FINISH)` 调用返回 `Z_OK`（[发现](findings/deflatebound-fixed-far-matches/README.md)）。gzip extra 字段长度为 `2^32 - 2` 或 `2^32 - 1` 时，`2 + extra_len` 这个和在 32 位上回绕（[发现](findings/deflatebound-extra-len/README.md)）。必需的安全目标都不依赖这个上界的数值。有两处功能命题依赖它，这两项发现的页面说它们在这些情形下按现在的写法是假的：对每种策略量化的 `DeflateCompletes`，以及关于数值的目标 `Goal.deflateBound` 和 `Goal.deflateBound_z`（它们未证明）。默认策略不受影响，所以计划中的默认流往返不受影响。这些功能命题怎样改正，还没有决定。

### 待复查的历史报告

早先的工作报告过六个事项。其中三个已经对照固定版本的源码重新检查，现在是带复现的发现：

- gzip extra 字段长度的算术：[extra 字段很长时的 `deflateBound`](findings/deflatebound-extra-len/README.md)；
- 部分读取之后的恢复：[`gzread` 从过时的 `x.next` 复制](findings/gzread-transparent-stale-next/README.md)，补丁 0003；
- 负位置的定位：[开头的 `gzungetc` 之后调用 `gzseek`](findings/gzseek-pushback-overflow/README.md)，补丁 0002。

另外三个还没有对照固定版本的源码重新检查（[发现，早期的库观察](findings.md#earlier-library-observations)）：

- 参数变更的丢失；
- 结束失败之后的恢复；
- EOF 之后的向前定位。

带条件的定位故障引理证明不了可达性：有符号位置的条件和借用指针的条件，还没有从实际的调用历史中推出来。`inflateBack` 的历史报告对该回调 API 而言仍未确认；普通 inflate 的 sanitizer 示例不能定论。[早先的证明笔记](history/proof-earlier-notes.md)保留了其中两份报告的原文：`inflateBack` 缺少 `whave` 的报告（“回调解码器：迁移来的定义域表”一节，原文标题为 `Callback decoder: the migrated domain table`），以及 `gzsetparams`“参数变更丢失”的实验（[该节](history/proof-earlier-notes.md#gzsetparams-experiment)）。外部字符串的分配器和固定的循环燃料还没有审查到这样的程度：足以断言完整的 gzip 所有权，或断言任意有限的回调都会终止。怀疑存在缺陷，并不是把某种公开情形排除在外的许可。[发现](findings.md)保存证据和置信度；补丁见 [patches/README.md](../patches/README.md)。没有应用笼统的未定义行为补丁。

[架构指南](design/architecture.md#design-decisions)记录了设计决策 D1–D6。[安全性规格](spec/safety.md#uninitialised-memory)定义了新分配内存带来的证明义务。

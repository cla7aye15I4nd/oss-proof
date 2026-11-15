<!-- source-sha256: 3d8d00894a9b41546ac8b6805d1402d5a2014e129298260fa83f38b8c317c910 -->
# 发现与证据登记

本页列出本项目在 zlib 本身发现的问题。它把四组分开：由 sanitizer 在真实 C 上确认的问题，仅按 C 标准字面规定属于未定义的问题，`deflateBound` 的两处不属于内存错误的失信，以及在本项目自己的补丁里发现的一个缺口。每个问题都有自己的页面，给出调用序列、运行命令、输出、严重程度和修复。后面的几节保留早期的、未确认的观察。

固定的源码是上游 `develop` 的提交 `757f0527`。上游状态读取于 2026-11-14。[Sanitizer 报告](sanitizer-reports.md)列出所有保留的 sanitizer 复现，包括不属于 zlib 问题的调用者错误。[补丁](../patches/README.md)说明被验证的源码应用的五个补丁。未完成的调查只记在[进度](progress.md)中。

差分测试、sanitizer 运行和模型运行都是证据，不是关于 C 的证明。

## 固定的源码中已确认的问题

一个问题同时具备以下三项时才算**已确认**：调用序列、保留的复现，以及一次 sanitizer 报告了它的真实 C 运行。

| 问题 | 在哪里出问题 | 证据 | 上游状态 |
| --- | --- | --- | --- |
| [`inflateCopy` 比较无关的指针](findings/inflate-copy-fixed/README.md) | 对已经解码过固定码块、之后没有解码过动态码块的流调用 `inflateCopy`。文档用法。没有观察到错误结果。 | AddressSanitizer 的指针对检查，`inflate.c:1383` | [拉取请求 #1369](https://github.com/madler/zlib/pull/1369)：维护者于 2026-11-06 答复“Applied”；还不在 `develop` 上。本仓库的补丁 0001。 |
| [开头的 `gzungetc` 之后调用 `gzseek`](findings/gzseek-pushback-overflow/README.md) | 在位置 0 调用 `gzungetc`，再调用 `gzseek`：`gzseek64` 中有符号溢出。文档用法。 | UndefinedBehaviorSanitizer，`gzlib.c:395`、`403`、`424` | [拉取请求 #1361](https://github.com/madler/zlib/pull/1361)，仍处于打开状态，尚无答复。本仓库的补丁 0002。 |
| [`gzread` 从过时的 `x.next` 复制](findings/gzread-transparent-stale-next/README.md) | 透明读取；`read()` 返回一些字节后失败：读到输出缓冲区之外的堆内存。文档用法。 | AddressSanitizer，`gzread.c:369` | [拉取请求 #1363](https://github.com/madler/zlib/pull/1363)，仍处于打开状态，尚无答复。本仓库的补丁 0003。 |
| [gz 位置溢出，读取](findings/gzread-pos-overflow/README.md) | 在 `lseek` 成功却不移动的设备（Linux 的 `/dev/zero`）上定位到 2^63 附近之后做透明读取。文档用法。 | x86_64 Linux 上的 UndefinedBehaviorSanitizer，位于 `gz_read`、`gzgetc` 和 `gzgetc()` 宏 | 没有提交。本仓库的本地补丁 0004。 |
| [gz 位置溢出，写入](findings/gzwrite-pos-overflow/README.md) | 在能接受这些数据的接收端（`/dev/null`）上向前定位到 2^63 附近之后做透明写入。文档用法。 | UndefinedBehaviorSanitizer，`gzwrite.c:230`、`352` | 没有提交。本仓库的本地补丁 0004。 |
| [`deflateResetKeep` 之后的 `deflateCopy`](findings/deflate-copy-pending-prev/README.md) | 之后在副本上调用 `deflate` 会读到窗口之外。它需要直接调用 `deflateResetKeep`，而 zlib.h 把该函数列为不属于 API：不是文档 API 的缺陷。 | AddressSanitizer，`deflate.c:1511`；valgrind，`deflate.c:1555` | 没有报告。有一份[报告草稿](findings/deflate-copy-pending-prev-report.md)。没有补丁：证明排除了这个调用（[偏离记录](deviations.md)）。 |

对每个已诊断的序列，置信度都高。前五个在 zlib.h 的文档用法之内。补丁 0004 和 0005 是本地补丁：项目所有者于 2026-11-12 批准，没有提交上游。

## 按 C 标准的字面规定未定义，没有 sanitizer 报告

这两个问题按 C 标准的措辞是未定义行为。没有 sanitizer 报告其中任何一个，也没有观察到错误行为，所以它们不满足“已确认”的定义。各自的页面用编译进真实 C 的探针展示了这次计算。

| 问题 | 在哪里出问题 | 证据 | 上游状态 |
| --- | --- | --- | --- |
| [`gz_reset` 从不写入 `x.next`](findings/gz-reset-next-uninitialised/README.md) | 在还没有任何输出时调用 `gzseek` 或 `gzdirect`，会对一个从未写入的字段执行 `x.next += 0`。 | 探针运行；对 C 的解读 | 没有提交。本仓库的本地补丁 0005。 |
| [`x.next` 留在调用者的缓冲区中](findings/gz-next-dangling-after-direct-read/README.md) | 一次大的 `gzread` 读入某个缓冲区、调用者随后释放它之后，`gzseek` 或 `gzdirect` 对悬空指针执行 `x.next += 0`。 | 探针运行；对 C 的解读 | 没有提交。本仓库的本地补丁 0005。 |

## `deflateBound` 的失信，不是内存错误

`zlib.h` 承诺：一次带 `Z_FINISH` 的 `deflate` 调用，如果拿到全部输入，并且输出缓冲区的大小是 `deflateBound` 返回的值，就以 `Z_STREAM_END` 结束。下面两种情形已在固定的 C 上复现，这次调用返回的是 `Z_OK`：这个界太小。两者都不是未定义行为，sanitizer 也没有任何报告，所以它们不满足上面“已确认”的定义，那个定义要求有 sanitizer 报告。两者都没有打补丁。

| 问题 | 在哪里出问题 | 证据 | 上游状态 |
| --- | --- | --- | --- |
| [`Z_FIXED` 在级别 1 到 3 时 `deflateBound` 太小](findings/deflatebound-fixed-far-matches/README.md) | `windowBits` 为 15、`memLevel` 为 8、策略为 `Z_FIXED`、级别 1 到 3。对 1,000,000 字节的输入，界是 1,000,318，而流最多需要 1,008,570 字节。`compress`、`compress2` 和 `compressBound` 使用默认策略，不受影响。 | 固定的 C 上的 `repro.c`，分别在启用和不启用 AddressSanitizer 与 UndefinedBehaviorSanitizer 的情况下运行。范围来自命题测试 `tests/goals/deflate-bound`。系统自带的 zlib 1.2.12 在级别 1 到 9 上全部失败。 | 没有报告。上游是否已经知道，尚未向上游核实。 |
| [gzip extra 字段长度为 2^32 − 2 或 2^32 − 1 时的 `deflateBound`](findings/deflatebound-extra-len/README.md) | `deflateBound` 按 32 位计算 `2 + extra_len`，所以对这两个长度，和发生回绕，界大约小了 64 KiB。 | 固定的 C 上的 `tests/goals/deflate-bound/bound.c`，`extra` 模式 | 上游已知（上游拉取请求 1360 中有讨论）。 |

每个发现页面都说明了该情形对功能命题意味着什么。按这两页的说法，`DeflateCompletes` 照现在的写法对第一种情形不成立，因为它对每一种策略全称量化；数值目标 `Goal.deflateBound` 和 `Goal.deflateBound_z` 对第二种情形的两个长度不成立。这两个数值目标都没有已登记的定理（`tests/audit/proved-goals.txt`）。

## 在本项目自己的补丁里发现的缺口

这是本地补丁 0004 第一版的缺陷，不是上游 zlib 的又一个缺陷。

| 问题 | 在哪里出问题 | 证据 | 状态 |
| --- | --- | --- | --- |
| [透明探测之后的位置溢出](findings/gz-position-copy-overflow.md) | 在补丁 0004 的第一版下，`gz_look` 的透明分支缓冲输入时没有这个界限，所以读取者返回时可能有 `x.pos + x.have` 大于 `GZ_OFF_MAX`，随后 `gzgetc()` 宏溢出。 | Lean 模型在一个构造出的状态上的运行，以及对 C 的解读。没有在 sanitizer 下复现：这段历史需要约 2^63 个解码字节。 | 由补丁 0004 的第二版（2026-11-13）补上。模型回归测试：`tests/verification/regressions/gz-position-copy-overflow.lean`。 |

在不打任何补丁的固定的源码中，同一段历史更早就溢出了，溢出在 `gz_read` 里：那就是已确认的问题“gz 位置溢出，读取”。

## 其他页面使用的标签

[gz 证明说明](proof/gzip.md)和历史页面用标签称呼其中六份报告。

| 标签 | 问题 |
| --- | --- |
| R-1 | 开头的 `gzungetc` 之后调用 `gzseek` |
| R-2 | `gzread` 从过时的 `x.next` 复制 |
| R-3 | `gz_reset` 从不写入 `x.next` |
| R-4 | `x.next` 留在调用者的缓冲区中 |
| F-1 | gz 位置溢出，读取 |
| W7 | gz 位置溢出，写入 |

## 不属于 zlib 缺陷的记录

列在这里，是为了不让人把它们误当成 zlib 缺陷。

| 记录 | 它是什么 | 位置 |
| --- | --- | --- |
| 把 `gzerror` 返回的字符串传给 `gzprintf` | 文档缺口。把 `gzerror` 返回的字符串传给同一句柄上的 `gzprintf` 是释放后使用：`gzprintf` 在格式化之前就释放了句柄的消息。zlib.h 说之后的 `gzerror` 调用可能使该字符串失效，文件关闭后该字符串不再可用（`zlib.h:1793`）；它没有提到 `gzprintf`。gz 安全目标要求 `gzprintf` 的字符串与句柄自己的块分开（[偏离记录](deviations.md#gzip-file-interface)，“Gz printf 字符串”一行）。 | [gzprintf-error-string](../tests/regression/gzprintf-error-string/README.md) |
| `deflateResetKeep` 与过时的散列项 | 直接调用 `deflateResetKeep` 之后出现的数据错误（错误的匹配），不是内存错误。它是不是 zlib 缺陷，尚未向上游核实：该函数不属于有文档的 API。 | [deflate-resetkeep-stale-hash](findings/deflate-resetkeep-stale-hash/README.md) |

## 早期的库观察

这些观察来自早期工作，没有确认。每一行说明保留了什么。另有四项早期观察已成为已确认的问题，列在第一张表里（`inflateCopy`、`gzungetc` 之后的 `gzseek`、过时的 `x.next`、位置溢出）。还没有被证明确认的 C 解读标为**尚未由证明确认**。

| 观察 | 保留的资料与置信度 | 报告的范围 |
| --- | --- | --- |
| `gzsetparams` 可能记下一次内部压缩器并未接受的变更 | 早期的发现文字报告了两次独立运行：级别 6 下 16640–16660 个随机字节，请求级别 0，再输入 200000 个零字节，得到一个约 16.9 KB、仍是压缩形式的文件。[早期证明笔记](history/proof-earlier-notes.md#gzsetparams-experiment)把这个实验和所提出的机制作为未确认的报告保留；[gzip 证明指南](proof/gzip.md)只指向那里。 | 普通的参数变更；仍能产生有效数据。[契约审查](checking/contract-review.md)要求成功的有效变更到达内部压缩器。 |
| `crc32_combine_op` 对任意算子可能不终止 | 早期的发现文字报告了 `1UL << 32` 的两次超时运行；[CRC 源码分析](proof/crc32.md)记录运行过 `crc32_combine_op(1, 2, 1UL << 32)`。没有保留独立的复现。 | 不是由 `crc32_combine_gen` 生成的算子。文档规定的生成算子定义域是另一回事；这不是该定义域内失败的证据。 |
| `gzflush(..., Z_FINISH)` 失败后清除错误，之后输出可能丢失 | 早期的发现文字报告：之后继续写入并成功关闭，文件却是空的。[gz 分析](proof/gzip.md)提供源码背景；含有复现的那段文字没有保留。只是报告的观察。 | 错误恢复和写入者的生存期。这不改变另外证明的 `gzclearerr` 清除效果。 |
| 越过末尾的 `gzseek` 可能与 `gztell` 不一致，并保留 EOF | 早期的发现文字报告了一个五字节的 gzip 文件：向前定位五个字节返回 10，而 `gztell` 返回 5，EOF 仍然置位；透明文件的行为不同。[gz 分析](proof/gzip.md)保留了位置和待执行跳过的背景。属于报告的 API 怪异行为；没有保留独立的复现。 | 输入结束之后的逻辑位置。它是否违反公开契约，需要另行审查。 |
| 较小的 inflate 窗口可能让成功与否取决于输出怎样分块 | 早期的发现文字报告了一个 20000 字节的流：一次调用给足输出空间时被接受，窗口较小、每次调用 100 字节时被拒绝。[inflate API](spec/api/inflate-stream.md)说明了窗口的定义域。这是对文档所述小窗口限制的历史观察，不是上游缺陷。 | 窗口小于流的需要。不能据此声称任意小的窗口都能解码每个有效流。 |

## 早期记录的调用者定义域问题

[压缩一侧的分析](proof/deflate.md)和 [inflate 分析](proof/inflate.md)记录了这些情形。它们怎样归类取决于公开 API 允许什么；这里没有把其中任何一项升格为已确认的缺陷。

| 情形 | 问题与证据的边界 |
| --- | --- |
| `compress2` 和 `uncompress2` 的 NULL 长度指针 | 兼容包装函数在 `_z` 的检查之前读取标量单元。[分配回归测试](../tests/regression/compress-allocation/README.md)保留了一个读 NULL 的见证。诊断出读 NULL，并不说明调用者被允许传入 NULL。 |
| `deflateCopy(&s, &s)` | 报告称原来拥有的状态丢失。复制的安全目标假设目的流不是源记录（[偏离记录](deviations.md)，“复制的目的流”一行）。 |
| `inflateGetHeader(strm, NULL)` | 报告称解引用了 NULL。`inflateGetHeader` 的安全目标假设头部不是 `NULL`（[偏离记录](deviations.md#stream-calls-inflate-and-deflate)，“头部参数”一行）。 |
| inflate 期间的 `gz_header` extra 缓冲区 | 当 `extra` 缓冲区与未读输入重叠时，EXTRA 的 `zmemcpy` 是未定义的；当调用者在 extra 字段中途调低 `extra_len` 时，它会写到 `extra_max` 之外。两种情况都已用 sanitizer 在 [extra 字段回归测试](../tests/regression/inflate-gzip-extra/README.md)中复现。zlib.h 没有说明这两种布局是否允许；`Goal.inflate_safety` 通过 `ActiveHeader` 排除了两者（[偏离记录](deviations.md)，“inflate 的 gzip extra 字段”一行）。 |
| `deflateSetDictionary` 与 `total_in` | 字典字节计入这个计数器。早先对“输入字节”的解释可能没有算上它们；文档的含义与操作上的细化必须分清。 |
| 迟到的 `deflatePrime` 和 `deflateSetHeader` | C 可能接受不合文档顺序的调用；之后对头部的解引用就可能无效。C 接受了调用，不等于该序列是文档允许的用法。 |
| `deflateResetKeep` 与预置字典输出 | 保留下来的历史可能让下一个流要求字典。这需要按文档所述的重置语义处理，不能假设每次重置都得到全新的历史。 |

## 模型与规格方面的证据

这些记录涉及形式化本身或对它的解释。它们不是库的安全性发现。下面链接的测试是保留的执行证据或诊断证据；本页并不声称重新运行过它们。

| 记录 | 保留的证据 | 含义 |
| --- | --- | --- |
| inflate 后期的内存失败可能发生在已有输出之后 | [分配回归测试](../tests/regression/compress-allocation/README.md)记录了一个截断的 zlib 前缀：返回 `Z_MEM_ERROR`，同时有一个输出字节和两个已存的计数。早期的运行还记录到：窗口分配失败时，指针已经前进，而流的总数和校验和不变。 | 内存错误不意味着没有输出。[契约审查](checking/contract-review.md)记录了更正后的实用函数关系，以及初始化失败与后期失败在标量效果上的区别。 |
| 已消耗的预读内容不一定全部描述一个有效流 | [延迟距离回归测试](../tests/regression/inflate-deferred-distance/README.md)保留了裸字节 `73 04 42 00`：一次调用输出 `A`，下一次调用拒绝一个不可能的距离，且不再消耗输入。 | 原先针对全部预读内容的规格过强。审查后采用的支持前缀条件是对模型的更正，不是 zlib 缺陷。 |
| 负的预置位值保留其低位 | [预置位回归测试](../tests/regression/inflate-prime/README.md)在各种有符号值和边界位数上比较实际调用。 | 把负值映射为零是规格错误。有限的一致性不是一般的细化证明。 |
| 压缩器的自动存储不得消耗分配失败 | [分配回归测试](../tests/regression/compress-allocation/README.md)保留了失败序号、缓冲区和存活块的观察，以及对旧翻译的一个变异。 | 那次额外的分配是翻译缺陷。目的指针为 NULL 时的指针相减，仍是另一个关于 C 是否有定义的问题。 |
| 静态 CRC 输入有表示出来的地址 | [正向回归测试](../tests/verification/regressions/crc-static-address.lean)保留了原先反例中那次有效的 47 字节静态表读取，并检查两个 CRC 入口。 | 翻译模型的拒绝已经修复，没有缩小校验和的调用者定义域。这不是上游缺陷；一般的 ABI 与别名限制仍然存在。 |
| gz 状态可能保留一个指向调用者缓冲区的指针 | [gz 分析](proof/gzip.md)记录了直接解压之后的加零运算，以及调用者可能释放缓冲区的情况。没有 sanitizer 报告它。[发现](findings/gz-next-dangling-after-direct-read/README.md)用探针展示了这次加零。 | 模型对悬空指针上的运算报故障。本地补丁 0005 去掉了这次加零；见本页第二张表。 |

[运行时审查](checking/runtime-review.md)记录了其他表示上的缺口，包括新分配的指针在模型中为 NULL，以及固定的垃圾值。[可信基础](trusted-base.md)说明当前的义务。历史上的审查结论不是完整的安全性证明或正确性证明。

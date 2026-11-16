<!-- source-sha256: de1e97ca49c7032c46d242cb65cb74c2ff741c0da10479f02914a8aae001b260 -->
# 发现：本项目在 zlib 中发现了什么

本页列出本项目在 zlib 本身发现的问题。它把三组分开：由 sanitizer 在真实 C 上确认的问题，仅按 C 标准字面规定属于未定义的问题，以及 `deflateBound` 的两处不属于内存错误的失信。每个问题都有自己的页面，给出调用序列、运行命令、输出、严重程度和修复。后面的几节保留未确认的观察，以及不属于 zlib 缺陷的行为。

固定的源码是上游 `develop` 的提交 `99623ef7`，即 zlib 1.4。上游状态截至 2026-11-15。[Sanitizer 报告](sanitizer-reports.md)列出所有 sanitizer 复现，包括不属于 zlib 问题的调用者错误。[补丁](../patches/README.md)说明被验证的源码应用的六个补丁。

差分测试、sanitizer 运行和模型运行都是证据，不是关于 C 的证明。

## 固定的源码中已确认的问题

一个问题同时具备以下三项时才算**已确认**：调用序列、复现，以及一次 sanitizer 报告了它的真实 C 运行。

| 问题 | 在哪里出问题 | 证据 | 上游状态 |
| --- | --- | --- | --- |
| [`inflateCopy` 比较无关的指针](findings/inflate-copy-fixed/README.md) | 对已经解码过固定码块、之后没有解码过动态码块的流调用 `inflateCopy`。文档用法。没有观察到错误结果。 | AddressSanitizer 的指针对检查，`inflate.c:1383` | [拉取请求 #1369](https://github.com/madler/zlib/pull/1369)：维护者于 2026-11-06 答复“Applied”；还不在 `develop` 上。本仓库的补丁 0001。 |
| [开头的 `gzungetc` 之后调用 `gzseek`](findings/gzseek-pushback-overflow/README.md) | 在位置 0 调用 `gzungetc`，再调用 `gzseek`：`gzseek64` 中有符号溢出。文档用法。 | UndefinedBehaviorSanitizer，`gzlib.c:395`、`403`、`424` | [拉取请求 #1361](https://github.com/madler/zlib/pull/1361)，仍处于打开状态，尚无答复。本仓库的补丁 0002。 |
| [`gzread` 从过时的 `x.next` 复制](findings/gzread-transparent-stale-next/README.md) | 透明读取；`read()` 返回一些字节后失败：读到输出缓冲区之外的堆内存。文档用法。 | AddressSanitizer，`gzread.c:369` | [拉取请求 #1363](https://github.com/madler/zlib/pull/1363)，仍处于打开状态，尚无答复。本仓库的补丁 0003。 |
| [gz 位置溢出，读取](findings/gzread-pos-overflow/README.md) | 在 `lseek` 成功却不移动的设备（Linux 的 `/dev/zero`）上定位到 2^63 附近之后做透明读取。文档用法。 | x86_64 Linux 上的 UndefinedBehaviorSanitizer，位于 `gz_read`、`gzgetc` 和 `gzgetc()` 宏 | 没有提交。本仓库的本地补丁 0004。 |
| [gz 位置溢出，写入](findings/gzwrite-pos-overflow/README.md) | 在能接受这些数据的接收端（`/dev/null`）上向前定位到 2^63 附近之后做透明写入。文档用法。 | UndefinedBehaviorSanitizer，`gzwrite.c:230`、`352` | 没有提交。本仓库的本地补丁 0004。 |
| [`deflateResetKeep` 之后的 `deflateCopy`](findings/deflate-copy-pending-prev/README.md) | 之后在副本上调用 `deflate` 会读到窗口之外。它需要直接调用 `deflateResetKeep`，而 zlib.h 把该函数列为不属于 API：不是文档 API 的缺陷。 | AddressSanitizer，`deflate.c:1511`；valgrind，`deflate.c:1555` | 没有报告。有一份[报告草稿](findings/deflate-copy-pending-prev-report.md)。没有补丁：证明排除了这个调用（[偏离记录](deviations.md)）。 |

对每个已诊断的序列，置信度都高。前五个在 zlib.h 的文档用法之内。补丁 0004 和 0005 是本地补丁：没有提交上游。

## 按 C 标准的字面规定未定义，没有 sanitizer 报告

这两个问题按 C 标准的措辞是未定义行为。没有 sanitizer 报告其中任何一个，也没有观察到错误行为，所以它们不满足“已确认”的定义。各自的页面用编译进真实 C 的探针展示了这次计算。

| 问题 | 在哪里出问题 | 证据 | 上游状态 |
| --- | --- | --- | --- |
| [`gz_reset` 从不写入 `x.next`](findings/gz-reset-next-uninitialised/README.md) | 在还没有任何输出时调用 `gzseek` 或 `gzdirect`，会对一个从未写入的字段执行 `x.next += 0`。 | 探针运行；对 C 的解读 | 没有提交。本仓库的本地补丁 0005。 |
| [`x.next` 留在调用者的缓冲区中](findings/gz-next-dangling-after-direct-read/README.md) | 一次大的 `gzread` 读入某个缓冲区、调用者随后释放它之后，`gzseek` 或 `gzdirect` 对悬空指针执行 `x.next += 0`。 | 探针运行；对 C 的解读 | 没有提交。本仓库的本地补丁 0005。 |

## `deflateBound` 的失信，不是内存错误

`zlib.h` 承诺：一次带 `Z_FINISH` 的 `deflate` 调用，如果拿到全部输入，并且输出缓冲区的大小是 `deflateBound` 返回的值，就以 `Z_STREAM_END` 结束。下面两种情形已在固定的 C 上复现，这次调用返回的是 `Z_OK`：这个界太小。两者都不是未定义行为，sanitizer 也没有任何报告，所以它们不满足上面“已确认”的定义，那个定义要求有 sanitizer 报告。第一种已在本地打补丁（补丁 0006）；第二种没有打补丁。

| 问题 | 在哪里出问题 | 证据 | 上游状态 |
| --- | --- | --- | --- |
| [`Z_FIXED` 在级别 1 到 3 时 `deflateBound` 太小](findings/deflatebound-fixed-far-matches/README.md) | `windowBits` 为 15、`memLevel` 为 8、策略为 `Z_FIXED`、级别 1 到 3。对 1,000,000 字节的输入，界是 1,000,318，而流最多需要 1,008,570 字节。`compress`、`compress2` 和 `compressBound` 使用默认策略，不受影响。 | 固定的 C 上的复现，分别在启用和不启用 AddressSanitizer 与 UndefinedBehaviorSanitizer 的情况下运行。范围来自在真实 C 上对各参数检验这项承诺的测试。系统自带的 zlib 1.2.12 在级别 1 到 9 上全部失败。带补丁 0006 时，复现程序和对含远距离匹配的输入所做的搜索在每个级别都能结束。 | 没有报告。上游是否已经知道，尚未向上游核实。本仓库的本地补丁 0006：没有提交。 |
| [gzip extra 字段长度为 2^32 − 2 或 2^32 − 1 时的 `deflateBound`](findings/deflatebound-extra-len/README.md) | `deflateBound` 按 32 位计算 `2 + extra_len`，所以对这两个长度，和发生回绕，界大约小了 64 KiB。 | 固定的 C 上一个用这两个长度调用 `deflateBound` 的 C 驱动程序 | 上游已知（上游拉取请求 1360 中有讨论）。 |

每个发现页面都说明了该情形对功能命题意味着什么。没有补丁 0006 时，完备性命题 `DeflateCompletes` 对第一种情形不成立，因为它对每一种策略全称量化。数值目标 `Goal.deflateBound` 和 `Goal.deflateBound_z` 对第二种情形的两个长度不成立；两者都未完成。

## 经由 `gz_look` 的位置溢出

这不是上游 zlib 的又一个缺陷。它说明位置溢出的修复（补丁 0004）为什么也给 `gz_look` 加了界限。只给读取函数加界限是不够的：`gz_look` 的透明分支也缓冲输入，那里没有界限时，读取者返回时可能有 `x.pos + x.have` 大于 `GZ_OFF_MAX`，随后 `gzgetc()` 宏溢出（[发现](findings/gz-position-copy-overflow.md)）。

证据：Lean 模型在一个构造出的状态上的运行（[模型检查](../tests/verification/regressions/gz-position-copy-overflow.lean)），以及对 C 的解读。没有在 sanitizer 下复现：这段历史需要约 2^63 个解码字节。在不打任何补丁的固定的源码中，同一段历史更早就溢出了，溢出在 `gz_read` 里：那就是已确认的问题“gz 位置溢出，读取”。

## 不属于 zlib 缺陷的记录

列在这里，是为了不让人把它们误当成 zlib 缺陷。

| 记录 | 它是什么 | 位置 |
| --- | --- | --- |
| 把 `gzerror` 返回的字符串传给 `gzprintf` | 文档缺口。把 `gzerror` 返回的字符串传给同一句柄上的 `gzprintf` 是释放后使用：`gzprintf` 在格式化之前就释放了句柄的消息。zlib.h 说之后的 `gzerror` 调用可能使该字符串失效，文件关闭后该字符串不再可用（`zlib.h:1793`）；它没有提到 `gzprintf`。gz 安全目标要求 `gzprintf` 的字符串与句柄自己的块分开（[偏离记录](deviations.md#gzip-file-interface)，“Gz printf 字符串”一行）。 | [gzprintf-error-string](../tests/regression/gzprintf-error-string/README.md) |
| `deflateResetKeep` 与过时的散列项 | 直接调用 `deflateResetKeep` 之后出现的数据错误（错误的匹配），不是内存错误。它是不是 zlib 缺陷，尚未向上游核实：该函数不属于有文档的 API。 | [deflate-resetkeep-stale-hash](findings/deflate-resetkeep-stale-hash/README.md) |

<a id="earlier-library-observations"></a>

## 未确认的观察

这些关于库行为的观察没有确认：其中任何一项都没有保留复现。还没有被证明确认的 C 解读标为**尚未由证明确认**。

| 观察 | 观察到了什么 | 范围 |
| --- | --- | --- |
| `gzsetparams` 可能记下一次内部压缩器并未接受的变更 | 两次独立运行：级别 6 下 16640–16660 个随机字节，请求级别 0，再输入 200000 个零字节，得到一个约 16.9 KB、仍是压缩形式的文件。其机制**尚未由证明确认**。 | 普通的参数变更；仍能产生有效数据。 |
| `crc32_combine_op` 对任意算子可能不终止 | 用算子 `1UL << 32` 的两次运行超时。已证明的内容说的是翻译：`crc32_combine_op_diverges` 表明翻译在调用 `crc32_combine_op(1, 2, 1UL << 32)` 上耗尽燃料（[CRC 证明](proof/crc32.md)）。 | 不是由 `crc32_combine_gen` 生成的算子。文档规定的生成算子定义域是另一回事；这不是该定义域内失败的证据。 |
| `gzflush(..., Z_FINISH)` 失败后清除错误，之后输出可能丢失 | 之后继续写入并成功关闭，留下的文件却是空的。 | 错误恢复和写入者的生存期。这不改变另外证明的 `gzclearerr` 清除效果。 |
| 越过末尾的 `gzseek` 可能与 `gztell` 不一致，并保留 EOF | 对一个五字节的 gzip 文件，向前定位五个字节返回 10，而 `gztell` 返回 5，EOF 仍然置位；透明文件的行为不同。 | 输入结束之后的逻辑位置。它是否违反公开契约，需要另行审查。 |
| 较小的 inflate 窗口可能让成功与否取决于输出怎样分块 | 一个 20000 字节的流：一次调用给足输出空间时被接受，窗口较小、每次调用 100 字节时被拒绝。[inflate API](spec/api/inflate-stream.md)说明了窗口的定义域。这是文档所述的小窗口限制，不是上游缺陷。 | 窗口小于流的需要。不能据此声称任意小的窗口都能解码每个有效流。 |

## 调用者定义域问题

[压缩一侧的分析](proof/deflate.md)和 [inflate 分析](proof/inflate.md)记录了这些情形。它们怎样归类取决于公开 API 允许什么；这里没有把其中任何一项升格为已确认的缺陷。

| 情形 | 问题与证据的边界 |
| --- | --- |
| `compress2` 和 `uncompress2` 的 NULL 长度指针 | 兼容包装函数在 `_z` 的检查之前读取标量单元。一个[复现](../tests/regression/compress-allocation/README.md)展示了这次读 NULL。诊断出读 NULL，并不说明调用者被允许传入 NULL。 |
| `deflateCopy(&s, &s)` | 报告称原来拥有的状态丢失。复制的安全目标假设目的流不是源记录（[偏离记录](deviations.md)，“复制的目的流”一行）。 |
| `inflateGetHeader(strm, NULL)` | 报告称解引用了 NULL。`inflateGetHeader` 的安全目标假设头部不是 `NULL`（[偏离记录](deviations.md#stream-calls-inflate-and-deflate)，“头部参数”一行）。 |
| inflate 期间的 `gz_header` extra 缓冲区 | 当 `extra` 缓冲区与未读输入重叠时，EXTRA 的 `zmemcpy` 是未定义的；当调用者在 extra 字段中途调低 `extra_len` 时，它会写到 `extra_max` 之外。两种情况都已用 sanitizer [复现](../tests/regression/inflate-gzip-extra/README.md)。zlib.h 没有说明这两种布局是否允许；`Goal.inflate_safety` 通过 `ActiveHeader` 排除了两者（[偏离记录](deviations.md)，“inflate 的 gzip extra 字段”一行）。 |
| `deflateSetDictionary` 与 `total_in` | 字典字节计入这个计数器。文档中的“输入字节”是否包括它们，是文档含义的问题，与代码实际怎么做是两回事。 |
| 迟到的 `deflatePrime` 和 `deflateSetHeader` | C 可能接受不合文档顺序的调用；之后对头部的解引用就可能无效。C 接受了调用，不等于该序列是文档允许的用法。 |
| `deflateResetKeep` 与预置字典输出 | 保留下来的历史可能让下一个流要求字典。这需要按文档所述的重置语义处理，不能假设每次重置都得到全新的历史。 |

## 规格必须容许的 zlib 行为

这些记录说的是真实的 C。它们不是安全性发现，也不是 zlib 缺陷；每一项都是 zlib 的规格必须容许的行为。链接的测试运行了真实的 C；它们是证据，不是证明。

| 行为 | 证据 | 含义 |
| --- | --- | --- |
| `inflate` 后期的内存失败可能发生在已有输出之后 | 一个截断的 zlib 前缀返回 `Z_MEM_ERROR`，同时有一个输出字节和两个已存的计数（[测试](../tests/regression/compress-allocation/README.md)）。 | 内存错误不意味着没有输出。初始化时的失败与后期的失败对计数的效果不同。 |
| 一次调用已消耗的输入不一定全部属于一个有效流 | 对裸字节 `73 04 42 00`，一次调用输出 `A`，下一次调用拒绝一个不可能的距离，且不再消耗输入（[测试](../tests/regression/inflate-deferred-distance/README.md)）。 | 要求每个已消耗的字节都属于某个有效流的规格过强。 |
| 负的位预置值保留其低位 | 在各种有符号值和边界位数上对 `inflatePrime` 的调用（[测试](../tests/regression/inflate-prime/README.md)）。 | 负值不被当作零。有限的一致性不是一般的细化证明。 |
| `compress*` 的自动流记录不消耗分配尝试 | 对失败的分配序号、缓冲区和存活块的观察（[测试](../tests/regression/compress-allocation/README.md)）。 | `compress*` 的模型不得把这个自动记录算作一次可能失败的分配。目的指针为 `NULL` 时的指针相减，仍是另一个关于 C 是否有定义的问题。 |
| CRC 的输入可以是静态数据 | 经由两个 CRC 入口对一张静态表的 47 字节读取（[模型检查](../tests/verification/regressions/crc-static-address.lean)）。 | 校验和的调用者定义域包括静态存储。一般的 ABI 与别名限制仍然存在（[模型的限制](model-limits.md)）。 |
| gz 状态可能保留一个指向调用者缓冲区的指针 | 直接解压之后，状态对一个指向调用者可能已释放的缓冲区的指针做加零运算。没有 sanitizer 报告它。[发现](findings/gz-next-dangling-after-direct-read/README.md)用探针展示了这次加零。 | 模型对悬空指针上的运算报故障。本地补丁 0005 去掉了这次加零；见本页第二张表。 |

[可信基础](trusted-base.md)和[模型的限制](model-limits.md)说明模型在哪些地方与 C 不同，包括新分配的指针读出来是 `NULL`，以及每个未初始化的整数单元取一个固定的值。

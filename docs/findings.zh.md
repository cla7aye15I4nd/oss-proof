<!-- source-sha256: 2d0b09b16ccf542e221d1d70f6846f2f243701e3155f07e9a62821d377a6bded -->
# 发现与证据登记

本页先列出固定版本 zlib 源码中已确认的问题，再列出尚未确认的早期观察。根目录的 `README.md` 记录每个已确认的问题；本页用一张表给出同样的事实，并保留历史。[Sanitizer 报告](sanitizer-reports.md)列出每个保留的 sanitizer 复现。[进度](progress.md)是当前调查和剩余工作的唯一清单。

已确认的问题需要一个允许的调用序列、一份保留的复现，以及真实 C 在 sanitizer 下的一次运行。证据较弱时，该行会如实写明证据是什么。差分测试和模型运行是证据，不是关于 C 的证明。

## 固定版本源码中已确认的问题

固定版本是上游 `develop` 上的 `757f0527`。上游状态读取于 2026-11-14。

| 问题 | 描述 | 复现 | 可信度与范围 | 上游与验证所用源码 |
| --- | --- | --- | --- | --- |
| `inflateCopy` 比较无关的指针 | 默认 `inflateInit` 之后，停在固定块内的流，其 `lencode` 指向静态表。`inflateCopy` 把它与状态自己的数组做关系比较：未定义行为。 | [inflate-copy-fixed](findings/inflate-copy-fixed/README.md)，含 sanitizer 报告 | 对所诊断的序列可信度高。在文档允许的用法之内。 | 修复已作为 [PR #1369](https://github.com/madler/zlib/pull/1369) 提交；维护者于 2026-11-06 答复“Applied”。`develop` 分支头（`99623ef7`）还不包含它。这里以补丁 0001 应用。 |
| 开头 `gzungetc` 之后的 `gzseek` | 在位置 0 调用 `gzungetc` 使 `x.pos` 变为 -1。随后 `gzseek64` 的范围检查发生有符号算术溢出。 | [gzseek-pushback-overflow](../tests/regression/gzseek-pushback-overflow/README.md) | 高：UndefinedBehaviorSanitizer 报告三处。在文档允许的用法之内。 | 修复已作为 [PR #1361](https://github.com/madler/zlib/pull/1361) 提交，尚未合入，维护者尚未答复。这里以补丁 0002 应用。 |
| 部分读取后 `gzread` 使用过期的 `x.next` | 透明模式下，`read` 先提供一些字节，然后失败。`gz_fetch` 在设置 `x.next` 之前就返回，读取函数从旧指针复制：越出缓冲区的读。 | [gzread-transparent-stale-next](../tests/regression/gzread-transparent-stale-next/README.md) | 高：AddressSanitizer 报告这次读。在文档允许的用法之内；需要在读到部分数据之后出现读错误。 | 修复已作为 [PR #1363](https://github.com/madler/zlib/pull/1363) 提交，尚未合入，维护者尚未答复。这里以补丁 0003 应用。 |
| gz 位置溢出，读取（F-1） | 读取函数不加界限地累加有符号位置 `x.pos`。在 `lseek` 成功却不移动的设备上，定位到 2^63 − 1 会被接受，下一次读取就溢出。 | [发现](findings/gzread-pos-overflow/README.md)；[gzread-pos-overflow](../tests/regression/gzread-pos-overflow/README.md) | 高：x86_64 Linux 上的 UndefinedBehaviorSanitizer。范围：这类设备（Linux 的 `/dev/zero`），透明模式。 | 未提交。补丁 0004 是本地补丁，尚待提交上游（所有者于 2026-11-12 批准）。 |
| gz 位置溢出，写入（W7） | `gz_write` 和 `gzputc` 不加界限地累加 `x.pos`。透明写入者定位到 2^63 附近后，下一次写入溢出。 | [发现](findings/gzwrite-pos-overflow/README.md)；[gzwrite-pos-overflow](../tests/regression/gzwrite-pos-overflow/README.md) | 高：x86_64 Linux 上用 `/dev/null` 的 UndefinedBehaviorSanitizer。范围：接近 2^63 的透明位置。 | 未提交。补丁 0004，本地补丁，尚待提交上游。 |
| 透明探测之后的 gz 位置溢出 | 在补丁 0004 的第一版下，`gz_look` 的透明分支缓冲输入时没有用空间界限，所以读取者返回时 `x.pos + x.have` 可能超过 `GZ_OFF_MAX`，随后 `gzgetc()` 宏溢出。 | [发现](findings/gz-position-copy-overflow.md)；模型回归 `tests/verification/regressions/gz-position-copy-overflow.lean` | 已在模型中确认，也已通过阅读 C 确认。没有在 sanitizer 下复现：这段历史需要约 2^63 个解码字节。 | 补丁 0004 已覆盖它：该分支现在使用同样的空间界限。本地补丁，尚待提交上游。 |
| `x.next` 未写入或悬空时被加零（R-3、R-4） | 当该字段从未写入（R-3）或指向已释放的调用者缓冲区（R-4）时，`gzseek64` 和 `gz_skip_have` 以 `n == 0` 执行 `x.next += n`。 | [R-3](findings/gz-reset-next-uninitialised/README.md)、[R-4](findings/gz-next-dangling-after-direct-read/README.md)，各有一次探针运行 | 按 C 标准的字面规定未定义。没有 sanitizer 报告它们，也没有观察到异常行为。 | 未提交。补丁 0005 是本地补丁，尚待提交上游（所有者于 2026-11-12 批准）。 |
| `deflateResetKeep` 之后的 `deflateCopy` | `deflateCopy` 没有复制两个待插入的 `prev` 槽；之后在副本上调用 `deflate` 会沿着未初始化的槽走，`longest_match` 读到窗口之外。 | [发现](findings/deflate-copy-pending-prev/README.md)；[deflate-copy-pending-prev](../tests/regression/deflate-copy-pending-prev/README.md) | 对所诊断的序列可信度高：在未修改的固定版本上有 AddressSanitizer 和 valgrind 报告。范围：需要直接调用 `deflateResetKeep`，而 zlib.h 把它列为未文档化函数，所以这不是有文档的 API 的缺陷。 | 未报告。已有一份[报告草稿](findings/deflate-copy-pending-prev-report.md)。没有补丁：已证明的 deflate 定义域排除了这个调用（见[偏离记录](deviations.md)）。 |

有两条记录不是 zlib 缺陷。把它们列在这里，是为了避免被误当作缺陷。

| 记录 | 它是什么 | 位置 |
| --- | --- | --- |
| 把 `gzerror` 返回的字符串传给 `gzprintf` | 这是文档缺口，不是 zlib 缺陷。把 `gzerror` 返回的字符串传给同一句柄上的 `gzprintf` 是释放后使用：`gzprintf` 在格式化之前先释放句柄的消息。zlib.h 只说明之后的 `gzerror` 调用可能使该字符串失效。已证明的定义域要求 `gzprintf` 的字符串与句柄自己的内存块分离（见[偏离记录](deviations.md)）。 | [gzprintf-error-string](../tests/regression/gzprintf-error-string/README.md) |
| `deflateResetKeep` 与过期的哈希项 | 直接调用 `deflateResetKeep` 之后出现的数据错误（错误的匹配），不是内存错误。它是否算 zlib 缺陷，需要向上游确认（**to confirm**）：该函数没有文档。 | [deflate-resetkeep-stale-hash](findings/deflate-resetkeep-stale-hash/README.md) |

## 早期库观察

下表记录早期工作的报告，以及现在保留了什么。没有保留复现的行属于未确认。仍待证明确认的 C 解读标为 **to confirm**。

| 观察 | 保留资料与可信度 | 报告范围 |
| --- | --- | --- |
| `gzsetparams` 可记录内部压缩器未接受的变更 | 早期发现文字报告两次独立运行：级别 6 的 16640–16660 个随机字节，请求级别 0，再输入 200000 个零字节，生成约 16.9 KB、仍被压缩的文件。[Gzip 证明指南](proof/gzip.md)保留机制，但标为候选。历史状态的不一致不等于当前确认。 | 普通参数变更；仍可产生有效数据。[契约审阅](checking/contract-review.md)要求成功的有效变更到达内部压缩器。 |
| `crc32_combine_op` 对任意操作符可能不终止 | 早期文字报告 `1UL << 32` 的两次超时运行；[CRC 源码分析](proof/crc32.md)记录运行过 `crc32_combine_op(1, 2, 1UL << 32)`。这里未保留独立复现。 | 非 `crc32_combine_gen` 生成的操作符。文档规定的生成操作符定义域另当别论；这不是该域内失败的证据。 |
| `gz_fetch` 可在部分读取后失败时保留陈旧源指针 | 现已确认：见上表（补丁 0003）。[gz 分析](proof/gzip.md)（R-2）和[翻译说明](design/external-io.md)保留了原因。 | 读取部分数据后出现读错误。普通的文件世界模型不覆盖每一种这样的外部读取序列。 |
| 在位置零 `gzungetc` 后 `gzseek` 可能发生有符号位置算术溢出 | 现已确认：见上表（补丁 0002）。[gz 分析](proof/gzip.md)把它记为 R-1。 | 负逻辑位置和大 seek 算术。不能据此限制广泛 seek 目标。 |
| `gzread` 和 `gzwrite` 可能使有符号位置 `x.pos` 溢出 | 已确认：见上表（F-1 和 W7，[补丁 0004](../patches/README.md)）。 | `lseek` 成功却不移动的设备，或接近 2^63 的透明位置。 |
| `gzflush(..., Z_FINISH)` 失败后清错可能先于输出丢失 | 早期文字报告之后继续写入、成功关闭，但文件为空。[gz 分析](proof/gzip.md)提供源码背景；此前含复现的长函数叙述已不保留。仅为报告的观察。 | 错误恢复和写入器生命周期。不改变另外证明的 `gzclearerr` 清错效果。 |
| `inflateCopy` 比较无关对象内的指针 | 已确认：见上表（补丁 0001）。[inflate 分析](proof/inflate.md)保留了早期报告。 | 默认初始化之后，流停在固定块内。 |
| 越过末尾的 `gzseek` 可与 `gztell` 不一致，并保留 EOF | 早期文字报告一个五字节 gzip 文件：再向前定位五字节返回 10，tell 返回 5，EOF 保持；透明文件行为不同。[gz 分析](proof/gzip.md)保留位置和待跳过操作背景。属于报告的 API 特性，没有独立保留复现。 | 输入结束后的逻辑位置。是否违反公开契约需另行审阅。 |
| 较小 inflate 窗口可能让成功依赖输出分块 | 早期文字报告一个 20000 字节流：单次调用提供足够输出空间时接受，较小窗口配合每次 100 字节调用时拒绝。[inflate API](spec/api/inflate-stream.md)说明窗口定义域。属于文档所述小窗口限制的历史观察，不是上游缺陷。 | 窗口小于流所需大小。不能据此声称任意小窗口都能解码每个有效流。 |

## 早期记录的调用者定义域问题

[压缩侧分析](proof/deflate.md)和 [inflate 分析](proof/inflate.md)记录这些情况。分类取决于公开 API 允许什么；这里没有将任何一项提升为确认缺陷。

| 情况 | 历史问题与证据边界 |
| --- | --- |
| `compress2` 和 `uncompress2` 的空长度指针 | 兼容包装在 `_z` 检查前读取标量单元。[分配回归](../tests/regression/compress-allocation/README.md)现保留空读取见证。诊断出空读取不等于调用者允许传入 NULL。 |
| `deflateCopy(&s, &s)` | 报告原拥有状态丢失；源和目标相同是否被允许需要契约审阅。 |
| `inflateGetHeader(strm, NULL)` | 报告空指针解引用；空头部的调用者定义域需审阅。 |
| inflate 期间的 `gz_header` extra 缓冲区 | 当 `extra` 缓冲区与未读输入重叠时，EXTRA 的 `zmemcpy` 是未定义行为；当调用者在 extra 字段中途调低 `extra_len` 时，它会写出 `extra_max` 之外。两种情况都已用 sanitizer 在 [extra 字段回归](../tests/regression/inflate-gzip-extra/README.md)中复现。zlib.h 没有说明这两种布局是否允许；`Goal.inflate` 通过 `ActiveHeader` 排除了两者（[偏差](deviations.md)）。 |
| `deflateSetDictionary` 与 `total_in` | 字典字节计入计数器。此前对“输入字节”的解释可能排除了它们；文档含义与操作细化必须区分。 |
| 后期 `deflatePrime` 和 `deflateSetHeader` | C 可接受超出文档顺序的调用，之后的头部解引用可能无效。接受调用本身不让序列成为文档用法。 |
| `deflateResetKeep` 与预置字典输出 | 保留历史可使下一流请求字典。需使用文档中的 reset 语义，不能假设每种 reset 都产生全新历史。 |

## 模型与规范证据

这些记录涉及形式化或其解释，不是库安全性发现。以下链接测试是保留的执行或诊断证据；本页不声称为文档改动重跑过它们。

| 记录 | 保留证据 | 含义 |
| --- | --- | --- |
| 后期 inflate 内存失败可发生在输出之后 | [分配回归](../tests/regression/compress-allocation/README.md)记录截断 zlib 前缀以 `Z_MEM_ERROR` 返回，具有一个输出字节和两个已存计数。早期运行还记录窗口分配失败时指针已前进，而流总数和校验和不变。 | 内存错误不等于没有输出。[契约审阅](checking/contract-review.md)记录修正后的工具关系，以及 init 失败和后期失败不同的标量效果。 |
| 已消费的预读内容不一定全部描述有效流 | [延迟距离回归](../tests/regression/inflate-deferred-distance/README.md)保留 raw 字节 `73 04 42 00`：一次调用输出 `A`，下一次在不消费更多输入时拒绝不可能距离。 | 此前对全部预读内容的规范过强。审阅后的支持前缀条件是模型修正，不是 zlib 缺陷。 |
| 负 priming 值保留低位 | [priming 回归](../tests/regression/inflate-prime/README.md)比较有符号值和边界位计数下的实际调用。 | 把负数映射到零是规范错误。有限一致性不是一般细化证明。 |
| 压缩器自动存储不能消耗分配失败 | [分配回归](../tests/regression/compress-allocation/README.md)保留失败索引、缓冲区、存活块观察及旧翻译的变异。 | 额外分配是翻译缺陷。空目标指针减法仍是独立的 C 有定义性问题。 |
| 静态 CRC 输入现有表示出的地址 | [正向回归](../tests/verification/regressions/crc-static-address.lean)保留此前反例中有效的 47 字节静态表读取，并检查两个 CRC 入口。 | 翻译模型的拒绝已修复，没有缩小校验和调用者定义域。这不是上游缺陷；通用 ABI 与别名限制仍存在。 |
| Gz 状态可保留指向调用者缓冲区的指针 | [gz 分析](proof/gzip.md)记录直接解压后的加零算术，以及调用者可能释放缓冲区的情况（R-4）。没有 sanitizer 报告它。[发现](findings/gz-next-dangling-after-direct-read/README.md)用探针展示了这次零前进。 | 模型对悬空指针的算术报故障。本地补丁 0005 去掉了零前进；见已确认问题的表。 |

[运行时审阅](checking/runtime-review.md)记录其他表示缺口，包括新鲜指针在模型中为 NULL，以及固定任意初值。[可信基础](trusted-base.md)给出当前义务。历史审阅结论不是完整的安全性或正确性证明。

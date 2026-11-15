<!-- source-sha256: a972ed36f6d8cd3f95ef0d9156469d7cc0dbcc333d1f8469bfe039bb70659ab4 -->
# zlib-f

用 Lean 4 证明 zlib 是安全的，证明由内核检查。C 源码被逐条语句翻译成 Lean。证明表明：默认 x86_64 Linux 构建中每个有文档的公开函数，在任何调用序列里运行时都没有未定义行为、没有内存错误、没有泄漏，并且终止；前提是每条定理自己写明的那些条件。

**已证明。** 全部 63 个必需目标都有一个类型完全相同的[已登记](docs/glossary.md#status)定理。它们覆盖目标构建中 86 个有文档的函数：`inflate` 与 `deflate` 及其调用序列、其他流函数、校验和、`compress*` 与 `uncompress*`、gzip 文件接口，以及回调解码器 `inflateBack`。这 63 个目标是：52 个单函数安全目标、4 个序列安全目标、3 个拒绝目标和 4 个[非空性目标](docs/glossary.md#goals)。31 个 gz 函数共用一个序列目标，三个 `inflateBack` 函数共用另一个，所以 86 个函数用不到 86 个目标。[验收套件](docs/glossary.md#checking)曾在提交 `bde170e9` 上全部通过，当时 63 个目标都已登记，所以这些结论在该提交上已验收。有一处例外：四个初始化安全目标在那之后扩大了范围，范围扩大后的形式已登记，尚未验收。那个提交之后有什么变化，见[范围](docs/progress.md#scope)。

**所作假设。** 内核对照 Lean 命题检查每个证明。有六件事是被信任而没有被证明的（[可信基础](docs/trusted-base.md)）：

1. Lean 内核、三条标准公理，以及审计程序；
2. 关于内存、指针、故障和循环的运行时模型；
3. 对 C 的手工翻译；
4. 选定的源码：固定版本的 `zlib/` 加上五个[补丁](patches/README.md)；
5. 构建配置，以及分配、文件和格式化的模型；
6. 命题本身：每个目标说的确实是它该说的。

差分测试是翻译与 C 一致的证据，不是证明。有些定理带有 `zlib.h` 没有写出的前提：调用者的缓冲区互不重叠、使用默认分配器、gz 读取调用的终止需要小于 2^61 字节的读取预算、一次 `inflateBack` 调用的输入少于 2^48 字节。[偏离记录](docs/deviations.md)把这些前提按函数列成了核对清单。

**未完成。** 安全结论所需要的东西没有缺口。31 个 gz 函数和三个 `inflateBack` 函数的安全性由两个序列目标证明（`Goal.gz_sequence_safety`、`Goal.inflate_back_sequence_safety`），这两个目标覆盖每段历史中的每次调用。它们还不像另外 52 个函数那样各有一个单函数目标；陈述并登记这 34 个目标是剩余的工作。补丁 0004 和 0005 尚未提交上游。

**并非必需。** 安全结论不需要功能正确性，即 `inflate` 的输出等于格式规定的内容，或 `deflate` 的输出能解码回输入。其中有一部分是计划内的工作，尚未证明：默认 zlib 流先经 `deflate` 再经 `inflate` 的往返。其他构建配置、自定义分配器，以及 `zlib.h` 列为未文档化的函数，都不在计划内。[范围](docs/progress.md#scope)列出每一组及其理由。先前已证明的功能目标保持登记。

## 哪条定理覆盖某个函数

| 问题 | 去哪里看 |
| --- | --- |
| 哪条定理证明了函数 X 是安全的，定义域是什么？ | [按函数查覆盖情况](docs/coverage.md) |
| 我的调用要满足什么才被覆盖？ | [偏离记录](docs/deviations.md)开头的核对清单 |
| 结论是已检查、已登记还是已验收，对应哪个提交？ | [范围](docs/progress.md#scope) |
| 这些词是什么意思？ | [术语表](docs/glossary.md) |

## 目标的种类

目标是名为 `Goal.…` 的 Lean 命题；只有类型与目标完全相同的定理才算证明了它。清单文件 `tests/audit/public-api.json` 为每个有文档的函数写明一个安全目标和一个功能目标。对 34 个 gz 函数和 `inflateBack` 函数，清单文件写的安全目标就是序列目标。

| 种类 | 说的是什么 | 位置 | 审计是否要求 |
| --- | --- | --- | --- |
| 安全目标 | 调用返回而没有未定义行为，只写它获准写的内存（它的帧），并且不泄漏 | `ZlibF/Spec/Safety/`；gz 与 `inflateBack` 的目标在 `ZlibF/Spec/Public/` | 要求 |
| 非空性目标 | 安全目标的前提可以被满足：有一个具体的堆，在它上面初始化或打开成功 | `ZlibF/Spec/Safety/Domains.lean`、`ZlibF/Spec/Public/` | 要求 |
| 功能目标 | 结果是什么：返回值、输出字节 | `ZlibF/Spec/Functional/` | 不要求。已证明的会被完整审计；未证明的不会导致任何检查失败 |

规则见[安全目标与功能目标的拆分](docs/design/safety-functional-split.md)。

## 文档

**[阅读文档网站](https://www.dataisland.org/zlib-f/)** · [网站内容源码](docs/README.md)

| 阅读入口 | 回答什么问题 |
| --- | --- |
| [总览](https://www.dataisland.org/zlib-f/reference/docs/overview.html) | 证明了什么，假设了什么，证明是怎样搭起来的？ |
| [结果与状态](https://www.dataisland.org/zlib-f/status.zh.html) | 什么已登记，什么在计划内，什么不在？ |
| [按函数查覆盖情况](https://www.dataisland.org/zlib-f/reference/docs/coverage.html) | 哪条定理覆盖函数 X？ |
| [偏离记录](https://www.dataisland.org/zlib-f/reference/docs/deviations.html) | 一次调用要满足什么才被覆盖？ |
| [可信基础](https://www.dataisland.org/zlib-f/reference/docs/trusted-base.html) | 内核不检查什么？ |
| [全部目标的依赖图](https://www.dataisland.org/zlib-f/reference/docs/progress.html#proof-progress-graph) | 目标之间怎样依赖，各自覆盖多大的输入范围？ |
| [证据索引](https://www.dataisland.org/zlib-f/reference/docs/progress.html) | 每个目标的精确命题、证明和依赖在哪里？ |
| [规格](https://www.dataisland.org/zlib-f/reference/docs/spec/README.html) | 安全目标、API 契约和格式说的是什么？ |
| [API](https://www.dataisland.org/zlib-f/reference/api.html) | 每个函数要求什么，保证什么？ |
| [设计](https://www.dataisland.org/zlib-f/reference/docs/design/README.html) | 翻译和内存模型是怎样工作的？ |
| [证明](https://www.dataisland.org/zlib-f/reference/docs/proof/README.html) | 各部分论证是怎样组合的？ |
| [检查](https://www.dataisland.org/zlib-f/reference/docs/checking/README.html) | 每项检查能确立什么？ |
| [参与贡献](https://www.dataisland.org/zlib-f/reference/docs/checking/contributing.html) | 运行哪些命令，按什么顺序？ |
| [术语表](https://www.dataisland.org/zlib-f/reference/docs/glossary.html) | 这些术语是什么意思？ |

## 仓库结构

- `zlib/`：固定版本的上游源码；不直接修改，修复补丁放在 `patches/`。
- `ZlibF/Zlib/`：逐条语句翻译的 C 实现。
- `ZlibF/Spec/Safety/`：必需的安全目标。`ZlibF/Spec/Functional/`：功能契约、格式模型和 API 模型。`ZlibF/Spec/Public/`：两者共用的定义，以及 gz 接口和 `inflateBack` 的五个必需目标。
- `ZlibF/Proof/` 和 `ZlibF/Math/`：实现证明和不涉及堆的数学推导。
- `ZlibF/Runtime/`：内存、指针、算术和执行语义。
- `tests/`：差分测试、变异测试和证明审计。

## 本地检查

```bash
lake build ZlibF
scripts/check-sorry.sh
```

这两条命令就是快速关卡。[参与贡献](docs/checking/contributing.md)列出每一步；[检查指南](docs/checking/README.md)说明每项检查能确立什么，以及一项结论怎样成为已验收。

## 在 zlib 中发现的问题

这项工作在固定版本的源码中发现了下列问题。每行给出复现、置信度和适用范围。最后两行是关于大小的承诺没有兑现，不是内存错误。[发现](docs/findings.md)有每个问题的完整说明和上游状态；[补丁说明](patches/README.md)描述每个补丁。

| 问题 | 是否在有文档的 API 之内 | 证据与置信度 | 被验证源码中的修复 |
| --- | --- | --- | --- |
| 流停在固定块内部时，`inflateCopy` 用关系运算符比较互不相关的指针，这是未定义行为 | 是 | 在固定版本的 C 上的[复现](docs/findings/inflate-copy-fixed/README.md)。对所诊断的调用序列置信度高。 | 补丁 0001，即上游 [PR #1369](https://github.com/madler/zlib/pull/1369) 的修复 |
| 一开始就调用 `gzungetc` 之后再调用 `gzseek`：`x.pos` 为 -1，`gzseek64` 的范围检查发生有符号溢出 | 是 | [复现](docs/findings/gzseek-pushback-overflow/README.md)：UndefinedBehaviorSanitizer 报告三处。置信度高。 | 补丁 0002，取自上游 [PR #1361](https://github.com/madler/zlib/pull/1361)，该拉取请求仍处于打开状态 |
| 透明模式下，部分读取之后读取失败，再调用 `gzread`：`gz_fetch` 在设置 `x.next` 之前就返回，读取函数从旧指针复制，读到缓冲区之外 | 是；需要在读到部分数据之后出现读取错误 | [复现](docs/findings/gzread-transparent-stale-next/README.md)：AddressSanitizer 报告这次读取。置信度高。 | 补丁 0003，上游 [PR #1363](https://github.com/madler/zlib/pull/1363)，该拉取请求仍处于打开状态 |
| gz 位置溢出：`gzread`、`gzgetc`、`gzgetc()` 宏、`gzwrite` 和 `gzputc` 把字节数加到有符号 64 位位置 `x.pos` 上，没有上界检查 | 是；出现在 `lseek` 成功却不移动的设备上（`/dev/zero`、`/dev/null`），或透明模式下位置接近 2^63 时 | [读取](docs/findings/gzread-pos-overflow/README.md)和[写入](docs/findings/gzwrite-pos-overflow/README.md)两个方向的复现：x86_64 Linux 上的 UndefinedBehaviorSanitizer。对所诊断的调用序列置信度高。 | 补丁 0004，本地补丁，经所有者批准，尚未提交上游：位置保持在 `z_off64_t` 范围内，会溢出的调用以 `Z_DATA_ERROR` 失败 |
| 同一种溢出，经由补丁 0004 第一版中 `gz_look` 的透明 COPY 分支：在一个带尾随数据的 gzip 成员、一次 `gzclearerr` 和一次接近 2^63 − 1 的读取之后，`x.pos + x.have` 超过 `GZ_OFF_MAX` | 是；在上述历史之后、距 `GZ_OFF_MAX` 不超过 `size` 字节之处 | [发现](docs/findings/gz-position-copy-overflow.md)：在模型中确认，并通过阅读 C 确认。没有 sanitizer 的确认；这段历史需要大约 2^63 个解码字节。就打过补丁的源码本身而言，置信度高。 | 补丁 0004 也给这个分支加了上界 |
| 对未设置或悬空的 `x.next` 前进零步：该字段从未写入，或指向已释放的调用者缓冲区时，`gzseek64` 和 `gz_skip_have` 执行 `x.next += 0` | 是；即两项发现中的两个调用序列 | [未设置](docs/findings/gz-reset-next-uninitialised/README.md)与[悬空](docs/findings/gz-next-dangling-after-direct-read/README.md)两种情形各有一次探针运行。按 C 标准的字面是未定义行为。证据弱于上面各行：sanitizer 对两种情形都不报告，也没有观察到异常行为。 | 补丁 0005，本地补丁，经所有者批准，尚未提交上游 |
| `deflateResetKeep` 之后的 `deflateCopy`：两个待处理的 `prev` 槽没有被复制，之后在副本上调用 `deflate` 会沿着未初始化的槽走下去，`longest_match` 读到窗口之外 | 否：需要直接调用 `deflateResetKeep`，而 `zlib.h` 把它列为未文档化函数 | 在未修改的固定版本上的[复现](docs/findings/deflate-copy-pending-prev/README.md)：AddressSanitizer 报告这次读取，valgrind 报告未初始化的槽。对所诊断的调用序列置信度高。在 zlib 1.4 和固定的 `develop` 上能复现，在 1.3.1 和 1.3.2 上不能。 | 没有。已证明的 deflate 定义域排除了这种调用（[偏离记录](docs/deviations.md)）。已有一份[报告草稿](docs/findings/deflate-copy-pending-prev-report.md)；尚未向上游发送任何内容。 |
| `Z_FIXED` 策略、压缩级别 1 到 3、`windowBits` 为 15 且 `memLevel` 为 8 时，`deflateBound` 给出的上界偏小：按这个大小给出空间，一次 `deflate(Z_FINISH)` 调用返回 `Z_OK`，与 `zlib.h` 的承诺不符 | 是。这是没有兑现的承诺，不是内存错误；`compress`、`compress2` 和 `compressBound` 使用默认策略，不受影响 | 在固定版本的 C 上的[复现](docs/findings/deflatebound-fixed-far-matches/README.md)，开启和不开启 sanitizer 都做过，sanitizer 没有任何报告。对所诊断的参数置信度高。系统自带的 zlib 1.2.12 在级别 1 到 9 上全部失败。尚未报告上游。上游是否已知，尚未向上游核实。 | 没有。安全目标都不依赖这个上界的数值 |
| gzip extra 字段长度为 2^32 − 2 或 2^32 − 1 时的 `deflateBound`：`2 + extra_len` 在 32 位上回绕，上界少了大约 64 KiB | 是。这是没有兑现的承诺，不是内存错误 | 在固定版本的 C 上的[复现](docs/findings/deflatebound-extra-len/README.md)。上游已知。 | 没有。安全目标都不依赖这个上界的数值 |

`inflateCopy` 和各 gz 函数的安全目标是针对打过补丁的源码陈述的。

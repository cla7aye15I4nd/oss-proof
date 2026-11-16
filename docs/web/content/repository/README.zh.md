<!-- source-sha256: 17de5a3113bc024191e6bb5a4b7ad69276ab19cfdc1fb41aced5bafa2a33038a -->
# zlib-f

用 Lean 4 证明 zlib 是安全的，证明由内核检查。C 源码被逐条语句翻译成 Lean。证明表明：默认 x86_64 Linux 构建中每个有文档的公开函数，在任何调用序列里运行时都没有未定义行为、没有内存错误、没有泄漏，并且终止；前提是每条定理自己写明的那些条件。

一项结论**完成**，是指存在一条命题与目标完全相同的 Lean 定理，并且它通过了本项目的每一项检查。否则就是**未完成**。

**完成。** 目标构建中 86 个有文档的函数，每个都有一个安全目标，以及一个类型与该目标完全相同的定理：`inflate` 与 `deflate`、其他流函数、校验和、`compress*` 与 `uncompress*`、gzip 文件接口，以及回调解码器 `inflateBack`。`gzvprintf` 也有：`zlib.h` 把它列为未文档化，而 `gzprintf` 经由它实现。另有一些目标，各有一个类型完全相同的定理，覆盖 `inflate`、`deflate`、`inflateBack` 和 gz 函数的调用序列（序列安全目标），覆盖库必须拒绝的调用，例如流或句柄为 `NULL`（拒绝目标），并说明这些前提可以被满足（[非空性目标](docs/glossary.md#goals)）。每个函数对应的定理见[按函数查覆盖情况](docs/coverage.md)；[进度页](docs/progress.md)列出每项结论及其状态。

**所作假设。** 内核对照 Lean 命题检查每个证明。有六件事是被信任而没有被证明的（[可信基础](docs/trusted-base.md)）：

1. Lean 内核、三条标准公理，以及检查证明用了哪些公理、定理的命题是否与目标完全相同的程序；
2. 关于内存、指针、故障和循环的运行时模型；
3. 对 C 的手工翻译；
4. 选定的源码：固定版本的 zlib 加上各个[补丁](patches/README.md)；
5. 构建配置，以及分配、文件和格式化的模型；
6. 命题本身：每个目标说的确实是它该说的。

差分测试把翻译与真实的 C 作比较；它们是两者一致的证据，不是证明。有些定理带有 `zlib.h` 没有写出的前提：调用者的缓冲区互不重叠、使用默认分配器、gz 读取调用的终止需要小于 2^61 字节的读取预算、一次 `inflateBack` 调用的输入少于 2^48 字节。[偏离记录](docs/deviations.md)把这些前提按函数列成了核对清单。

**未完成。** 功能正确性，即 `inflate` 的输出等于格式规定的内容，或 `deflate` 的输出能解码回输入。安全结论不需要它。其中有一部分在计划内：默认 zlib 流先经 `deflate` 再经 `inflate` 的往返。它的条件形式已有一条定理：两条调用序列都到达 `Z_STREAM_END` 时，输出等于输入。完备性（空间足够时两边一定能结束）和无条件形式还没有定理。其他构建配置、自定义分配器，以及 `zlib.h` 列为未文档化的函数，都不在计划内。[进度页](docs/progress.md)列出每一组及其理由。尽管如此，有些功能目标已有定理；[按函数查覆盖情况](docs/coverage.md)列出了它们。

## 哪条定理覆盖某个函数

| 问题 | 去哪里看 |
| --- | --- |
| 哪条定理证明了函数 X 是安全的，定义域是什么？ | [按函数查覆盖情况](docs/coverage.md) |
| 我的调用要满足什么才被覆盖？ | [偏离记录](docs/deviations.md)开头的核对清单 |
| 哪些结论完成了，哪些未完成？ | [进度页](docs/progress.md) |
| 这些词是什么意思？ | [术语表](docs/glossary.md) |

## 目标的种类

目标是名为 `Goal.…` 的 Lean 命题；只有类型与目标完全相同的定理才算证明了它。每个有文档的函数都有自己的安全目标，名为 `Goal.<function>_safety`（或 `_safe`）；`compressBound` 和 `compressBound_z` 是纯函数，由功能目标代替安全目标。

| 种类 | 说的是什么 | 状态 |
| --- | --- | --- |
| 安全目标 | 调用返回而没有未定义行为，只写它获准写的内存（它的帧），并且不泄漏 | 完成，每个有文档的函数都是 |
| 非空性目标 | 安全目标的前提可以被满足：有一个具体的堆，在它上面初始化或打开成功 | 完成 |
| 功能目标 | 结果是什么：返回值、输出字节 | 有些函数完成，有些未完成；安全结论不依赖未完成的那些 |

两类目标怎样分开，见[安全目标与功能目标的拆分](docs/design/safety-functional-split.md)。

## 文档

**[阅读文档网站](https://www.dataisland.org/zlib-f/)**

| 阅读入口 | 回答什么问题 |
| --- | --- |
| [总览](https://www.dataisland.org/zlib-f/reference/docs/overview.html) | 证明了什么，假设了什么，证明是怎样搭起来的？ |
| [进度](https://www.dataisland.org/zlib-f/reference/docs/progress.html) | 哪些结论完成了，哪些未完成，哪些不在计划内？ |
| [按函数查覆盖情况](https://www.dataisland.org/zlib-f/reference/docs/coverage.html) | 哪条定理覆盖函数 X？ |
| [偏离记录](https://www.dataisland.org/zlib-f/reference/docs/deviations.html) | 一次调用要满足什么才被覆盖？ |
| [可信基础](https://www.dataisland.org/zlib-f/reference/docs/trusted-base.html) | 内核不检查什么？ |
| [完成的结论依靠什么](https://www.dataisland.org/zlib-f/reference/docs/checking/README.html) | “完成”二字背后有哪些检查？ |
| [规格](https://www.dataisland.org/zlib-f/reference/docs/spec/README.html) | 安全目标、API 契约和格式说的是什么？ |
| [API](https://www.dataisland.org/zlib-f/reference/api.html) | 每个函数要求什么，保证什么？ |
| [设计](https://www.dataisland.org/zlib-f/reference/docs/design/README.html) | 翻译和内存模型是怎样工作的？ |
| [证明](https://www.dataisland.org/zlib-f/reference/docs/proof/README.html) | 各部分论证是怎样组合的？ |
| [术语表](https://www.dataisland.org/zlib-f/reference/docs/glossary.html) | 这些术语是什么意思？ |

## 自己检查这些证明

```bash
lake build ZlibF
scripts/check-sorry.sh
```

第一条命令编译所有模块，于是 Lean 内核检查了每个证明。源码中若还留有 `sorry`（被承认而没有证明的步骤），第二条命令就失败。还检查了什么，见[完成的结论依靠什么](docs/checking/README.md)。

## 在 zlib 中发现的问题

这项工作在固定版本的源码中发现了下列问题。每行给出复现、置信度和适用范围。最后两行是关于大小的承诺没有兑现，不是内存错误。[发现](docs/findings.md)有每个问题的完整说明和上游状态；[补丁说明](patches/README.md)描述每个补丁。

| 问题 | 是否在有文档的 API 之内 | 证据与置信度 | 被验证源码中的修复 |
| --- | --- | --- | --- |
| 流停在固定块内部时，`inflateCopy` 用关系运算符比较互不相关的指针，这是未定义行为 | 是 | 在固定版本的 C 上的[复现](docs/findings/inflate-copy-fixed/README.md)。对所诊断的调用序列置信度高。 | 补丁 0001，即上游 [PR #1369](https://github.com/madler/zlib/pull/1369) 的修复 |
| 一开始就调用 `gzungetc` 之后再调用 `gzseek`：`x.pos` 为 -1，`gzseek64` 的范围检查发生有符号溢出 | 是 | [复现](docs/findings/gzseek-pushback-overflow/README.md)：UndefinedBehaviorSanitizer 报告三处。置信度高。 | 补丁 0002，取自上游 [PR #1361](https://github.com/madler/zlib/pull/1361)，该拉取请求仍处于打开状态 |
| 透明模式下，部分读取之后读取失败，再调用 `gzread`：`gz_fetch` 在设置 `x.next` 之前就返回，读取函数从旧指针复制，读到缓冲区之外 | 是；需要在读到部分数据之后出现读取错误 | [复现](docs/findings/gzread-transparent-stale-next/README.md)：AddressSanitizer 报告这次读取。置信度高。 | 补丁 0003，上游 [PR #1363](https://github.com/madler/zlib/pull/1363)，该拉取请求仍处于打开状态 |
| gz 位置溢出：`gzread`、`gzgetc`、`gzgetc()` 宏、`gzwrite` 和 `gzputc` 把字节数加到有符号 64 位位置 `x.pos` 上，没有上界检查 | 是；出现在 `lseek` 成功却不移动的设备上（`/dev/zero`、`/dev/null`），或透明模式下位置接近 2^63 时 | [读取](docs/findings/gzread-pos-overflow/README.md)和[写入](docs/findings/gzwrite-pos-overflow/README.md)两个方向的复现：x86_64 Linux 上的 UndefinedBehaviorSanitizer。对所诊断的调用序列置信度高。其中一条路径经由 `gz_look` 的透明 COPY 分支，它在模型中并通过阅读 C 得到[确认](docs/findings/gz-position-copy-overflow.md)，没有 sanitizer 的确认：这段历史需要大约 2^63 个解码字节。 | 补丁 0004，本地补丁：尚未提交上游。位置保持在 `z_off64_t` 范围内，会溢出的调用以 `Z_DATA_ERROR` 失败；`gz_look` 的 COPY 分支也加了上界 |
| 对未设置或悬空的 `x.next` 前进零步：该字段从未写入，或指向已释放的调用者缓冲区时，`gzseek64` 和 `gz_skip_have` 执行 `x.next += 0` | 是；即两项发现中的两个调用序列 | [未设置](docs/findings/gz-reset-next-uninitialised/README.md)与[悬空](docs/findings/gz-next-dangling-after-direct-read/README.md)两种情形各有一次探针运行。按 C 标准的字面是未定义行为。证据弱于上面各行：sanitizer 对两种情形都不报告，也没有观察到异常行为。 | 补丁 0005，本地补丁：尚未提交上游 |
| `deflateResetKeep` 之后的 `deflateCopy`：两个待处理的 `prev` 槽没有被复制，之后在副本上调用 `deflate` 会沿着未初始化的槽走下去，`longest_match` 读到窗口之外 | 否：需要直接调用 `deflateResetKeep`，而 `zlib.h` 把它列为未文档化函数 | 在未修改的固定版本上的[复现](docs/findings/deflate-copy-pending-prev/README.md)：AddressSanitizer 报告这次读取，valgrind 报告未初始化的槽。对所诊断的调用序列置信度高。在 zlib 1.4（即固定的版本）上能复现，在 1.3.1 和 1.3.2 上不能。 | 没有。已证明的 deflate 定义域排除了这种调用（[偏离记录](docs/deviations.md)）。尚未报告上游；已有一份[报告草稿](docs/findings/deflate-copy-pending-prev-report.md)。 |
| `Z_FIXED` 策略、压缩级别 1 到 3、`windowBits` 为 15 且 `memLevel` 为 8 时，`deflateBound` 给出的上界偏小：按这个大小给出空间，一次 `deflate(Z_FINISH)` 调用返回 `Z_OK`，与 `zlib.h` 的承诺不符 | 是。这是没有兑现的承诺，不是内存错误；`compress`、`compress2` 和 `compressBound` 使用默认策略，不受影响 | 在未打补丁的 C 上的[复现](docs/findings/deflatebound-fixed-far-matches/README.md)，开启和不开启 sanitizer 都做过，sanitizer 没有任何报告。对所诊断的参数置信度高。系统自带的 zlib 1.2.12 在级别 1 到 9 上全部失败。尚未报告上游。上游是否已知，尚未向上游核实。 | 补丁 0006，本地补丁：尚未提交上游。安全目标都不依赖这个上界的数值 |
| gzip extra 字段长度为 2^32 − 2 或 2^32 − 1 时的 `deflateBound`：`2 + extra_len` 在 32 位上回绕，上界少了大约 64 KiB | 是。这是没有兑现的承诺，不是内存错误 | 在固定版本的 C 上的[复现](docs/findings/deflatebound-extra-len/README.md)。上游已知。 | 没有。安全目标都不依赖这个上界的数值 |

`inflateCopy` 和各 gz 函数的安全目标是针对打过补丁的源码陈述的。

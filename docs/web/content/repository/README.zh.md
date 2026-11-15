<!-- source-sha256: 1e95704edf2b00ecef4af8f946fcbaac0553df7c9c7920cb39f3ca8f018635fe -->
# zlib-f

用 Lean 4 证明 zlib 是安全的，证明由内核检查。C 源码被逐条语句翻译成 Lean；证明表明，默认 x86_64 Linux 构建中每个有文档的公开函数，在它的各种调用序列上运行时都没有未定义行为、没有内存错误、没有泄漏，并且终止。

**已证明。** 全部 63 个必需目标都有一个类型恰好相同的已登记定理，验收套件在提交 `bde170e9`（2026-11-15）上全部通过。必需目标是目标构建中 86 个有文档函数的安全目标和非空性目标：`inflate` 与 `deflate` 及其调用序列、其他流函数、校验和、`compress*` 与 `uncompress*`、gzip 文件接口，以及回调解码器 `inflateBack`。

**所作假设。** 内核只对照 Lean 命题检查证明，不检查运行时模型、手工翻译以及文件和格式化模型是否与 C 一致：这些靠审阅和测试，列在[可信基础](docs/trusted-base.md)中。差分测试是忠实度的证据，不是证明。有些定理带有 `zlib.h` 没有写出的前提：调用者的缓冲区互不重叠；gz 读取调用的终止需要低于 2^61 字节的读取预算；一次 `inflateBack` 调用得到的输入少于 2^48 字节。[偏离记录](docs/deviations.md)逐条列出。验证对象是固定版本的 `zlib/` 加上五个[补丁](patches/README.md)。

**未完成。** 31 个 gz 函数和三个 `inflateBack` 函数还没有各自的安全目标：它们目前都指向各自的序列目标（`Goal.gz_sequence_safety`、`Goal.inflate_back_sequence_safety`），这两个序列目标已登记。逐函数的目标尚待陈述和登记。

**不在计划内。** 功能正确性（`inflate` 的输出等于格式规定的内容，`deflate` 的输出能解码回输入），自 2026-11-11 起；只有计划内的安全证明所依赖的功能性事实仍在范围内，已经证明的部分保留。其他构建配置，以及 `zlib.h` 列为未文档化的函数，也不在计划内。[范围](docs/progress.md#scope)列出每一组及其理由。[状态页](https://www.dataisland.org/zlib-f/status.zh.html)根据证明记录，把每项结论显示为未完成、已检查或已登记。

## 目标

每个公开函数有两个目标，都在 Lean 命名空间 `ZlibF.Spec.Public.Goal` 中。它的**安全目标**陈述调用返回、没有未定义行为、只写自己的帧、不泄漏。它的**功能目标**在 `ZlibF/Spec/Functional/` 中，陈述结果是什么。`tests/audit/public-api.json` 为每个函数写出两者（`safety_goal`、`functional_goal`）。安全目标在 `ZlibF/Spec/Safety/` 中；gz 与 `inflateBack` 的目标仍在 `ZlibF/Spec/Public/` 中。验收审计要求安全目标和非空性目标：每个都必须在 `tests/audit/theorems.txt` 中有一个类型恰好相同的定理。清单中列出例外的 `open_safety` 现在为空。已证明的功能目标接受完整审计；未证明的不使任何检查失败。见[拆分说明](docs/design/safety-functional-split.md)。

## 文档

**[阅读文档网站](https://www.dataisland.org/zlib-f/)** · [网站内容源码](docs/README.md)

| 阅读入口 | 内容 |
| --- | --- |
| [证明总览](https://www.dataisland.org/zlib-f/reference/docs/overview.html) | 目标、假设和证明框架。 |
| [结果与状态](https://www.dataisland.org/zlib-f/status.zh.html) | 已确立什么，什么在计划内，什么不在。 |
| [全部目标的依赖图](https://www.dataisland.org/zlib-f/reference/docs/progress.html#proof-progress-graph) | 目标之间的依赖及各自覆盖的输入范围。 |
| [证据索引](https://www.dataisland.org/zlib-f/reference/docs/progress.html) | 每个目标的精确命题、证明和依赖。 |
| [规格](https://www.dataisland.org/zlib-f/reference/docs/spec/README.html) | 需要证明的安全、输入、API、内部函数和格式要求。 |
| [API](https://www.dataisland.org/zlib-f/reference/api.html) | 每个函数的前提和保证。 |
| [数据格式](https://www.dataisland.org/zlib-f/reference/docs/spec/format/README.html) | DEFLATE、zlib 和 gzip 字节的含义。 |
| [设计](https://www.dataisland.org/zlib-f/reference/docs/design/README.html) | 翻译方式与内存模型。 |
| [证明](https://www.dataisland.org/zlib-f/reference/docs/proof/README.html) | 各部分论证的组合方式。 |
| [检查](https://www.dataisland.org/zlib-f/reference/docs/checking/README.html) | 什么算已检查，什么算已验收。 |
| [参与贡献](https://www.dataisland.org/zlib-f/reference/docs/checking/contributing.html) | 运行哪些命令，按什么顺序？ |
| [术语表](https://www.dataisland.org/zlib-f/reference/docs/glossary.html) | 这些术语是什么意思？ |

## 仓库结构

- `zlib/`：固定版本的上游源码；不直接修改，修复补丁放在 `patches/`。
- `ZlibF/Zlib/`：逐条语句翻译的 C 实现。
- `ZlibF/Spec/Safety/`：必需的安全目标。`ZlibF/Spec/Functional/`：功能契约、格式模型和 API 模型。`ZlibF/Spec/Public/`：两者共用的定义。
- `ZlibF/Proof/` 和 `ZlibF/Math/`：实现证明和不涉及堆的数学推导。
- `ZlibF/Runtime/`：内存、指针、算术和执行语义。
- `tests/`：差分测试、变异测试和证明审计。

## 本地检查

```bash
lake build ZlibF
scripts/check-sorry.sh
```

[参与贡献](docs/checking/contributing.md)列出每一步。各项检查的范围和最终验收条件见[检查指南](https://www.dataisland.org/zlib-f/reference/docs/checking/README.html)。差分测试是翻译忠实度的证据，不是证明。
[源码问题记录](docs/findings.md)列出问题的证据强度和适用范围。

## 源码问题：deflateResetKeep 之后的 deflateCopy

直接调用 `deflateResetKeep` 并调用一次 `deflate(Z_BLOCK)` 之后，有两个链头等待插入；`deflateCopy` 不复制它们的 `prev` 槽，副本上的一次 `Z_RLE` 或 `Z_HUFFMAN_ONLY` 刷新以 `insert = 0` 结束，所以它们不会被重新插入。之后一次默认策略的 `deflate` 会沿一个未初始化的 `prev` 槽前进，`longest_match` 读到窗口之外。[保留的复现](docs/findings/deflate-copy-pending-prev/README.md)在 x86_64 Linux 上诊断固定的、未修改的 C：AddressSanitizer 报告窗口之外的读取，valgrind 报告使用了未初始化的槽。对诊断出的序列，置信度高。它在 zlib 1.4 和固定的 `develop` 上复现，不在 1.3.1 或 1.3.2 上复现（部分复制随 1.3.2 引入，丢弃前瞻随 1.4 引入）。范围：它需要 `deflateResetKeep`，zlib.h 把该函数声明为未文档化、不属于 zlib API，所以这不是已文档化 API 的缺陷；已证明的 deflate 流定义域排除了它（[偏差](docs/deviations.md)）。已写好一份[报告草稿](docs/findings/deflate-copy-pending-prev-report.md)，没有向上游发送任何内容。

## 源码问题：gz 位置溢出

`gzread` 和 `gzwrite` 把搬运的字节数加到有符号 64 位位置 `x.pos` 上，不做上界检查。在位置能到达 2^63 − 1 的透明文件上，这个加法会溢出，是未定义行为。读取：在 `lseek` 成功却不移动的设备上（Linux 上的 `/dev/zero`），`gzseek(INT64_MAX, SEEK_SET)` 被接受，随后的 `gzread` 在 `gz_read`、`gzgetc` 和 `gzgetc()` 宏中溢出（[复现](docs/findings/gzread-pos-overflow/README.md)）。写入：透明写入者在 `/dev/null` 上定位到接近 2^63 之后，`gzwrite` 和 `gzputc` 溢出（[复现](docs/findings/gzwrite-pos-overflow/README.md)）。在 x86_64 Linux 上用固定版本的 C，UndefinedBehaviorSanitizer 报告了两者。对诊断出的序列，置信度高。范围：`lseek` 成功却不移动的设备，或接近 2^63 的透明位置。验证对象包含一个本地修复，[补丁 0004](patches/README.md)，经所有者批准，尚未提交上游：位置保持在 `z_off64_t` 之内，会溢出的调用以 `Z_DATA_ERROR` 失败。

该修复中的一个缺口：`gz_look` 的透明 COPY 分支缓冲至多 `size` 个字节，不受剩余空间的限制。所以在一个带尾部数据的 gzip 成员、`gzclearerr` 和一次接近 2^63 − 1 的读取之后，读取者返回时 `x.pos + x.have` 超过 `GZ_OFF_MAX`，随后 `gzgetc()` 宏使 `x.pos` 溢出（[发现](docs/findings/gz-position-copy-overflow.md)）。已在模型中确认，也已通过阅读 C 确认；实际中无法复现（约 2^63 个解码字节）；没有 sanitizer 确认。对按所写的打过补丁的源码，置信度高。范围：带补丁 0004、在这段历史之后位置距 `GZ_OFF_MAX` 不到 `size` 个字节的读取者。补丁 0004 现在也限制了这个分支。

## 源码修复

使用默认参数初始化的流如果在固定块中途暂停，`inflateCopy` 会比较静态固定码表与单独分配的状态码数组。保留的[复现材料](docs/findings/inflate-copy-fixed/README.md)诊断了固定版本中未经修改的 C。现在验证的源码通过[临时补丁](patches/README.md)采用了[上游 PR #1369](https://github.com/madler/zlib/pull/1369) 中完全相同的修复；Lean 翻译也使用相同的相等性检查。对于已诊断的 LP64 问题，证据置信度高；公开 `inflateCopy` 的完整证明仍未完成，且在计划内：`inflateCopy` 是 `inflate_sequence` 所涉及的流调用。

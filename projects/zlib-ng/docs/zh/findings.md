# 发现：zlib-ng 中发现的问题

本工作在被验证提交的 zlib-ng `develop` 分支中发现了三个问题。每个都是 zlib-ng 自身的缺陷，可通过 `zlib.h`
有文档的函数触达，并由真实 C 代码的运行（其中一处由 ISO C17 条文）展示。补丁 0003、0004 与 0006 修复了它们。

| 问题 | 错在哪里 | 触达的调用 | 证据 | 修复 | 上游 |
| --- | --- | --- | --- | --- | --- |
| `inflateCopy` 比较无关指针 | `inflateCopy` 用 `>=` 与 `<=` 比较指向静态表 `lenfix` 的指针与指向堆状态的指针：未定义行为（ISO C17 §6.5.8p5）。 | 对处于固定编码块内的流调用 `inflateCopy` | AddressSanitizer 指针对检查，`inflate.c:1410` | 补丁 0003 | 未提交 |
| `gzseek` 偏移溢出 | `gzseek64` 在 `SEEK_CUR` 下无界地把待跳过量加到偏移上：64 位有符号溢出。在首次读取之前还会对从未赋值的 `x.next` 加 0。 | 以写模式 `gzopen`，`gzseek(file, INT64_MAX, SEEK_SET)`，`gzseek(file, 1, SEEK_CUR)` | UndefinedBehaviorSanitizer，`gzlib.c:412` | 补丁 0004 | 未提交 |
| gzip 额外字段长度很大时 `deflateBound` 过小 | 对带额外字段的用户 gzip 头，`deflateBound` 以 32 位 `unsigned` 计算 `2 + extra_len`，在 `extra_len >= 0xfffffffe` 时回绕，而 `deflate` 写出 `2 + (extra_len & 0xffff)` 个头字节。于是以 `avail_out = deflateBound(...)` 进行一次 `deflate(Z_FINISH)` 不返回 `Z_STREAM_END`，违背 `zlib.h`。 | gzip 模式 `deflateInit2`，`extra_len = 0xffffffff` 的 `deflateSetHeader`，`deflateBound`，`deflate(Z_FINISH)` | 真实 C 代码返回 `Z_OK` 而非 `Z_STREAM_END` | 补丁 0006 | 未提交 |

早先 2.3.3 版本中发现的问题（`gzbuffer` 大小溢出、负长度时 `crc32_combine*` 不返回、`adler32` 以 `NULL`
和长度 1 调用）已在 `develop` 分支修复；它们的复现保留为回归测试。

这些运行在被验证源码按被验证配置（参见[概述](index.html)）的 LP64 构建上进行，应用了除修复该问题的补丁之外的
所有补丁，而非在 x86_64 Linux 目标本身上。应用全部补丁后，这些调用均无消毒器报告并正常返回。

消毒器报告或真实 C 代码的运行只是关于那次运行的证据，不是证明。安全性定理针对的是打过补丁的源码。

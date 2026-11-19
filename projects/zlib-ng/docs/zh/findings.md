<!-- source-sha256: 3d5b6f289d20b9517fdde60c5cb6671edf9636a0f582ded68a135447caf935b7 -->
# 发现的问题：zlib-ng 中的缺陷

本工作在 zlib-ng 2.3.3 中发现了五个问题。每个都是 zlib-ng 自身的缺陷，可通过 `zlib.h` 有文档的函数触达，
并由真实 C 代码的运行展示。补丁 0001 至 0004 与补丁 0007 修复了它们。

| 问题 | 错误之处 | 触达它的调用 | 证据 | 修复 | 上游 |
| --- | --- | --- | --- | --- | --- |
| `gzbuffer` 大小溢出 | `gzbuffer` 接受最大 `0x7fffffff` 的大小。随后 `gz_buffer_alloc` 以 `int` 计算 `want * 2`（有符号溢出），`zng_alloc_aligned` 以 32 位计算 `sizeof(void *) + size + align`，回绕为 8：只分配 8 字节，却把保存的指针写到块外。 | 以写模式 `gzopen`，`gzbuffer(file, 0x55555540)`，`gzwrite` | UndefinedBehaviorSanitizer，`gzlib.c:76`；AddressSanitizer 堆缓冲区溢出，`zutil.c:135` | 补丁 0001 | 未提交 |
| `crc32_combine*` 不返回 | 负的 `len2` 使 `x2nmodp` 永远右移 `-1`；`op == 0` 使 `multmodp` 永远找不到置位。 | `crc32_combine(crc1, crc2, -1)`、`crc32_combine_gen(-1)`、`crc32_combine_op(crc1, crc2, 0)` | 真实 C 代码运行 10 秒内未返回 | 补丁 0002 | 未提交 |
| `inflateCopy` 比较无关指针 | `inflateCopy` 用 `>=` 与 `<=` 比较指向静态表 `lenfix` 的指针和指向堆状态的指针：未定义行为（ISO C17 §6.5.8p5）。 | 对处于固定编码块中的流调用 `inflateCopy` | AddressSanitizer 指针对检查，`inflate.c:1399` | 补丁 0003 | 未提交 |
| `gzseek` 偏移溢出 | `gzseek64` 在 `SEEK_CUR` 时把待跳过量无界地加到偏移上：64 位有符号溢出。 | 以写模式 `gzopen`，`gzseek(file, INT64_MAX, SEEK_SET)`，`gzseek(file, 1, SEEK_CUR)` | UndefinedBehaviorSanitizer，`gzlib.c:388` | 补丁 0004 | 未提交 |
| `adler32` 以 `NULL` 和长度 1 调用 | `zlib.h` 规定 `buf == Z_NULL` 时 `adler32` 返回初始值。zlib-ng 在检查 `NULL` 之前处理 `len == 1`，经由空指针读取。 | `adler32(1, Z_NULL, 1)` | UndefinedBehaviorSanitizer 空指针读取，`adler32_p.h:22`；AddressSanitizer SEGV | 补丁 0007 | 未提交 |

这些运行在 zlib-ng 2.3.3 源码按被验证配置（参见[概述](index.html)）的 LP64 构建上进行，应用了除修复该问题的补丁之外的
所有补丁，而非在 x86_64 Linux 目标本身上。应用全部补丁后，这些调用都在没有消毒器报告的情况下运行并返回。

消毒器报告或真实 C 代码的运行只是关于那次运行的证据，不是证明。安全性定理针对打过补丁的源码。

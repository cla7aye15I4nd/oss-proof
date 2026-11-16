<!-- source-sha256: 6706e038be08ffa8fad1de656040d2dc034bf85668032076eb1dfac0325438b7 -->
# `deflateResetKeep` 之后的 `deflateCopy`：`longest_match` 读到窗口之外

直接调用 `deflateResetKeep` 之后，由 `deflateCopy` 得到的流可能在散列链表 `prev` 中带有两个未初始化的项。之后在副本上调用 `deflate` 会沿着其中一个走下去，`longest_match` 于是读到窗口之外。这个序列需要 `deflateResetKeep`，而 `zlib.h` 把它列为不属于 zlib API，所以这不是文档 API 的缺陷。

本页给出状态、复现以及与证明的关系。机制、受影响的发行版、影响和可能的修复在[报告草稿](../deflate-copy-pending-prev-report.md)中；那份草稿是写给 zlib 维护者的，没有寄出。

## 状态

- 内存错误：先读取一个未初始化的表项，然后读到窗口之外的堆内存。
- 在上游 `develop` 的提交 `757f0527154291bcf6bfbd6396ecde6bedd2db95` 上，由 AddressSanitizer 和 valgrind 在 x86_64 Linux（GCC 14）上报告；arm64 macOS 上有同样的 AddressSanitizer 报告。本仓库的补丁不涉及 deflate 的源文件。
- 在文档 API 之外：它需要直接调用 `deflateResetKeep`。
- 没有报告给上游。没有补丁：证明排除了这个调用（[偏离记录](../../deviations.md)，“直接调用 `deflateResetKeep`”一行）。

## 调用序列

```c
deflateInit2(&a, 6, Z_DEFLATED, 9, 8, Z_DEFAULT_STRATEGY);   /* windowBits 9：1024 字节的窗口缓冲区 */
/* 600 字节输入 */
deflate(&a, Z_NO_FLUSH);
deflateResetKeep(&a);               /* 保留窗口和散列，丢弃预读 */
deflate(&a, Z_BLOCK);               /* 无输入：insert 变为 2 */
deflateCopy(&c, &a);                /* 只复制 strstart - insert 以下的 prev */
deflateParams(&c, 6, Z_RLE);
deflate(&c, Z_SYNC_FLUSH);          /* 无输入：deflate_rle 把 insert 设为 0 */
deflateParams(&c, 6, Z_DEFAULT_STRATEGY);
/* 以 strstart - 2 处三个窗口字节开头的输入 */
deflate(&c, Z_FINISH);              /* longest_match 沿着未初始化的 prev 项走下去 */
```

每个缓冲区都有效且互不重叠，每个调用都是对导出函数的调用。完整程序是 [`repro.c`](repro.c)；回归测试目录中的 [`copy.c`](../../../tests/regression/deflate-copy-pending-prev/copy.c) 是同一个驱动程序。它包含 `deflate.h`，只为读取 `strstart` 和三个窗口字节，以及打印状态。它安装一个用 16 位值 1030 填充新分配内存的分配器，使候选位置正好落在 1024 字节的窗口之后，报告因而是确定的。带参数 `plain` 时使用默认分配器。

## 运行

在仓库根目录，`zlib/` 子模块已检出：

```sh
ZLIB_SRC=$PWD/zlib bash tests/regression/deflate-copy-pending-prev/run.sh
```

脚本用 `-fsanitize=address,undefined -g -O1` 构建 zlib 并运行 `copy.c`；AddressSanitizer 必须报告 `longest_match` 中的读取。装有 valgrind 时，它还会不带 sanitizer 再构建一次，并在 memcheck 下运行 `copy plain`，memcheck 必须报告对未初始化项的使用。检查成立时脚本以状态 0 退出。第一项检查打印的一行是：

```
ok: deflateCopy after deflateResetKeep, then Z_RLE: longest_match reads past the window
```

## Sanitizer 判定

摘自 [`report.txt`](../../../tests/regression/deflate-copy-pending-prev/report.txt)，x86_64 Linux：

```
==PID==ERROR: AddressSanitizer: heap-buffer-overflow on address 0x519000000e89 at pc 0x0000004033f1 bp 0x7ffe4828dba0 sp 0x7ffe4828db98
READ of size 1 at 0x519000000e89 thread T0
    #0 0x4033f0 in longest_match deflate.c:1511
    #1 0x4095b4 in deflate_slow deflate.c:2029
    #2 0x41ef85 in deflate deflate.c:1239
0x519000000e89 is located 7 bytes after 1026-byte region [0x519000000a80,0x519000000e82)
```

这个区域是副本的窗口，在 `deflateCopy`（`deflate.c:1361`）中分配。使用默认分配器时，同一文件中 valgrind 的报告：

```
==PID== Conditional jump or move depends on uninitialised value(s)
==PID==    at 0x40176B: longest_match (deflate.c:1555)
==PID==  Uninitialised value was created by a heap allocation
==PID==    by 0x404C6F: deflateCopy (deflate.c:1362)
```

在 arm64 macOS 上运行了一次，在 `deflate.c:1511` 得到同样的 AddressSanitizer 报告；那里没有 valgrind。

## 范围与严重程度

- **谁会遇到。** 在流的中途直接调用 `deflateResetKeep`，然后调用 `deflateCopy`，再把副本的策略改为 `Z_RLE`（或 `Z_HUFFMAN_ONLY`）又改回来的程序。只靠数据不能触发它：只能控制被压缩字节的攻击者决定不了这些调用。
- **后果。** 先读取未初始化的内存，然后在距窗口起点至多 65535 的偏移处读取至多 258 个字节。没有观察到写入。压缩输出可能依赖于读到的字节。
- **发行版。** 报告出现在 zlib 1.4 和上述 `develop` 提交上，在 1.3.1 和 1.3.2 上不出现（AddressSanitizer，arm64 macOS，同一驱动程序）。报告草稿写明了缺一不可的两个上游提交。
- **严重程度。** 对这样使用 `deflateResetKeep` 的程序是中等；对只用文档 API 的程序没有影响。

## `zlib.h` 的说法

`deflateResetKeep` 声明在注释 “`undocumented functions (not part of the zlib API)`”（未文档化的函数，不属于 zlib API）之下（`zlib.h:2043`，声明在第 2051 行）。`deflateCopy`、`deflateParams` 和 `deflate` 是有文档的，zlib.h 没有提到在 `deflateResetKeep` 之后怎样使用它们。

## 修复

这里没有应用任何修复，也没有向上游寄出任何修复。报告草稿列出了三种可能的修复。其中一种只在这个复现上试过：把 `deflateCopy` 改为复制 `prev` 的全部 `w_size` 项之后，没有报告，`deflate` 返回 `Z_STREAM_END`。

## 与证明的关系

deflate 的安全目标把直接调用 `deflateResetKeep` 排除在它们覆盖的调用历史之外。这个发现就是该排除不能去掉的原因：有了这个调用，`deflate` 可能读到窗口之外。

没有这个调用时，对 `prev` 的部分复制是可靠的，而且这是一个定理。按报告草稿中机制的编号：

- 没有第 2 步（`deflateResetKeep`），就没有等待插入的链头：每个非零的 `head` 项都在 `strstart - insert` 以下。对满足 deflate 不变量 `DInv` 的状态，没有待执行的滑动时（前提 `matches = 0`），这就是 `DInv.heads_inserted`。在级别 0、有一次待执行滑动时（前提 `matches = 1`），这是 `DInv.slid_heads_inserted`，说的是这次滑动执行之后的各项。`DInv` 在 deflate 流定义域的历史所到达的每个状态中都成立：这是定理 `reachable_inv_of`，它唯一的前提 `SequenceFacts` 就是定理 `sequence_facts`。有两次或更多待执行滑动时（级别 0），不变量对这些表不作任何断言，而 `deflateParams` 会在非零级别运行之前清空它们。
- 没有第 4 步（`deflateCopy`），这两个项保存着那两个位置插入时写下的值。
- 没有第 5 步（`Z_RLE` 刷新），`fill_window` 会在任何 `longest_match` 之前插入这两个位置，从而重写它们的项。

在真实 C 上运行的检查器在 460 万个抽样状态上与第一条命题一致。这是证据，不是证明。

允许 `deflateResetKeep` 的按位置的散列链不变量，在第 5 步之后不成立。不带复制时相关的数据错误见 [deflate-resetkeep-stale-hash](../deflate-resetkeep-stale-hash/README.md)。

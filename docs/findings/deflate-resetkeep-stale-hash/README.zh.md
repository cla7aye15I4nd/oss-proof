<!-- source-sha256: be4be52ff40f17a46f0f920748d3ffb714c186f6ec971ceba9e797dec70eb46b -->
# `deflateResetKeep`：过时的散列项可能产生错误的匹配

在流的中途直接调用 `deflateResetKeep` 之后，下一个流里可能出现第三个字节不对的匹配，于是它解码出的数据与输入不同。这是数据错误，不是内存错误，没有 sanitizer 会报告它。`zlib.h` 把 `deflateResetKeep` 列为不属于 zlib API。

## 状态

- 在固定的源码（`757f0527154291bcf6bfbd6396ecde6bedd2db95`，上游 `develop`）上复现，平台为 arm64 macOS，不带 sanitizer。
- 它是不是 zlib 的缺陷，尚未向上游核实：zlib.h 没有说明 `deflateResetKeep` 的预期用法。
- 没有报告给上游。没有补丁：证明排除了直接调用 `deflateResetKeep`（[偏离记录](../../deviations.md)，“直接调用 `deflateResetKeep`”一行）。

## 调用序列

```c
deflateInit2(&s, level, Z_DEFLATED, -wb, mem, Z_DEFAULT_STRATEGY);   /* 裸 deflate */
/* 输入 A */
deflate(&s, Z_NO_FLUSH);            /* 窗口里留有预读 */
deflateResetKeep(&s);               /* 保留窗口和散列，丢弃预读 */
/* 输入 B */
deflate(&s, Z_FINISH);              /* 第二个流 */
```

第二个流可以引用保留下来的窗口 `window[0 .. strstart)`。把这些字节当作预置字典来解码，应当得到 B。在某些历史中却得不到。

原因：`deflateResetKeep` 保留 `strstart`，把 `lookahead` 设为 0。散列里仍有位置 `strstart - 2` 和 `strstart - 1`，它们插入时所用的三字节键延伸到了已被丢弃的预读里。下一次 `deflate` 调用从 `strstart` 起写入新的输入。`longest_match` 不比较候选的第三个字节（它依赖散列键相等），所以一个过时的候选可能在第三个字节不对的情况下被接受。

完整程序是 [`repro.c`](repro.c)。它按种子逐个尝试随机的参数和输入，找到三个解码结果与 B 不同的历史后停止。它包含 `deflate.h`，用来读取 `strstart` 和保留下来的窗口。

## 运行

在仓库根目录，`zlib/` 子模块已检出：

```sh
cc -I zlib docs/findings/deflate-resetkeep-stale-hash/repro.c \
   zlib/{adler32,crc32,deflate,inflate,inftrees,inffast,trees,zutil}.c -o stale-hash
./stale-hash
```

为撰写本页在 arm64 macOS 上运行一次的输出（退出状态 1）：

```
MISMATCH seed 13 level 8 wb 15 mem 3 alpha 5 na 508 nb 1292 rc 1 got 1292 first diff 680
MISMATCH seed 35 level 6 wb 12 mem 6 alpha 4 na 2204 nb 1041 rc 1 got 1041 first diff 989
MISMATCH seed 40 level 8 wb 11 mem 9 alpha 4 na 913 nb 1754 rc 1 got 1754 first diff 437
tried 41 bad 3
```

每个 `MISMATCH` 行是一个历史：`inflate` 返回 `Z_STREAM_END`（`rc 1`），长度正确，而 `first diff` 处的字节与输入不同。前 41 个完成的历史中有三个不同。

## Sanitizer 判定

没有。这些历史中既没有越界访问，也没有未定义的算术；错误出在数据上。没有保留 `report.txt`。

## 范围与严重程度

- **谁会遇到。** 在一次留下预读的 `deflate` 调用之后直接调用 `deflateResetKeep`，然后用同一个流继续压缩数据的程序。
- **后果。** 压缩流解码出的数据与输入不同。没有内存错误。`deflate` 和 `inflate` 都不返回错误码。
- **严重程度。** 对这样的程序：无声的数据损坏。对只用文档 API 的程序：没有影响，因为 `deflateReset` 在 `deflateResetKeep` 之后会清空散列。

历史中再加上 `deflateCopy`，同样的过时项会导致内存错误：[deflate-copy-pending-prev](../deflate-copy-pending-prev/README.md)。

## `zlib.h` 的说法

`deflateResetKeep` 声明在注释 “`undocumented functions (not part of the zlib API)`”（未文档化的函数，不属于 zlib API）之下（`zlib.h:2043`，声明在第 2051 行）。它的用法没有说明。

## 修复

这里没有应用任何修复。`repro.c` 中记录了一次实验：在 `deflateResetKeep` 里 `s->lookahead = 0;` 之后加上 `CLEAR_HASH(s)`，200000 个历史中没有一个不同。撰写本页时没有重新做这个实验。

## 与证明的关系

直接调用 `deflateResetKeep` 之后，deflate 不变量 `DInv` 的散列链子句不成立。因此安全目标的 deflate 流定义域里没有这样的调用，也没有定理覆盖这个历史。

在这个不带 `deflateCopy` 的历史中，没有发现内存错误。对 C 的解读是：无论散列键是什么，`longest_match` 都只读取窗口之内的字节。这一解读**尚未由证明确认**；只要这个调用仍在已证明的定义域之外，本项目的证明就不会确认它。

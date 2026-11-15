<!-- source-sha256: 0c8a14d87d4f494482582ecec39c6926b2365cfc124b8351818b5684e90b2916 -->
# `inflateCopy` 比较指向无关对象的指针

对停在固定码块内部的流调用 `inflateCopy` 时，它用 `>=` 和 `<=` 比较一个指向静态表的指针和一个指向堆上 inflate 状态的指针。C 只对指向同一对象的指针定义这两个运算符。zlib 的维护者只读本页，就能复现这份报告并作出判断。

## 状态

- 按 C 标准是未定义行为（C11 6.5.8p5：对指向不同对象的指针做关系比较）。在 `inflateCopy` 的文档用法之内。
- 在未修改的固定版本源码（`757f0527154291bcf6bfbd6396ecde6bedd2db95`，上游 `develop`）上，由 AddressSanitizer 的指针对检查报告，平台为 x86_64 Linux 和 arm64 macOS。
- 没有观察到错误结果：不开指针对检查时，同一程序的 `inflateCopy` 返回 `Z_OK`。
- 修复已作为 [PR #1369](https://github.com/madler/zlib/pull/1369) 提交上游。维护者于 2026-11-06 答复“Applied”。2026-11-14 读取的上游 `develop` 头部（`99623ef7`）还不包含它。验证对象把所提交的那个提交作为[补丁 0001](../../../patches/README.md) 应用。

## 调用序列

```c
z_stream strm, copy;
unsigned char out[1];
memset(&strm, 0, sizeof strm);
memset(&copy, 0, sizeof copy);
inflateInit(&strm);                 /* 默认：zlib 封装，32K 窗口 */
strm.next_in = encoded;             /* 一个 zlib 流，唯一的块是固定码块 */
strm.avail_in = sizeof encoded;
strm.next_out = out;
strm.avail_out = 1;                 /* 只够放一个字节 */
inflate(&strm, Z_NO_FLUSH);         /* 在固定码块内返回 Z_OK：state->lencode 是静态的 lenfix */
inflateCopy(&copy, &strm);          /* inflate.c:1383：state->lencode >= state->codes */
```

`encoded` 有 23 个字节：一个 zlib 头和一个最终固定码块，解码为 2048 个字节 `A`。完整程序是 [`repro.c`](repro.c)。没有哪个缓冲区过小，也没有两个缓冲区重叠。

固定版本 `inflate.c` 中的语句（第 1383 和 1384 行）：

```c
if (state->lencode >= state->codes &&
    state->lencode <= state->codes + ENOUGH - 1) {
```

`state->codes` 是 inflate 状态内部的数组，该状态由 `inflateInit` 分配。在固定码块内，`state->lencode` 指向静态表 `lenfix`。

## 运行

在仓库根目录，`zlib/` 子模块已检出：

```sh
python3 docs/findings/inflate-copy-fixed/reproduce.py
```

脚本把 `repro.c` 与未修改的 `zlib/` 中六个解码器源文件一起编译，选项为 `-O1 -g -fsanitize=address,pointer-compare,pointer-subtract -fno-omit-frame-pointer`，运行时设置 `ASAN_OPTIONS=detect_invalid_pointer_pairs=2:detect_leaks=0`。`CC` 选择编译器（默认是 `clang`）。只有运行以错误退出、并打印出点名 `inflateCopy` 和 `lenfix` 的指针对报告，脚本才算成功；编译错误不算。成功时最后一行是：

```
CONFIRMED: default-init fixed-block inflateCopy compares unrelated objects
```

## Sanitizer 判定

摘自 [`report.txt`](report.txt)，x86_64 Linux：

```
inflate=0 produced=1 fixed_block=1
==PID==ERROR: AddressSanitizer: invalid-pointer-pair: 0x5a0a568b10a0 0x78f4037e0668
    #0 0x5a0a568ab70f in inflateCopy zlib/inflate.c:1383
0x5a0a568b10a0 is located 0 bytes inside of global variable 'lenfix' defined in 'zlib/inffixed.h:10:19' (0x5a0a568b10a0) of size 2048
0x78f4037e0668 is located 1384 bytes inside of 7176-byte region [0x78f4037e0100,0x78f4037e1d08)
```

这是报告中的五行；7176 字节的区域是 `inflateInit2_`（`inflate.c:206`）分配的 inflate 状态。为撰写本页在 arm64 macOS（Apple clang）上运行了一次，在同一行得到相同的判定。

## 范围与严重程度

- **谁会遇到。** 对任何处在固定码块内部的流调用 `inflateCopy`：默认的 `inflateInit` 或任意 `inflateInit2`，任何含有固定码块的输入，以及一次在该块结束之前返回的 `inflate` 调用。
- **后果。** 没有观察到后果。在平坦地址空间的平台上，这个比较就是地址比较；对静态表它为假，副本保留指向静态表的指针，这是正确的。`distcode` 同理。风险只在于编译器可以假定这是指向同一对象的两个指针之间的比较。
- **严重程度。** 低：严格说是未定义行为，但没有内存错误，没有错误输出；压缩数据除了要用到固定码块之外，不能控制它。

## `zlib.h` 的说法

`inflateCopy`“把目的流设置为源流的完整副本”（`zlib.h:974`）。它对源流停在流中何处没有任何条件，所以上面的调用序列是文档用法。

## 修复

[PR #1369](https://github.com/madler/zlib/pull/1369)，提交 `300fea14353d2e2ca61210aca7c48861ded5788c`：用指针相等 `state->lencode == state->codes` 判断这张表是否属于状态自身，代替那两个关系比较。只要 `lencode` 指向状态自己的数组，它就指向数组开头：`inflate.c` 在 `state->next = state->codes` 之后紧接着用 `state->next` 给它赋值（第 118、820 和 898 行）。所以相等判断选出的情形与原来相同。随后 `copy->lencode` 被设为 `copy->codes`，`distcode` 保持原来的偏移。

[补丁 0001](../../../patches/README.md) 正是这个提交。上游分支包含该修复、固定版本越过它之后，补丁就会删除。

## 与证明的关系

Lean 翻译跟随打过补丁的源码。在指针模型中，对指向不同对象的两个指针比较大小是故障，所以未打补丁的语句无法被证明是安全的。本页的复现有意构建未打补丁的源码。[复制回归测试](../../../tests/regression/inflate-copy/README.md)构建打过补丁的源码，并把真实 C 中成功的 `inflateCopy` 调用与翻译比较；这种比较是忠实性的证据，不是证明。

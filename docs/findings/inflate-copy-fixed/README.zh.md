<!-- source-sha256: 87afa1386cf3207de7cf6578188a4dd6f74596621cab4c5312964c55aecb418b -->
# `inflateCopy` 比较指向无关对象的指针

如果一个流已经解码过固定码块，而且之后没有解码过动态码块，对它调用 `inflateCopy` 时，它用 `>=` 和 `<=` 比较一个指向静态表的指针和一个指向堆上 inflate 状态的指针。C 只对指向同一对象的指针定义这两个运算符（C11 6.5.8p5），所以这次比较是未定义行为。

该语句在不打补丁的 `inflate.c` 中（第 1383 和 1384 行）：

```c
if (state->lencode >= state->codes &&
    state->lencode <= state->codes + ENOUGH - 1) {
```

`state->codes` 是 inflate 状态内部的数组，该状态由 `inflateInit` 分配。从固定码块开始起，`state->lencode` 指向静态表 `lenfix`。

## 到达它的调用

```c
z_stream strm, copy;
unsigned char out[1];
memset(&strm, 0, sizeof strm);
memset(&copy, 0, sizeof copy);
inflateInit(&strm);                 /* 默认：zlib 封装，32K 窗口 */
strm.next_in = encoded;             /* 一个 zlib 流，唯一的块是固定码块 */
strm.avail_in = sizeof encoded;
strm.next_out = out;
strm.avail_out = 1;                 /* 只有一个字节的空间 */
inflate(&strm, Z_NO_FLUSH);         /* 在固定码块内返回 Z_OK：state->lencode 是静态的 lenfix */
inflateCopy(&copy, &strm);          /* inflate.c:1383：state->lencode >= state->codes */
```

`encoded` 有 23 个字节：一个 zlib 头和一个最终的固定码块，解码为 2048 个字节 `A`。完整程序是 [`repro.c`](repro.c)。没有缓冲区过小，也没有两个缓冲区重叠。

只要流的 `lencode` 是静态表，对它调用 `inflateCopy` 就会到达这条语句：任何 `inflateInit` 或 `inflateInit2`，以及任何含有固定码块的输入。`inflate` 遇到固定码块时把 `lencode` 指向静态表。这个指针一直留在那里，直到动态码块替换它或者流被重置；存储块不改变它。所以复制可以发生在固定码块之内、之后，或者流结束之后。

`zlib.h` 说 `inflateCopy` 的作用是 `Sets the destination stream as a complete copy of the source stream`（把目标流设置为源流的完整副本，`zlib.h:974`）。它对源流停在流中的什么位置没有任何条件。

## 证据

在不打补丁的 C 上，AddressSanitizer 的指针对检查报告这次比较。在仓库根目录、已检出 `zlib/` 子模块时运行：

```sh
python3 docs/findings/inflate-copy-fixed/reproduce.py
```

脚本把 `repro.c` 与未修改的 `zlib/` 中的六个解码器源文件一起编译，使用 `-O1 -g -fsanitize=address,pointer-compare,pointer-subtract -fno-omit-frame-pointer`，并以 `ASAN_OPTIONS=detect_invalid_pointer_pairs=2:detect_leaks=0` 运行。`CC` 选择编译器（默认是 `clang`）。只有当运行以错误退出，并且打印出指名 `inflateCopy` 和 `lenfix` 的指针对报告时，脚本才成功。成功时它的最后一行是：

```
CONFIRMED: default-init fixed-block inflateCopy compares unrelated objects
```

摘自 [`report.txt`](report.txt)，x86_64 Linux：

```
inflate=0 produced=1 fixed_block=1
==PID==ERROR: AddressSanitizer: invalid-pointer-pair: 0x5a0a568b10a0 0x78f4037e0668
    #0 0x5a0a568ab70f in inflateCopy zlib/inflate.c:1383
0x5a0a568b10a0 is located 0 bytes inside of global variable 'lenfix' defined in 'zlib/inffixed.h:10:19' (0x5a0a568b10a0) of size 2048
0x78f4037e0668 is located 1384 bytes inside of 7176-byte region [0x78f4037e0100,0x78f4037e1d08)
```

那个 7176 字节的区域是 `inflateInit2_` 分配的 inflate 状态。arm64 macOS 在同一行给出同样的判定。

## 影响

没有观察到错误结果：不开指针对检查时，同一程序的 `inflateCopy` 返回 `Z_OK`。在地址空间平坦的平台上，这次比较就是地址比较，对静态表它为假，副本保留指向静态表的指针，这是正确的。`distcode` 也是如此。风险在于编译器可以假定这次比较的两个指针指向同一对象。

## 修复

[补丁 0001](../../../patches/README.md) 用指针相等 `state->lencode == state->codes` 来判断表是不是状态自己的，取代那两个关系比较。只要 `lencode` 指向状态自己的数组，它就指向数组的开头：`inflate.c` 总是在 `state->next = state->codes` 之后紧接着用 `state->next` 给它赋值。所以相等判断选出的情形相同。之后 `copy->lencode` 被设为 `copy->codes`，`distcode` 保持它的偏移。

上游：该补丁就是[拉取请求 #1369](https://github.com/madler/zlib/pull/1369) 的提交，维护者答复“Applied”。zlib 1.4 中没有它。

## 与证明的关系

Lean 翻译遵循打过补丁的源码。在指针模型中，对指向不同对象的两个指针比较大小是故障，所以不打补丁的语句无法被证明是安全的。

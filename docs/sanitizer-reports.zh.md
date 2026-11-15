<!-- source-sha256: 414b1f2ecf94ee662d676bfee378da5f681026d8350569bd139530ea1a052a31 -->
# Sanitizer 报告

本页列出所有保留的复现：在这些复现中，sanitizer 报告真实 C 有未定义行为或内存错误。共有十一个目录。五个展示调用者的错误，安全定理用一条具名前提把它们排除在外；一个展示一个需要未文档化函数的调用序列；五个展示 zlib 本身的缺陷，被验证的源码为它们打了补丁。每个目录里有运行脚本、C 驱动程序，以及 `report.txt` 中的原始 sanitizer 输出。

## 怎样读每一节

每一节给出 C 写成的调用序列、从 `report.txt` 抄来的 sanitizer 判定行，以及下面两者之一：

- 对调用者的错误，给出**排除它的前提**：该布局违反的那条安全目标假设，并链接到[偏离记录](deviations.md)中对应的行；
- 对 zlib 的缺陷，给出它在[发现](findings.md)中的页面链接，以及修复它的补丁。

这里说的安全目标是 `ZlibF/Spec/Safety/` 中的目标：每个函数一个目标，例如 `Goal.inflate_safety` 和 `Goal.deflate_safety`；每种调用序列一个目标，例如 `Goal.inflate_sequence_safety`、`Goal.deflate_sequence_safety` 和 `Goal.gz_sequence_safety`。某个函数目标的前提，也是序列目标中同一调用的前提。这些目标都已登记；验收状态见[进度](progress.md#scope)。

各报告的平台和源码：

| 报告 | 主机 | 所构建的源码 |
| --- | --- | --- |
| 除 `gzprintf-error-string` 之外的四个调用者错误目录 | x86_64 Linux；arm64 macOS 上判定相同，唯一的差异记在 `prime.c` 下 | 固定的源码加补丁 0001。行号是固定的源码的行号：补丁 0001 只改动 `inflate.c` 第 1383 行附近。 |
| `gzprintf-error-string` | 只有 arm64 macOS（Apple clang） | 固定的源码加补丁 0001 至 0005。行号是这份打过补丁的源码的行号，与固定的源码不同。 |
| `deflate-copy-pending-prev` | x86_64 Linux（GCC 14）；arm64 macOS 上有同样的 AddressSanitizer 报告 | 固定的源码；没有补丁涉及 deflate 的文件。 |
| `inflate-copy-fixed`、`gzseek-pushback-overflow`、`gzread-transparent-stale-next` | x86_64 Linux（GCC 15.2）；arm64 macOS（Apple clang 21）上判定相同 | 不打任何补丁的固定的源码。行号是固定的源码的行号。 |
| `gzread-pos-overflow`、`gzwrite-pos-overflow` | x86_64 Linux（内核 7.0，GCC 15.2）。写入一侧的报告在 arm64 macOS 上也能复现；读取一侧的报告在那里运行了一次，没有复现（观察到的情况见[它的页面](findings/gzread-pos-overflow/README.md)）。 | 固定的源码加除 0004 以外的补丁，即各自的 `run.sh` 构建的源码。保留下来的那次用真实 `/dev/null` 的 `gzwrite-pos-overflow` 运行，用的是补丁 0001 至 0003。`gzread.c` 的行号比固定的源码大一；`gzwrite.c` 的行号与固定的源码相同。 |

一份 sanitizer 报告是关于真实 C 的一次运行的证据。它不是证明。

## 已证明定义域之外的调用者错误

调用 zlib 的程序必须有意构造这些布局和调用顺序：把头部缓冲区指向自己的输入或输出，在 zlib 使用头部记录时修改它，在 zlib.h 允许的时间点之后调用函数，为长度单元传入 `NULL`，或者把 `gzerror` 返回的字符串传给同一句柄上的 `gzprintf`。它们不是攻击者能控制的输入。任何压缩字节流都触发不了其中任何一种。

这些都没有报告给上游，也都不记为 zlib 缺陷。`gzprintf` 的情形记为文档缺口。

### `inflate-gzip-extra`：`inflate` 期间的 gzip extra 缓冲区

[目录](../tests/regression/inflate-gzip-extra/README.md)，[报告](../tests/regression/inflate-gzip-extra/report.txt)。zlib.h 对这两种布局都没有说明。

`overlap.c`：extra 缓冲区与存放 extra 字段的输入重叠。

```c
inflateInit2(&strm, 31);            /* gzip */
head.extra = in + 14;               /* extra 字段位于 in + 12 .. in + 20 */
head.extra_max = 8;
inflateGetHeader(&strm, &head);
strm.next_in = in;
inflate(&strm, Z_FINISH);           /* inflate.c:626：zmemcpy(head->extra + len, next, ...) */
```

```
==PID==ERROR: AddressSanitizer: memcpy-param-overlap: memory ranges [0x7269582f018e,0x7269582f0196) and [0x7269582f018c, 0x7269582f0194) overlap
    #2 0x64e96ca550f5 in inflate inflate.c:626
```

`shrink.c`：`inflate` 处在 extra 字段内部时，调用者调低 `extra_len`。

```c
head.extra = malloc(0xffffffffu);
head.extra_max = 0xffffffffu;
inflateGetHeader(&strm, &head);
inflate(&strm, Z_NO_FLUSH);         /* 12 个头部字节：停在 4 字节的 extra 字段内 */
head.extra_len = 0;                 /* 调用者修改记录 */
inflate(&strm, Z_NO_FLUSH);         /* inflate.c:626：写到偏移 2^32 - 4 处 */
```

```
==PID==ERROR: AddressSanitizer: heap-buffer-overflow on address 0x7b0f3f1ff7ff at pc 0x7f0f43328d2d bp 0x7ffd603f0d00 sp 0x7ffd603f04a8
WRITE of size 4 at 0x7b0f3f1ff7ff thread T0
    #2 0x64da3988bf46 in inflate inflate.c:626
```

排除它的前提：[偏离记录，“inflate 的 gzip extra 字段”一行](deviations.md#stream-calls-inflate-and-deflate)（`InflateHeaderProgress`）。`inflate` 读取 gzip 头部期间，extra 缓冲区与未读输入分开；在 extra 字段内，`extra_len` 不小于还要读取的字节数。它是 `Goal.inflate_safety` 的前提，也是 `Goal.inflate_sequence_safety` 中每个 `inflate` 调用的前提。

### `deflate-gzip-name-output`：gzip 名称位于 `deflate` 要写的缓冲区里

[目录](../tests/regression/deflate-gzip-name-output/README.md)，[报告](../tests/regression/deflate-gzip-name-output/report.txt)。zlib.h 对这两种布局都没有说明。

`output.c`：名称就是调用者的输出缓冲区。

```c
deflateInit2(&s, 6, Z_DEFLATED, 31, 1, Z_DEFAULT_STRATEGY);   /* gzip，memLevel 1 */
head.name = buf;                    /* 1024 字节，NUL 在下标 505 处 */
deflateSetHeader(&s, &head);
s.next_out = buf;
s.avail_out = 1024;
deflate(&s, Z_NO_FLUSH);            /* deflate.c:1177：刷新覆盖了 NUL */
```

```
==PID==ERROR: AddressSanitizer: heap-buffer-overflow on address 0x793cff3e0480 at pc 0x5dd4f2b5609c bp 0x7ffefba39f50 sp 0x7ffefba39f40
READ of size 1 at 0x793cff3e0480 thread T0
    #0 0x5dd4f2b5609b in deflate deflate.c:1177
```

`pending.c`：名称位于流自己的 `pending_buf` 中（通过内部状态取得）。判定属于同一类，在同一行：

```
==PID==ERROR: AddressSanitizer: heap-buffer-overflow on address 0x6daba5be0500 at pc 0x644e87c872ea bp 0x7ffe6e6b3ff0 sp 0x7ffe6e6b3fe0
READ of size 1 at 0x6daba5be0500 thread T0
    #0 0x644e87c872e9 in deflate deflate.c:1177
```

排除它的前提：[偏离记录，“deflate 的 gzip 头区域”一行](deviations.md#stream-calls-inflate-and-deflate)（`DeflateHeaderApart`）。`deflate` 写出挂接的 gzip 头部期间，输入范围、输出范围、extra 字段、名称和注释两两分开，后三者位于流拥有的存储之外。它是 `Goal.deflate_safety` 的前提，也是 `Goal.deflate_sequence_safety` 中每个 `deflate` 调用的前提。

### `deflate-history-domain`：迟到的调用，以及对头部记录的修改

[目录](../tests/regression/deflate-history-domain/README.md)，[报告](../tests/regression/deflate-history-domain/report.txt)。四种情形。

`prime.c`：`deflate` 已经开始之后调用 `deflatePrime`。zlib.h 排除了它：它写道 `deflatePrime` “`must be used before the first deflate() call`”（必须在第一次 deflate() 调用之前使用，`zlib.h:825`）。

```c
deflateInit2(&z, 1, Z_DEFLATED, -15, 1, Z_DEFAULT_STRATEGY);  /* 裸流，memLevel 1 */
deflate(&z, Z_NO_FLUSH);            /* 300 个输入字节：符号已被记录 */
for (k = 0; k < 200; k++)
    deflatePrime(&z, 16, 0xffff);   /* pending 增长到符号缓冲区上 */
deflate(&z, Z_FINISH);              /* trees.c:930：d_code(dist) */
```

```
trees.c:930:20: runtime error: index 767 out of bounds for type 'uch [512]'
trees.c:930:20: runtime error: load of address 0x614810c3571f with insufficient space for an object of type 'const uch'
```

在 arm64 macOS 上第一行相同；UndefinedBehaviorSanitizer 接下来报告的是 `trees.c:937` 处的有符号左移溢出，而不是上面的第二行，因为越界读到的字节不同。

`header.c 1`：`deflate` 已经开始之后调用 `deflateSetHeader(strm, NULL)`。zlib.h 排除了它：`deflateSetHeader` 可以在初始化或重置之后调用，并且要 “`before the first call of deflate()`”（在第一次调用 deflate() 之前，`zlib.h:840`）。

```c
deflateInit2(&z, 6, Z_DEFLATED, 31, 1, Z_DEFAULT_STRATEGY);   /* gzip，memLevel 1 */
g.extra = extra;                    /* 2000 字节 */
g.extra_len = 2000;
deflateSetHeader(&z, &g);
z.avail_out = 10;
deflate(&z, Z_NO_FLUSH);            /* 停在 extra 字段内，已写出 500 字节 */
deflateSetHeader(&z, Z_NULL);
deflate(&z, Z_FINISH);              /* deflate.c:1137：s->gzhead->extra */
```

```
deflate.c:1137:22: runtime error: member access within null pointer of type 'struct gz_header'
==PID==ERROR: AddressSanitizer: SEGV on unknown address 0x000000000018 (pc 0x62e83b3ddde4 bp 0x7ffe5b49aca0 sp 0x7ffe5b49aa40 T0)
```

排除这两种情形的前提：[偏离记录，“其他流参数”一行](deviations.md#stream-calls-inflate-and-deflate)（`DeflateNotStarted`）。`deflatePrime` 和 `deflateSetHeader` 只在第一次 `deflate` 调用启动流之前调用。它是 `Goal.deflatePrime_safety` 和 `Goal.deflateSetHeader_safety` 的前提，也是 `Goal.deflate_sequence_safety` 中同样调用的前提。

`header.c 2`：开头相同；随后调用者缩短 extra 字段。对头部写出期间的修改，zlib.h 没有说明。

```c
g.extra_len = 10;                   /* 小于已写出的 500 字节 */
deflate(&z, Z_FINISH);              /* deflate.c:1142：从 extra 缓冲区 zmemcpy */
```

```
==PID==ERROR: AddressSanitizer: heap-buffer-overflow on address 0x7c21e51e0850 at pc 0x7e51e6f2901f bp 0x7ffed5b3e4c0 sp 0x7ffed5b3dc68
READ of size 512 at 0x7c21e51e0850 thread T0
    #2 0x57575de3d176 in deflate deflate.c:1142
```

`clear.c`：1500 字节的 extra 字段和 3 字节的名称；调用者在中途把 `extra` 清为 `NULL`。

```c
head.extra = extra;
head.extra_len = 1500;
head.name = (Bytef *)name;          /* "abc" */
deflateSetHeader(&s, &head);
s.avail_out = 100;
deflate(&s, Z_FINISH);              /* 停在 extra 字段内 */
head.extra = Z_NULL;                /* 调用者修改记录 */
deflate(&s, Z_FINISH);              /* deflate.c:1177：读取 name[gzindex]，越过了名称 */
```

```
==PID==ERROR: AddressSanitizer: heap-buffer-overflow on address 0x722a2ebe0204 at pc 0x64bb6cd58142 bp 0x7fff28a19670 sp 0x7fff28a19660
READ of size 1 at 0x722a2ebe0204 thread T0
    #0 0x64bb6cd58141 in deflate deflate.c:1177
0x722a2ebe0204 is located 496 bytes after 4-byte region [0x722a2ebe0010,0x722a2ebe0014)
```

排除这两种情形的前提：[偏离记录，“deflate 的 gzip 头进度”一行](deviations.md#stream-calls-inflate-and-deflate)（`DeflateHeaderProgress`）。在每个写出挂接的 gzip 头部的 `deflate` 调用处，字段仍然覆盖已写出的部分，并且字段没有在中途被设为 `NULL`。它是 `Goal.deflate_safety` 的前提，也是 `Goal.deflate_sequence_safety` 中每个 `deflate` 调用的前提。

### `compress-allocation`：`NULL` 长度单元

[目录](../tests/regression/compress-allocation/README.md)，`ubwitness.c`，[报告](../tests/regression/compress-allocation/report.txt)。zlib.h 把 `destLen` 描述为进入时目的缓冲区的大小；它没有提到 `NULL`。`report.txt` 只含 `run.sh` 的这个见证步骤；该运行脚本的其余部分是与 Lean 翻译的比较，没有 sanitizer 报告。

```c
compress2(dst, NULL, src, 1, 6);    /* compress.c:70：z_size_t got = *destLen; */
compress(dst, NULL, src, 1);        /* 同一条语句 */
```

```
compress.c:70:20: runtime error: load of null pointer of type 'uLongf'
```

排除它的前提：[偏离记录，“整缓冲区压缩”一行](deviations.md#whole-buffer-utilities-and-checksums)（`CompressArguments`；`CompressorSafety` 中的子句 `capacity ≠ none`）。`compress` 和 `compress2` 的长度单元不是 `NULL`。它是 `Goal.compress_safety` 和 `Goal.compress2_safety` 的前提。`_z` 形式会检查这个单元是否为 `NULL`，它们的目标允许 `NULL`。

### `gzprintf-error-string`：把句柄自己的错误字符串当作 `%s` 参数

[目录](../tests/regression/gzprintf-error-string/README.md)，`errstr.c`，[报告](../tests/regression/gzprintf-error-string/report.txt)。这是文档缺口，不是 zlib 缺陷：zlib.h 说之后的 `gzerror` 调用可能使该字符串失效，文件关闭后该字符串不再可用（`zlib.h:1793`）；它没有提到 `gzprintf`。

```c
/* p[1]：一个已写满的非阻塞管道的写端 */
gzFile f = gzdopen(p[1], "wT");
gzwrite(f, big, 100000);            /* 以 EAGAIN 停顿：err = Z_ERRNO，分配了一条消息 */
const char *m = gzerror(f, &e);     /* 句柄自己的消息 */
gzprintf(f, "%s", m);               /* gzvprintf 先释放这条消息，然后 vsnprintf 读取它 */
```

```
==PID==ERROR: AddressSanitizer: heap-use-after-free on address 0x604000000390 at pc 0x000102dc6ed0 bp 0x00016d8715f0 sp 0x00016d870d80
READ of size 2 at 0x604000000390 thread T0
    #2 0x0001025a9e50 in gzvprintf gzwrite.c:491
freed by thread T0 here:
    #1 0x0001025a7fc8 in gz_error gzlib.c:568
    #2 0x0001025a9b1c in gzvprintf gzwrite.c:448
```

在不打补丁的固定的源码中，这三条语句分别位于 `gzwrite.c:485`（`vsnprintf` 调用）、`gzlib.c:563`（`free`）和 `gzwrite.c:442`（`gz_error` 调用）。

排除它的前提：[偏离记录，“Gz printf 字符串”一行](deviations.md#gzip-file-interface)（`GzArguments`）。`gzprintf` 和 `gzvprintf` 的格式串以及每个 `%s` 参数都位于句柄拥有的块之外。它是 `Goal.gz_sequence_safety` 中每个 `gzprintf` 和 `gzvprintf` 调用的前提。

## 需要未文档化函数的调用序列

### `deflate-copy-pending-prev`：`deflateResetKeep` 之后的 `deflateCopy`

[目录](../tests/regression/deflate-copy-pending-prev/README.md)，`copy.c`，[报告](../tests/regression/deflate-copy-pending-prev/report.txt)。这不是调用者布局：每个缓冲区都有效且互不重叠，每个调用都是对导出函数的调用。这个序列用到 `deflateResetKeep`，zlib.h 把它声明在 “`undocumented functions (not part of the zlib API)`”（未文档化的函数，不属于 zlib API）之下。完整说明见[发现](findings/deflate-copy-pending-prev/README.md)；有一份[报告草稿](findings/deflate-copy-pending-prev-report.md)，没有寄出。

```c
deflateInit2(&a, 6, Z_DEFLATED, 9, 8, Z_DEFAULT_STRATEGY);
deflate(&a, Z_NO_FLUSH);
deflateResetKeep(&a);
deflate(&a, Z_BLOCK);
deflateCopy(&c, &a);
deflateParams(&c, 6, Z_RLE);
deflate(&c, Z_SYNC_FLUSH);          /* 无输入 */
deflateParams(&c, 6, Z_DEFAULT_STRATEGY);
deflate(&c, Z_FINISH);              /* 输入以 strstart - 2 处的字节开头 */
```

```
==PID==ERROR: AddressSanitizer: heap-buffer-overflow on address 0x519000000e89 at pc 0x0000004033f1 bp 0x7ffe4828dba0 sp 0x7ffe4828db98
READ of size 1 at 0x519000000e89 thread T0
    #0 0x4033f0 in longest_match deflate.c:1511
```

使用默认分配器时，valgrind 在 `deflate.c:1555` 报告依赖未初始化值的条件跳转，该值来自 `deflateCopy` 对 `prev` 的分配。

排除它的前提：[偏离记录，“直接调用 `deflateResetKeep`”一行](deviations.md#stream-calls-inflate-and-deflate)。deflate 的调用历史中没有直接的 `deflateResetKeep` 调用。这限定了 `Goal.deflate_safety`、`Goal.deflateCopy_safety` 以及其他 deflate 目标所谈论的流，也限定了 `Goal.deflate_sequence_safety` 的历史。

## 库缺陷

这五个是 zlib 在文档用法之内的缺陷。每个在[发现](findings.md)之下都有一页，给出调用序列、运行命令、判定、严重程度和修复。运行脚本有意构建不带修复的源码；gz 的运行脚本还会构建带修复的源码，并检查报告已经消失。

| 目录 | 判定 | 发现 | 被验证的源码中的修复 |
| --- | --- | --- | --- |
| [inflate-copy-fixed](findings/inflate-copy-fixed/README.md)（[报告](findings/inflate-copy-fixed/report.txt)） | AddressSanitizer `invalid-pointer-pair`，`inflate.c:1383`，在静态的 `lenfix` 与 inflate 状态之间 | [`inflateCopy` 比较无关的指针](findings/inflate-copy-fixed/README.md) | 补丁 0001，上游拉取请求 #1369 |
| [gzseek-pushback-overflow](../tests/regression/gzseek-pushback-overflow/README.md)（[报告](../tests/regression/gzseek-pushback-overflow/report.txt)） | UndefinedBehaviorSanitizer：有符号整数溢出，`gzlib.c:395`、`403`、`424` | [开头的 `gzungetc` 之后调用 `gzseek`](findings/gzseek-pushback-overflow/README.md) | 补丁 0002，上游拉取请求 #1361 |
| [gzread-transparent-stale-next](../tests/regression/gzread-transparent-stale-next/README.md)（[报告](../tests/regression/gzread-transparent-stale-next/report.txt)） | AddressSanitizer `heap-buffer-overflow`，1 字节读，`gzread.c:369`，位于 32 字节输出缓冲区之后 0 字节处 | [`gzread` 从过时的 `x.next` 复制](findings/gzread-transparent-stale-next/README.md) | 补丁 0003，上游拉取请求 #1363 |
| [gzread-pos-overflow](../tests/regression/gzread-pos-overflow/README.md)（[报告](../tests/regression/gzread-pos-overflow/report.txt)） | UndefinedBehaviorSanitizer：有符号整数溢出，位于 `gz_read`（`x.pos += n`）、`gzgetc()` 宏和 `gzgetc` 函数 | [gz 位置溢出，读取](findings/gzread-pos-overflow/README.md) | 补丁 0004，本地 |
| [gzwrite-pos-overflow](../tests/regression/gzwrite-pos-overflow/README.md)（[报告](../tests/regression/gzwrite-pos-overflow/report.txt)） | UndefinedBehaviorSanitizer：有符号整数溢出，`gzwrite.c:230`（`gz_write`）和 `gzwrite.c:352`（`gzputc`） | [gz 位置溢出，写入](findings/gzwrite-pos-overflow/README.md) | 补丁 0004，本地 |

每个修复的上游状态见[补丁](../patches/README.md)。

## 没有报告的运行，作为某种布局有定义的证据保留

这些运行使用同样的 sanitizer，没有任何报告。它们表明某种布局是有定义的 C，所以证明覆盖它。

- [inflate-shared-block](../tests/regression/inflate-shared-block/README.md)：输入范围和输出范围位于同一个堆块中，两种先后顺序都有。这在前提 `StreamBuffers` 之内：它要求两个范围分开，不要求它们位于不同的块。
- [inflate-gzip-flags-prime](../tests/regression/inflate-gzip-flags-prime/README.md)：对处于 `FLAGS` 的 gzip 流调用 `inflatePrime`，使标志字变为 65544。这是有定义的，尽管 zlib.h 说 `inflatePrime` “`should be used with raw inflate`”（应当用于裸 inflate，`zlib.h:1021`）。

## 未列入

- [deflate-slide](../tests/regression/deflate-slide/README.md)：UndefinedBehaviorSanitizer 在一个人为构造的内部状态中报告有符号溢出，目前没有任何调用序列被证实能到达这个状态。它测试的是翻译中的溢出故障，不是调用者布局。
- sanitizer 构建保持无报告的差分回归测试：`inflate-copy`、`inflate-deferred-distance`、`inflate-prime`、`trees-depth-read`、`crc-byte-views`。
- [deflate-resetkeep-stale-hash](findings/deflate-resetkeep-stale-hash/README.md) 中的数据错误，没有 sanitizer 报告它。
- 本地补丁 0005 去掉的对 `x.next` 的加零（[未写入](findings/gz-reset-next-uninitialised/README.md)、[悬空](findings/gz-next-dangling-after-direct-read/README.md)）：按 C 标准的字面规定未定义，用探针展示；没有 sanitizer 报告它。
- 透明探测之后的位置溢出，是补丁 0004 第一版的缺口（[发现](findings/gz-position-copy-overflow.md)）：已在模型中确认，也已通过对 C 的解读确认，没有在 sanitizer 下复现。
- [inflate-configured-window](../tests/regression/inflate-configured-window/README.md)：在一个输入上对 C 的原生运行，不带 sanitizer，没有报告。

## 添加复现

新的 sanitizer 复现放在 `tests/regression/<name>/` 下，带 `run.sh`、`report.txt`，并在本页加一节。`report.txt` 保存原始输出，其中进程号已替换，路径改为相对于仓库或 zlib 根目录。

<!-- source-sha256: 2b2ef4b09ee9bbad1bd71693e3abdc1413364d658f920d2cd265609a2a3ef0f3 -->
# `gzread`：在设备上定位之后位置发生有符号溢出

gz 读取函数把交付的字节数加到有符号的位置 `state->x.pos` 上，没有上界。在 Linux 上，对 `/dev/zero` 这样的字符设备做透明模式的 `gzseek`，可以把位置设为 `INT64_MAX`，下一次读取就让它溢出。zlib 的维护者只读本页，就能复现这份报告并作出判断。写入一侧的对应问题是 [gzwrite-pos-overflow](../gzwrite-pos-overflow/README.md)。测试文件在 [`tests/regression/gzread-pos-overflow`](../../../tests/regression/gzread-pos-overflow/README.md)。

## 状态

- 未定义行为：`x.pos` 的有符号整数溢出，出现在 `gz_read`、`gzgetc` 函数，以及在调用者代码中展开的 zlib.h 的 `gzgetc()` 宏里。在文档用法之内。
- 由 UndefinedBehaviorSanitizer 在 x86_64 Linux（内核 7.0，GCC 15.2）上报告；源码是固定的 `757f0527154291bcf6bfbd6396ecde6bedd2db95` 加上本仓库除 0004 以外的补丁。在 arm64 macOS 上用 Apple clang 运行了一次，没有复现：那里对 `/dev/zero` 的 `lseek` 接受这个偏移并把它返回，读取没有交付位置 `INT64_MAX` 之后的任何字节，sanitizer 也没有任何报告。没有试过别的系统。
- 没有提交上游。被验证的源码应用本地[补丁 0004](../../../patches/README.md)，项目所有者于 2026-11-12 批准。拉取请求的文字草稿在 [upstream-description.md](upstream-description.md)。

## 调用序列

```c
int fd = open("/dev/zero", O_RDONLY);
gzFile f = gzdopen(fd, "r");
gzread(f, buf, 1);                       /* 不是 gzip：透明模式（how == COPY） */
gzseek(f, INT64_MAX, SEEK_SET);          /* 设备上的 lseek 返回 0：x.pos = INT64_MAX */
gzread(f, buf, 16);                      /* gz_read：state->x.pos += n 溢出 */
```

第二个序列在调用者的代码里溢出：

```c
gzseek(f, INT64_MAX - 4, SEEK_SET);
gzread(f, buf, 1);                       /* gz_fetch 填满整个输出缓冲区 */
gzgetc(f); gzgetc(f); gzgetc(f);         /* 宏：x.pos 到达 INT64_MAX */
gzgetc(f);                               /* 宏中的 (g)->pos++ 溢出 */
```

定位为什么被接受：`gzseek64` 只检查目标能否用 `z_off64_t` 表示。在透明模式下，它随后对描述符调用 `lseek`。在 Linux 上，对 `/dev/zero` 的 `lseek` 返回 0、不失败，而设备继续提供字节：保留的报告显示了偏移为 `INT64_MAX - 1` 的这次调用。没有在别的设备上运行过。

完整程序是 [`devzero.c`](../../../tests/regression/gzread-pos-overflow/devzero.c)。

## 运行

在 Linux 上，仓库根目录，`zlib/` 子模块已检出：

```sh
ZLIB_SRC=$PWD/zlib bash tests/regression/gzread-pos-overflow/run.sh
```

脚本用 `-fsanitize=address,undefined -fno-sanitize-recover=undefined -g -O1` 把固定的源码构建两次：一次用除 0004 以外的 `patches/*.patch`，一次用全部补丁。它在每个构建上以三种模式运行 `devzero.c`。没有 0004 时，每次运行都必须报告位置的有符号溢出。有 0004 时不得有任何报告，并且读取必须以 `Z_DATA_ERROR`“position overflow”结束。六项检查全部成立时脚本以状态 0 退出；每项通过的检查打印一行以 `ok:` 开头的文字。在其他系统上，脚本打印 `skip: needs Linux (/dev/zero with a succeeding lseek)`，什么也不检查。

## Sanitizer 判定

摘自 [`report.txt`](../../../tests/regression/gzread-pos-overflow/report.txt)，x86_64 Linux，不含补丁 0004 的源码：

```
gzread.c:414:22: runtime error: signed integer overflow: 9223372036854775807 + 16 cannot be represented in type 'long int'
devzero.c:73:17: runtime error: signed integer overflow: 9223372036854775807 + 1 cannot be represented in type 'long int'
gzread.c:539:21: runtime error: signed integer overflow: 9223372036854775807 + 1 cannot be represented in type 'long int'
```

第一行是 `gz_read` 中的 `state->x.pos += n`，在未打补丁的固定的文件中是第 413 行。第二行是在 `devzero.c` 中展开的 `gzgetc()` 宏。第三行是 `gzgetc` 函数。撰写本页时没有重新运行这份报告：它需要 Linux。

本项目的故障注入测试框架在模拟设备式 `lseek` 时，2 000 个历史中有一个得到同样的报告。那次运行没有保留在这里。

## 范围与严重程度

- **谁会遇到。** 透明模式的读取者，其描述符的 `lseek` 成功却不限制偏移，随后还提供数据。Linux 上的 `/dev/zero` 就是这样的描述符，也是唯一运行过的一个。程序必须定位到 `INT64_MAX` 附近。对 gzip 流，同样的溢出需要大约 2^63 字节的解压输出，不现实。
- **后果。** 有符号计数器上的未定义行为。按通常的回绕，`gztell` 变为负数，之后的定位从错误的位置计算。
- **内存安全。** 没有发现这个溢出会引起内存错误。这是对未打补丁的 C 的解读，**尚未由证明确认**。本项目的证明也不会确认它：已登记的 gz 安全定理（`gz_sequence_safety_public`，它证明 `Goal.gz_sequence_safety`）针对的是带补丁 0004 的源码，在那里溢出不会发生。
- **严重程度。** 低：它需要在设备上有接近 2^63 的位置。

## `zlib.h` 的说法

每个调用都是文档用法：zlib.h 允许对任何描述符使用 `gzdopen`，允许定位到偏移类型能表示的任何位置，也允许之后读取。关于这一界限，它只说，如果结果位置 “`would not be representable in the offset type`”（不能用偏移类型表示），`gzseek` 返回 -1（`zlib.h:1687`）。对于把位置推过这一界限的读取，以及对于设备，它没有说明。

## 修复

[0004-gz-position-overflow.patch](../../../patches/0004-gz-position-overflow.patch) 的读取部分：辅助函数 `gz_room(state, max)` 返回 `max`，如果再交付 `max` 个字节会使 `x.pos` 超过 `GZ_OFF_MAX`，则返回更少。`gz_fetch` 最多向输出缓冲区填入这么多字节（至少一个，以便仍能发现输入结束），从而 `x.pos + x.have` 永不超过 `GZ_OFF_MAX`，`gzgetc()` 宏保持有定义。`gz_read` 和 `gzgets` 最多交付这么多字节；如果还剩无法交付的数据，就丢弃它并设置 `Z_DATA_ERROR`“position overflow”。在 `GZ_OFF_MAX - 2 * size` 以下没有任何变化。接近界限时交付相同的字节，只是每次填充更少。到达界限时，输入结束仍像以前一样报告；只有原本会使位置溢出的数据变成错误。

补丁保持的不变量是：每次调用返回时 `x.pos + x.have <= GZ_OFF_MAX`。`x.have` 的每个产生者都保持它：

- `gz_fetch` 最多加载 `GZ_OFF_MAX - x.pos` 个字节；
- `gz_look` 在透明模式下最多缓冲 `gz_room(state, avail_in)` 个字节，输入超出时记录同样的错误。补丁的第一版没有这个界限：见 [gz-position-copy-overflow](../gz-position-copy-overflow.md)；
- `gz_read` 的直接路径最多交付这么多字节；
- `gzungetc` 加入一个字节时把 `x.pos` 减一；
- 透明模式下的定位清空缓冲区。

`gz_fetch` 在 `GZ_OFF_MAX` 处为发现输入结束而加载的那一个字节，由它在那里仅有的调用者 `gz_read` 和 `gzgets` 在返回前丢弃（`gz_skip` 从不在 `GZ_OFF_MAX` 处取数据，因为 `x.pos + skip` 至多为 `GZ_OFF_MAX`）。因此逐字节取缓冲数据的快速路径（`gzgetc` 函数、`gzgetc()` 宏）以及 `gz_skip_have` 都无需检查。复现的 `fast` 运行在 `INT64_MAX - 2` 处检验了这些路径。

补丁的检查：[upstream-description.md](upstream-description.md) 的“测试”一节。

## 与证明的关系

[gz 证明说明](../../proof/gzip.md)把这份报告称为 F-1。证明针对的是打过补丁的源码。

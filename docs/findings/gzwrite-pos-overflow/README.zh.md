<!-- source-sha256: c9470ac3b72eb040d1ed86bdb8d82d6b2fbbdf97694ad3adcce31645e5506a32 -->
# `gzwrite`：向前定位之后位置发生有符号溢出

gz 写入函数把它们接受的字节数加到有符号位置 `state->x.pos` 上，没有上界。透明写入者向前定位到 `INT64_MAX` 附近之后，一旦接收端接受了定位所需的那些零，下一次写入就使位置溢出：在 `gz_write` 中，以及在 `gzputc` 的快速路径中。有符号溢出是未定义行为。读取一侧见 [gzread-pos-overflow](../gzread-pos-overflow/README.md)。

## 到达它的调用

```c
int fd = open("/dev/null", O_WRONLY);
gzFile f = gzdopen(fd, "wT");            /* 透明写入者 */
gzbuffer(f, 1 << 29);
gzseek(f, INT64_MAX - 10, SEEK_SET);     /* 被接受：记为待执行的跳过 */
gzwrite(f, buf, 100);                    /* gz_zero 写出 INT64_MAX - 10 个零，然后
                                            gzwrite.c:230：state->x.pos += copy 溢出 */
```

第二个序列：

```c
gzseek(f, INT64_MAX, SEEK_SET);
gzputc(f, 'a');                          /* gzwrite.c:352：state->x.pos++ 溢出 */
```

`gzseek64` 只检查目标能否用 `z_off64_t` 表示。写入者的向前定位被记为待执行的跳过，下一次写入先写出这么多个零（`gz_zero`），这把 `x.pos` 移到目标。之后 `gz_write`（`x.pos += copy` 和 `x.pos += n`）、`gzputc` 的快速路径（`x.pos++`）和 `gzprintf`（`x.pos += len`）继续往上加，没有上界。填零是 2^34 次、每次 2^29 字节的写入；`/dev/null` 全部接受。

透明写入者在能接受无限输出的接收端上到达溢出：`/dev/null`，或者通向一个丢弃数据的消费者的管道。对普通文件，写入早在此之前就失败了（`EFBIG`）。压缩的写入者必须先压缩这些零，大约是 2^63 字节的工作量。

每个调用都是文档用法。关于这个上限，`zlib.h` 只说如果结果位置 `would not be representable in the offset type`（无法用偏移类型表示，`zlib.h:1687`），`gzseek` 返回 -1。

完整程序是 [`wpos.c`](../../../tests/regression/gzwrite-pos-overflow/wpos.c)。

## 证据

对带有除 0004 以外全部补丁的 C，UndefinedBehaviorSanitizer 报告这次溢出。在仓库根目录、已检出 `zlib/` 子模块时运行：

```sh
ZLIB_SRC=$PWD/zlib bash tests/regression/gzwrite-pos-overflow/run.sh
```

脚本用 `-fsanitize=undefined -fno-sanitize-recover=undefined -g -O2` 把 zlib 源码构建两次：一次带 `patches/*.patch` 中除 0004 以外的补丁，一次带全部补丁。它在每个构建上运行两个序列。不带 0004 时，每次运行都必须报告位置的有符号溢出。带 0004 时不得有任何报告，并且写入必须以 `Z_DATA_ERROR`（消息为 `position overflow`）失败。四项检查全部成立时脚本以状态 0 退出，最后一行是：

```
ok: with the fix: Z_DATA_ERROR position overflow, no report
```

默认情况下程序与 `fastwrite.c` 链接，它提供的 `write()` 对 `/dev/null` 的描述符接受每个字节而不做系统调用：每次运行大约一分钟。在命令前加 `FULL=1` 则使用真实的 `/dev/null`：在 x86_64 Linux 上每次运行大约 17 分钟。

摘自 [`report.txt`](../../../tests/regression/gzwrite-pos-overflow/report.txt)，x86_64 Linux，不带补丁 0004 的源码，默认模式：

```
gzwrite.c:230:26: runtime error: signed integer overflow: 9223372036854775797 + 100 cannot be represented in type 'long int'
gzwrite.c:352:25: runtime error: signed integer overflow: 9223372036854775807 + 1 cannot be represented in type 'long int'
```

同一文件中还有一次用真实 `/dev/null` 运行得到的第一行。arm64 macOS 在默认模式下于相同的行给出这两条报告。

## 影响

有符号计数器上的未定义行为。按通常的回绕，`gztell` 变为负数。

## 修复

[补丁 0004](../../../patches/README.md)，写入一侧：当 `GZ_OFF_MAX - x.pos < len` 时，`gz_write` 拒绝写入 `len` 个字节；`gzputc` 在 `GZ_OFF_MAX` 处离开快速路径（随后 `gz_write` 拒绝）；`gzprintf` 拒绝会越过上限的格式化输出。它们都设置 `Z_DATA_ERROR`（消息为 `position overflow`）。不越过上限的写入不变。越过上限的写入被整体拒绝，所以一次越界的写入即使本来会在到达上限之前被 I/O 错误或停顿打断，报告的也是 `position overflow`，而不是那个 I/O 错误。

上游：该补丁是本地补丁，没有提交。

## 与证明的关系

[gzip 证明](../../proof/gzip.md)针对的是打过补丁的源码。

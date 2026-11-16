<!-- source-sha256: 341003bf6a91170720788c9c9c7e7230f86831577001a9f63967739a5586ba89 -->
# `gzwrite`：向前定位之后位置发生有符号溢出

gz 写入函数把接受的字节数加到有符号的位置 `state->x.pos` 上，没有上界。透明模式的写入者向前定位到 `INT64_MAX` 附近之后，一旦接收端收下了定位所需的那些零，下一次写入就让位置溢出。zlib 的维护者只读本页，就能复现这份报告并作出判断。读取一侧的对应问题是 [gzread-pos-overflow](../gzread-pos-overflow/README.md)。测试文件在 [`tests/regression/gzwrite-pos-overflow`](../../../tests/regression/gzwrite-pos-overflow/README.md)。

## 状态

- 未定义行为：`x.pos` 的有符号整数溢出，出现在 `gz_write` 和 `gzputc` 的快速路径里。在文档用法之内。
- 由 UndefinedBehaviorSanitizer 在 x86_64 Linux（内核 7.0，GCC 15.2）上用真实的 `/dev/null` 报告；用一种更快的模式，在 Linux 和 arm64 macOS 上也报告。较快的模式运行在上游 `develop` 的提交 `757f0527154291bcf6bfbd6396ecde6bedd2db95` 加上本仓库除 0004 以外的补丁之上，即 `run.sh` 构建的源码。保留下来的那次使用真实 `/dev/null` 的运行，用的是程序较早的一份副本，源码是同一提交加补丁 0001 至 0003。
- 没有提交上游。被验证的源码应用本地[补丁 0004](../../../patches/README.md)。覆盖读写两侧的拉取请求文字草稿在 [../gzread-pos-overflow/upstream-description.md](../gzread-pos-overflow/upstream-description.md)。

## 调用序列

```c
int fd = open("/dev/null", O_WRONLY);
gzFile f = gzdopen(fd, "wT");            /* 透明模式的写入者 */
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

`gzseek64` 只检查目标能否用 `z_off64_t` 表示。写入者的向前定位被记为待执行的跳过，下一次写入先写出那么多个零（`gz_zero`），把 `x.pos` 移到目标处。随后 `gz_write`（`x.pos += copy` 和 `x.pos += n`）、`gzputc` 的快速路径（`x.pos++`）以及 `gzprintf`（`x.pos += len`）继续往上加，没有上界。填零是 2^34 次、每次 2^29 字节的写入；`/dev/null` 全部接受。

完整程序是 [`wpos.c`](../../../tests/regression/gzwrite-pos-overflow/wpos.c)。

## 运行

在仓库根目录，`zlib/` 子模块已检出：

```sh
ZLIB_SRC=$PWD/zlib bash tests/regression/gzwrite-pos-overflow/run.sh
```

脚本用 `-fsanitize=undefined -fno-sanitize-recover=undefined -g -O2` 把 zlib 源码构建两次：一次用除 0004 以外的 `patches/*.patch`，一次用全部补丁。它在每个构建上运行这两个序列。没有 0004 时，每次运行都必须报告位置的有符号溢出。有 0004 时不得有任何报告，并且写入必须以 `Z_DATA_ERROR`“position overflow”失败。四项检查全部成立时脚本以状态 0 退出，最后一行是：

```
ok: with the fix: Z_DATA_ERROR position overflow, no report
```

默认情况下，程序与 `fastwrite.c` 链接；它提供一个 `write()`，对 `/dev/null` 的描述符不做系统调用就接受每个字节：每次运行约一分钟。在命令前加 `FULL=1` 则使用真实的 `/dev/null`：在 x86_64 Linux 上每次运行约 17 分钟。两种模式都只用 UndefinedBehaviorSanitizer 构建；在 AddressSanitizer 下，2^34 次被拦截的写入要花几个小时。

## Sanitizer 判定

摘自 [`report.txt`](../../../tests/regression/gzwrite-pos-overflow/report.txt)，x86_64 Linux，不含补丁 0004 的源码，默认模式：

```
gzwrite.c:230:26: runtime error: signed integer overflow: 9223372036854775797 + 100 cannot be represented in type 'long int'
gzwrite.c:352:25: runtime error: signed integer overflow: 9223372036854775807 + 1 cannot be represented in type 'long int'
```

同一文件里还有一次使用真实 `/dev/null` 的运行给出的第一行，那次运行用了 17 分钟（程序较早的一份副本，源码带补丁 0001 至 0003）。在 arm64 macOS 上以默认模式运行了一次，在相同的行得到这两份报告，类型打印为 `off_t`。

## 范围与严重程度

- **谁会遇到。** 透明模式的写入者，写往能接受无限输出的接收端：`/dev/null`，或者通向一个丢弃数据的消费者的管道。对普通文件，写入早就失败了（`EFBIG`）。对压缩写入者，那些零必须先被压缩，大约 2^63 字节的工作量，不现实。
- **后果。** 有符号计数器上的未定义行为。按通常的回绕，`gztell` 变为负数。
- **严重程度。** 低：溢出需要接收端接受大约 2^63 个字节。

## `zlib.h` 的说法

每个调用都是文档用法。关于这一界限，zlib.h 只说，如果结果位置 “`would not be representable in the offset type`”（不能用偏移类型表示），`gzseek` 返回 -1（`zlib.h:1687`）。对于把位置推过这一界限的写入，它没有说明。

## 修复

[0004-gz-position-overflow.patch](../../../patches/0004-gz-position-overflow.patch) 的写入部分：当 `GZ_OFF_MAX - x.pos < len` 时，`gz_write` 拒绝写入 `len` 个字节；`gzputc` 在 `GZ_OFF_MAX` 处离开其快速路径（随后 `gz_write` 拒绝）；`gzprintf` 拒绝会超过界限的格式化输出。每种情况都设置 `Z_DATA_ERROR`“position overflow”。不超过界限的写入不变。跨越界限的写入被整体拒绝。没有补丁时，这样的写入一旦让位置溢出就是未定义的；只有当 I/O 错误或阻塞在那之前把它停下时它才有定义，而有了补丁，这种情形报告的是“position overflow”，不是那个 I/O 错误。

## 与证明的关系

[gzip 证明](../../proof/gzip.md)针对的是打过补丁的源码。

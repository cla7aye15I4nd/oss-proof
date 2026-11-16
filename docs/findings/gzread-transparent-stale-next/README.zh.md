<!-- source-sha256: 8d5b7ae97b0419450ba19ad5f4c800a9b988ea4850501ca3b81976be5fa85a8c -->
# 部分读取之后出错时，`gzread` 从过时的 `x.next` 复制

在透明模式下（输入不是 gzip），如果 `read()` 返回了一些字节，而下一次 `read()` 失败，`gz_fetch` 会在设置 `state->x.next` 之前返回。读取者随后从旧指针复制这部分字节，而旧指针可能正好在输出缓冲区末尾之后：越界读取堆内存。

## 到达它的调用

```c
gzFile f = gzopen("raw.dat", "rb");     /* 128 字节，不是 gzip：透明模式 */
gzbuffer(f, 16);                         /* 输出缓冲区是 32 字节 */
for (int i = 0; i < 48; i++)
    gzgetc(f);                           /* x.have == 0；x.next == out + 32，缓冲区末尾之后 */
/* 从这里起，对该描述符的 read() 先返回 1 个字节，然后以 EIO 失败 */
gzread(f, buf, 1);                       /* gzread.c:369：memcpy(buf, state->x.next, n) */
```

最后一次调用中，不打补丁的 `gzread.c` 里发生的事：

1. `gz_read` 发现没有已缓冲的输出，调用 `gz_fetch`。
2. 在 `gz_fetch` 的 `case COPY` 中，`gz_load` 存下它拿到的那一个字节，设置 `x.have = 1`，然后返回 -1，因为下一次 `read()` 以 `EAGAIN` 以外的错误失败。
3. `gz_fetch` 立即返回 -1。`gz_load` 调用之后的赋值 `state->x.next = state->out` 被跳过。
4. `gz_read` 看到 `x.have != 0`，从 `x.next` 复制一个字节，而 `x.next` 仍然是 `out + 32`。

透明读取者在这种情况下到达它：描述符只交付了请求的一部分，然后以 `EAGAIN` 以外的错误失败，例如出故障的磁盘、网络文件系统、被重置的套接字或管道。压缩数据的路径（`case GZIP`）不受影响。

`zlib.h` 把这种情况描述为已处理：`If some data was read before an error, then that data is returned until exhausted`（如果出错之前已读到一些数据，这些数据会被返回，直到用完，`zlib.h:1492`）。不打补丁的代码返回的字节数是对的，字节本身是错的。

完整程序是 [`stale.c`](../../../tests/regression/gzread-transparent-stale-next/stale.c)。它定义了自己的 `read()`，静态链接的库会调用它，以此让第二次 `read()` 失败。

## 证据

在不打补丁的 C 上，AddressSanitizer 报告这次读取。在仓库根目录、已检出 `zlib/` 子模块时运行：

```sh
ZLIB_SRC=$PWD/zlib bash tests/regression/gzread-transparent-stale-next/run.sh
```

脚本用 `-fsanitize=address,undefined -fno-sanitize-recover=undefined -fno-omit-frame-pointer -g -O1` 把 zlib 源码构建两次：一次不带任何补丁，一次带 `patches/*.patch`。不打补丁的构建必须报告这次读取。打补丁的构建必须没有任何报告，并且 `gzread` 必须返回 1 且保留错误 `Z_ERRNO`。两者都成立时脚本以状态 0 退出，最后一行是：

```
ok: patched: gzread returns the byte and keeps Z_ERRNO, no report
```

摘自 [`report.txt`](../../../tests/regression/gzread-transparent-stale-next/report.txt)，x86_64 Linux，不打补丁的源码：

```
==PID==ERROR: AddressSanitizer: heap-buffer-overflow on address 0x7926271e0060 at pc 0x7cf628f2901f bp 0x7fff02a49d20 sp 0x7fff02a494c8
READ of size 1 at 0x7926271e0060 thread T0
    #2 0x64c563f4acad in gz_read unpatched/gzread.c:369
    #3 0x64c563f4b208 in gzread unpatched/gzread.c:454
0x7926271e0060 is located 0 bytes after 32-byte region [0x7926271e0040,0x7926271e0060)
```

那个 32 字节的区域是 `gz_look` 分配的输出缓冲区。arm64 macOS 给出同样的报告。

## 影响

作为文件数据返回给调用者的字节，是经由过时的指针读到的，而不是从 `gz_load` 存放它们的地方读到的。字节数是那次部分读取的字节数，最多为缓冲区大小的两倍。过时的指针停在上一次输出结束的地方，所以读取可以像复现中那样从输出缓冲区末尾开始并越过这块分配，也可以落在缓冲区之内而返回旧数据。它由 I/O 错误触发，不由文件的字节触发。

## 修复

[补丁 0003](../../../patches/README.md)：在 `gz_fetch` 的 `case COPY` 中，把赋值 `state->x.next = state->out;` 移到 `gz_load` 调用之前，使它在 `gz_load` 带着部分字节数返回 -1 时也成立。

上游：该补丁就是[拉取请求 #1363](https://github.com/madler/zlib/pull/1363) 的改动，该拉取请求仍处于打开状态。

## 与证明的关系

[gz 读取函数的安全证明](../../proof/gzip.md)针对的是打过补丁的源码。

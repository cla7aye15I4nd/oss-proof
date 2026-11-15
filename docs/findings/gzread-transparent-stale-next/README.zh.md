<!-- source-sha256: 0394eb863f55123e6dc2fdea339f7a3f51657ddc6be04fb7c554417910403b8d -->
# 部分读取之后出错时，`gzread` 从过时的 `x.next` 复制

在透明模式下（输入不是 gzip），如果 `read()` 返回了一些字节而下一次 `read()` 失败，`gz_fetch` 会在设置 `state->x.next` 之前返回。读取函数随后从旧指针复制这些已读到的字节，而旧指针可能正好在输出缓冲区末尾之后一个位置：这是一次越界的堆读取。zlib 的维护者只读本页，就能复现这份报告并作出判断。测试文件在 [`tests/regression/gzread-transparent-stale-next`](../../../tests/regression/gzread-transparent-stale-next/README.md)。

## 状态

- 内存错误：读到输出缓冲区之外的堆内存。在文档用法之内；它需要在读到部分数据之后发生 I/O 错误。
- 在未修改的固定版本源码（`757f0527154291bcf6bfbd6396ecde6bedd2db95`，上游 `develop`）上由 AddressSanitizer 报告，平台为 x86_64 Linux（GCC 15.2）和 arm64 macOS（Apple clang 21）。
- 修复已作为 [PR #1363](https://github.com/madler/zlib/pull/1363) 提交上游。该拉取请求仍处于打开状态；2026-11-14 读取其状态时，维护者还没有答复。验证对象把它作为[补丁 0003](../../../patches/README.md) 应用。

## 调用序列

```c
gzFile f = gzopen("raw.dat", "rb");     /* 128 字节，不是 gzip：透明模式 */
gzbuffer(f, 16);                         /* 输出缓冲区为 32 字节 */
for (int i = 0; i < 48; i++)
    gzgetc(f);                           /* x.have == 0；x.next == out + 32，在缓冲区末尾之后 */
/* 从这里起，该描述符上的 read() 先返回 1 个字节，然后以 EIO 失败 */
gzread(f, buf, 1);                       /* gzread.c:369：memcpy(buf, state->x.next, n) */
```

最后一个调用在固定版本的 `gzread.c` 中这样执行：

1. `gz_read` 发现没有缓冲的输出，调用 `gz_fetch`。
2. 在 `gz_fetch` 的 `case COPY` 中，`gz_load` 存下读到的那一个字节，设置 `x.have = 1`，然后返回 -1，因为下一次 `read()` 以 `EAGAIN` 以外的错误失败。
3. `gz_fetch` 立即返回 -1。`gz_load` 调用之后的赋值 `state->x.next = state->out` 被跳过。
4. `gz_read` 看到 `x.have != 0`，从 `x.next` 复制一个字节，而 `x.next` 仍是 `out + 32`。

完整程序是 [`stale.c`](../../../tests/regression/gzread-transparent-stale-next/stale.c)。它定义了自己的 `read()`，静态链接的库会调用它，用来让第二次 `read()` 失败。它包含 `gzguts.h` 只是为了打印状态。

## 运行

在仓库根目录，`zlib/` 子模块已检出：

```sh
ZLIB_SRC=$PWD/zlib bash tests/regression/gzread-transparent-stale-next/run.sh
```

脚本用 `-fsanitize=address,undefined -fno-sanitize-recover=undefined -fno-omit-frame-pointer -g -O1` 把固定版本源码构建两次：一次不打任何补丁，一次打上 `patches/*.patch`。未打补丁的构建必须报告这次读取。打过补丁的构建不得有任何报告，并且 `gzread` 必须返回 1 并保留错误 `Z_ERRNO`。两项都成立时脚本以状态 0 退出，最后一行是：

```
ok: patched: gzread returns the byte and keeps Z_ERRNO, no report
```

## Sanitizer 判定

摘自 [`report.txt`](../../../tests/regression/gzread-transparent-stale-next/report.txt)，x86_64 Linux，未打补丁的源码：

```
==PID==ERROR: AddressSanitizer: heap-buffer-overflow on address 0x7926271e0060 at pc 0x7cf628f2901f bp 0x7fff02a49d20 sp 0x7fff02a494c8
READ of size 1 at 0x7926271e0060 thread T0
    #2 0x64c563f4acad in gz_read unpatched/gzread.c:369
    #3 0x64c563f4b208 in gzread unpatched/gzread.c:454
0x7926271e0060 is located 0 bytes after 32-byte region [0x7926271e0040,0x7926271e0060)
```

32 字节的区域是 `gz_look`（`gzread.c:100`）分配的输出缓冲区。用 GCC 时，`SUMMARY` 行指向内联的加固版 `memcpy`。为撰写本页在 arm64 macOS 上运行了一次，得到同样的报告，摘要行为 `heap-buffer-overflow gzread.c:369 in gz_read`。

## 范围与严重程度

- **谁会遇到。** 透明模式的读取者，其描述符只交付了请求的一部分，然后以 `EAGAIN` 以外的错误失败：出故障的磁盘、网络文件系统、被重置的套接字或管道。压缩数据路径（`case GZIP`）不受影响。
- **后果。** 作为文件数据返回给调用者的字节，是经由过时的指针读出的，不是从 `gz_load` 存放它们的地方读出的。字节数是已读到的那部分的数量，至多为缓冲区大小的两倍。过时的指针停在上一批输出结束的地方，所以读取可能像复现中那样从输出缓冲区末尾开始并越出这块分配，也可能落在缓冲区内部并返回旧数据。
- **严重程度。** 中等：越界的堆读取，读到的内容会到达调用者。触发它的是 I/O 错误，不是文件的字节。

## `zlib.h` 的说法

zlib.h 把这种情形说成是已处理的：如果在出错之前读到了一些数据，这些数据会被返回，直到取完（`zlib.h:1492`）。未打补丁的代码返回的字节数是对的，字节却是错的。

## 修复

[PR #1363](https://github.com/madler/zlib/pull/1363)，头部 `37627fd3bb47`：在 `gz_fetch` 的 `case COPY` 中，把 `state->x.next = state->out;` 移到 `gz_load` 调用之前，这样当 `gz_load` 带着部分计数返回 -1 时它也成立。

[补丁 0003](../../../patches/README.md) 正是这一改动。上游包含该修复、固定版本越过它之后，补丁就会删除。

## 与证明的关系

[gz 证明说明](../../proof/gzip.md)把这份报告称为 R-2。gz 读取函数的安全证明针对的是打过补丁的源码。

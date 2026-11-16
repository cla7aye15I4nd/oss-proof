<!-- source-sha256: ab12153fb5bc5da259e33677d0d7db0e2d2f51be540e8011efc21f1949016eb0 -->
# gz_reset 从不写入 x.next；gzseek 和 gzdirect 却读取它

对一个新的读取者，`gz_open` 和 `gz_reset` 都不写入其状态中的指针 `x.next`。在还没有任何输出时调用 `gzseek` 和 `gzdirect`，会给这个从未写入的指针加零。按 C 标准的字面规定这是未定义的；除此之外，没有发现别的问题。

状态：按 C 标准的字面规定是未定义的。没有任何 sanitizer 报告它，也没有观察到错误行为，所以它不列为已确认的问题。被验证的源码中由本地补丁 [0005-gz-next-zero-advance.patch](../../../patches/0005-gz-next-zero-advance.patch) 修复；该补丁没有提交上游。同一补丁也修复 [gz-next-dangling-after-direct-read](../gz-next-dangling-after-direct-read/README.md)。

源码：上游 `develop` 的提交 `757f0527154291bcf6bfbd6396ecde6bedd2db95`，加补丁 0001 至 0004。`gzlib.c` 和 `gzread.c` 在 zlib 1.4（提交 `99623ef7097352da7993ba614161fd6a311e046e`，即本项目验证的版本）中逐字节相同；这里没有记录在该版本上的运行。[gzip 证明页](../../proof/gzip.md)针对的是打上全部补丁的源码。

## 问题

`gz_open` 用 `malloc` 分配 `gz_state` 记录，并写入其中一部分字段：

| 由谁写入 | 字段 |
| --- | --- |
| `gz_open` | `size`、`want`、`err`、`msg`、`mode`、`level`、`strategy`、`direct`、`path`、`fd`；读取者还有 `start` |
| `gz_reset`（`gz_open` 最后调用它） | `x.have`、`x.pos`、`past`、`again`、`skip`、错误（`err`、`msg`）、`strm.avail_in`；读取者还有 `eof`、`how`、`junk`；写入者还有 `reset` |
| 两者都不写 | `x.next`、缓冲区指针 `in` 和 `out`、`strm` 中除 `avail_in` 以外的每个字段；读取者还有 `reset`；写入者还有 `eof`、`how`、`junk`、`start` |

这份报告说的是 `x.next`：它在被写入之前就被计算。在读取者上，`x.next` 第一次被写入是在产生输出时（透明模式下的 `gz_look`、`gz_decomp`、`gz_fetch`、`gzungetc`）。有两个函数在此之前就计算它：

- `gzseek64`，不在透明模式时：`n` 是目标中落在输出缓冲区里的部分，缓冲区为空时为 0，而代码照样执行 `state->x.next += n`（`gzlib.c`，注释 `if reading, skip what's in output buffer` 之下的那一段）。
- `gz_skip_have`，由 `gzdirect` 在 `gz_look` 之后调用：对 gzip 文件，`gz_look` 不写 `x.next`，而 `gz_skip_have` 以 `n == 0` 执行 `state->x.next += n`。

读到的值是这块分配的不确定内容。C11 规定，使用可能是陷阱表示的不确定值是未定义的（6.2.6.1p5，J.2）；指针运算只对指向对象或其末尾之后一个位置的指针有定义（6.5.6p8），不确定的指针两者都不是。在 x86_64 上，用通常的编译器，`p + 0` 不改变 `p`，不会出错。

## 调用序列

```c
f = gzopen("data.gz", "rb");      /* gzip 文件 */
gzseek(f, 3, SEEK_SET);           /* 对从未写入的字段执行 x.next += 0 */

f = gzopen("data.gz", "rb");
gzdirect(f);                      /* gz_look（gzip），然后 gz_skip_have：x.next += 0 */
```

两者都是文档允许的用法；zlib.h 描述了 `gzdirect` “`used immediately after gzopen() or gzdopen()`”（紧接在 gzopen() 或 gzdopen() 之后使用）的情形（`zlib.h:1743`）。

## 证据

强度：仅按 C 标准的字面规定。没有 sanitizer 报告它：对任意值做 `p + 0` 既不是越界访问也不是指针溢出，而 MemorySanitizer 不报告只被复制的未初始化值。因此复现让 `gzlib.c` 和 `gzread.c` 中每个 `x.next += n` 都经过一个探针（`probe.h`；计算出的值不变），并打印每次 `n == 0` 的计算。在仓库根目录、`zlib/` 子模块已检出的情况下运行：

```sh
ZLIB_SRC=$PWD/zlib bash docs/findings/gz-reset-next-uninitialised/run.sh
```

成功时最后一行是 `ok: after the fix: x.next is never evaluated with n == 0`。修复前探针打印两行。保留下来的 [report.txt](report.txt)（x86_64 Linux，GCC 15.2）中是下面这样；在 AddressSanitizer 下，新分配的内存填充为 `0xbe`：

```
x.next + 0 at gzlib.c:435, x.next = 0xbebebebebebebebe
x.next + 0 at gzread.c:313, x.next = 0xbebebebebebebebe
```

保留下来的输出来自一份 `gz_look` 少两行的 `gzread.c`。在 `run.sh` 构建的源码中，`gz_skip_have` 的同一条语句是第 315 行。在 arm64 macOS 上用 Apple clang 运行了一次，打印的是 `gzlib.c:435` 和 `gzread.c:315`，其余相同。

文件：`unset.c`、`probe.h`、`run.sh`、`report.txt`。`run.sh` 在 ASan 和 UBSan 下分别构建不含和含 0005 的源码；修复前探针看到这两次计算，修复后一次也没有，两个构建都没有 sanitizer 报告。在 Lean 模型中，新分配的指针字段是 NULL，而 `NULL + 0` 能通过，所以模型也看不到它；暴露它的是“指针字段先写后读”这项源码审查（[安全性](../../spec/safety.md)第 3 节）。

## 范围

所有读取者：在 `gzopen`/`gzdopen` 之后（以及在 `gzrewind` 之后，那时 `x.next` 保留着以前的值），第一次不在透明模式且输出缓冲区为空的 `gzseek`，或对 gzip 文件的 `gzdirect`。在常见平台上没有可观察的后果。

## zlib.h 的说法

没有说明：公开的 `next` 字段 “`can only be used by the gzgetc() macro`”（只能被 gzgetc() 宏使用），而该宏只在 `have` 不为零时读取它。

## 修复

[0005-gz-next-zero-advance.patch](../../../patches/0005-gz-next-zero-advance.patch)：在 `gzseek64` 和 `gz_skip_have` 中，只有 `n` 不为零时才移动 `x.next`。当 `n` 不为零时，`x.have` 不为零，所以该字段在产生那些输出时已经写入。在 `gz_reset` 中把 `x.next` 初始化为 `NULL` 不行：`NULL + 0` 本身在 C 中就是未定义的，clang 的 `-fsanitize=pointer-overflow` 会报告它。在任何路径上，结果、返回值和状态都不变。

拉取请求草稿：[upstream-description.md](upstream-description.md)。

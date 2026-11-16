<!-- source-sha256: 209528851a2fe62064b99074855f4d1344eaac3fb4e8a5f781d5c77f7cde2311 -->
# 直接读取之后 x.next 留在调用者的缓冲区中

一次大的 `gzread` 直接解压到调用者的缓冲区之后，gz 状态里留着一个指向该缓冲区的指针。如果调用者释放了缓冲区，之后的 `gzseek` 或 `gzdirect` 会给这个悬空指针加零。按 C 标准的字面规定这是未定义的；除此之外，没有发现别的问题。

状态：按 C 标准的字面规定是未定义的。没有任何 sanitizer 报告它，也没有观察到错误行为，所以它不列为已确认的问题。被验证的源码中由本地补丁 [0005-gz-next-zero-advance.patch](../../../patches/0005-gz-next-zero-advance.patch) 修复；该补丁没有提交上游。同一补丁也修复 [gz-reset-next-uninitialised](../gz-reset-next-uninitialised/README.md)。

源码：上游 `develop` 的提交 `757f0527154291bcf6bfbd6396ecde6bedd2db95`，加补丁 0001 至 0004。[gzip 证明页](../../proof/gzip.md)针对的是打上全部补丁的源码。

## 问题

对 gzip 文件的大请求，`gz_read` 直接解压到调用者的缓冲区：它把 `strm.next_out` 设为该缓冲区并调用 `gz_decomp`，后者最后执行 `state->x.next = strm->next_out - state->x.have`。随后 `gz_read` 把 `x.have` 设为 0，却让 `x.next` 留在调用者的缓冲区内。调用者可以释放那个缓冲区：`gzread` 返回之后，zlib.h 没有给库任何对它的权利。之后：

- `gzseek64`（非透明，输出缓冲区为空）以 `n == 0` 执行 `state->x.next += n`；
- `gzdirect` 在成员已结束（`how == LOOK`）时调用 `gz_skip_have`，后者做同样的事。

C11 6.2.4p2：指针所指对象的生存期结束时，指针的值变为不确定；6.5.6p8：指针运算需要指向对象的指针。因此这次计算是未定义的。在 x86_64 上，用通常的编译器，`p + 0` 不改变 `p`，该指针也从不被解引用。

## 调用序列

```c
f = gzopen("data.gz", "rb");             /* 文件中有 100000 字节的数据 */
buf = malloc(100000);
gzread(f, buf, 100000);                  /* 直接解压：x.next 指向 buf 内 */
free(buf);
gzseek(f, 1, SEEK_CUR);                  /* 对悬空指针执行 x.next += 0 */
                                         /* 或：gzdirect(f) */
```

## 证据

强度：仅按 C 标准的字面规定。没有 sanitizer 报告它：没有访问，`p + 0` 也不溢出。Lean 模型会报告它：在模型中，对指向已释放块的指针做运算是故障。打补丁后，定理 `gzseek64_dangling_next_ok` 证明在没有缓冲数据时向前定位不会出故障，无论 `x.next` 持有什么。

因为没有 sanitizer 能看到它，复现让 `gzlib.c` 和 `gzread.c` 中每个 `x.next += n` 都经过一个探针（[../gz-reset-next-uninitialised/probe.h](../gz-reset-next-uninitialised/probe.h)；计算出的值不变），并打印每次 `n == 0` 的计算。在仓库根目录、`zlib/` 子模块已检出的情况下运行：

```sh
ZLIB_SRC=$PWD/zlib bash docs/findings/gz-next-dangling-after-direct-read/run.sh
```

脚本在 AddressSanitizer 和 UndefinedBehaviorSanitizer 下把 zlib 源码构建两次：一次用除 0005 以外的 `patches/*.patch`，一次用全部补丁。成功时最后一行是 `ok: after the fix: x.next is never evaluated with n == 0`。修复前探针打印两行。保留下来的 [report.txt](report.txt)（x86_64 Linux，GCC 15.2）中是下面这样：

```
x.next + 0 at gzread.c:313, x.next = inside the freed caller buffer
x.next + 0 at gzlib.c:435, x.next = inside the freed caller buffer
```

保留下来的输出来自一份 `gz_look` 少两行的 `gzread.c`。在 `run.sh` 构建的源码中，`gz_skip_have` 的同一条语句是第 315 行。在 arm64 macOS 上用 Apple clang 运行了一次，打印的是 `gzread.c:315` 和 `gzlib.c:435`，其余相同。

文件：`dangling.c`、`run.sh`、`report.txt`。修复前探针看到这两次计算，修复后一次也没有，两个构建都没有 sanitizer 报告。

## 范围

这样的 gzip 文件读取者：读取请求至少是缓冲区大小的两倍，并且在之后对同一文件调用 `gzseek` 或 `gzdirect` 之前，已经释放了读入的那块内存。在常见平台上没有可观察的后果。

## zlib.h 的说法

对于 `gzread` 返回之后其缓冲区的生存期，没有说明：调用者可以释放它。

## 修复

与 [gz-reset-next-uninitialised](../gz-reset-next-uninitialised/README.md) 相同：[0005-gz-next-zero-advance.patch](../../../patches/0005-gz-next-zero-advance.patch) 只在 `n` 不为零时移动 `x.next`。`n` 不为零时，输出刚在库自己的缓冲区中产生，`x.next` 指向那里。在任何路径上，结果、返回值和状态都不变。

拉取请求草稿（两者共用一个拉取请求）：[../gz-reset-next-uninitialised/upstream-description.md](../gz-reset-next-uninitialised/upstream-description.md)。

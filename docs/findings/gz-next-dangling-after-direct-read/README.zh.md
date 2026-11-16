<!-- source-sha256: fdf44138dd4b7e4b88e205027f5674b8ae745efa56c769f1b7f08425c072d226 -->
# 直接读取之后，`x.next` 留在调用者的缓冲区中

一次大的 `gzread` 直接解压到调用者的缓冲区之后，gz 状态保留着一个指向该缓冲区的指针。如果调用者释放了这个缓冲区，之后的 `gzseek` 或 `gzdirect` 会给这个悬空指针加零。按 C 标准的字面规定这是未定义的：指针所指对象的生存期结束时，指针的值变为不确定（C11 6.2.4p2），而指针运算需要指向对象的指针（6.5.6p8）。没有 sanitizer 报告它。在 x86_64 上，用通常的编译器，`p + 0` 不改变 `p`，而且这个指针从不被解引用。

对 gzip 文件的大请求，`gz_read` 直接解压到调用者的缓冲区：它把 `strm.next_out` 设为该缓冲区并调用 `gz_decomp`，后者以 `state->x.next = strm->next_out - state->x.have` 结束。随后 `gz_read` 把 `x.have` 设为 0，却让 `x.next` 仍指向调用者的缓冲区。之后：

- `gzseek64`（非透明，输出缓冲区为空）以 `n == 0` 执行 `state->x.next += n`；
- `gzdirect` 在成员已结束时（`how == LOOK`）调用 `gz_skip_have`，后者做同样的事。

## 到达它的调用

```c
f = gzopen("data.gz", "rb");             /* 含 100000 字节的数据 */
buf = malloc(100000);
gzread(f, buf, 100000);                  /* 直接解压：x.next 指向 buf 内部 */
free(buf);
gzseek(f, 1, SEEK_CUR);                  /* 对悬空指针执行 x.next += 0 */
                                         /* 或者：gzdirect(f) */
```

gzip 文件的读取者在这种情况下到达它：它以至少两倍缓冲区大小的请求读入某块内存，并在之后对同一文件调用 `gzseek` 或 `gzdirect` 之前释放了这块内存。`zlib.h` 没有让库在 `gzread` 返回之后对该缓冲区保有任何权利：调用者可以释放它。

## 证据

按 C 标准的字面规定未定义，并用探针展示。没有 sanitizer 报告这次计算：没有发生访问，`p + 0` 也不溢出。复现让 `gzlib.c` 和 `gzread.c` 中每一处 `x.next += n` 都经过一个探针（[probe.h](../gz-reset-next-uninitialised/probe.h)；计算出的值不变），并打印每一次 `n == 0` 的计算。在仓库根目录、已检出 `zlib/` 子模块时运行：

```sh
ZLIB_SRC=$PWD/zlib bash docs/findings/gz-next-dangling-after-direct-read/run.sh
```

脚本在 AddressSanitizer 和 UndefinedBehaviorSanitizer 下把 zlib 源码构建两次：一次带 `patches/*.patch` 中除 0005 以外的补丁，一次带全部补丁。成功时最后一行是 `ok: after the fix: x.next is never evaluated with n == 0`。修复之前探针打印两行。摘自 [report.txt](report.txt)，x86_64 Linux：

```
x.next + 0 at gzread.c:313, x.next = inside the freed caller buffer
x.next + 0 at gzlib.c:435, x.next = inside the freed caller buffer
```

在带补丁 0001 至 0004 的源码中，`gz_skip_have` 的这条语句位于 `gzread.c:315`。修复之后探针看不到任何这样的计算，两个构建都没有 sanitizer 报告。

Lean 模型会报告这种情形：在模型中，对指向已释放块的指针做运算是故障。带补丁时，定理 `gzseek64_dangling_next_ok` 证明：没有任何已缓冲数据时的向前定位不会发生故障，无论 `x.next` 持有什么值。

## 修复

[补丁 0005](../../../patches/README.md) 只有当 `n` 不为零时才推进 `x.next`。当 `n` 不为零时，输出刚刚在库自己的缓冲区中产生，`x.next` 正指向那里。任何路径上的结果、返回值和状态都不变。同一补丁也修复 [gz-reset-next-uninitialised](../gz-reset-next-uninitialised/README.md)。

上游：该补丁是本地补丁，没有提交。

## 与证明的关系

[gzip 证明](../../proof/gzip.md)针对的是打过补丁的源码。

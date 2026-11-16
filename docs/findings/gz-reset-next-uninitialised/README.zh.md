<!-- source-sha256: 298c0305aa56ec472f61fcfc94921108cfc4f3e28ffd312c50e6f1d118e4c388 -->
# `gz_reset` 从不写入 `x.next`；`gzseek` 和 `gzdirect` 却读取它

对一个新的读取者，`gz_open` 和 `gz_reset` 都不写入其状态中的指针 `x.next`。在还没有任何输出时调用 `gzseek` 和 `gzdirect`，会给这个从未写入的指针加零。按 C 标准的字面规定这是未定义的：读到的值是这块分配的不确定内容（C11 6.2.6.1p5，J.2），而指针运算只对指向对象或其末尾之后一个位置的指针有定义（6.5.6p8）。没有 sanitizer 报告它；在 x86_64 上，用通常的编译器，`p + 0` 不改变 `p`。

`gz_open` 用 `malloc` 分配 `gz_state` 记录，并写入其中一部分字段：

| 由谁写入 | 字段 |
| --- | --- |
| `gz_open` | `size`、`want`、`err`、`msg`、`mode`、`level`、`strategy`、`direct`、`path`、`fd`；读取者还有 `start` |
| `gz_reset`（`gz_open` 最后调用它） | `x.have`、`x.pos`、`past`、`again`、`skip`、错误（`err`、`msg`）、`strm.avail_in`；读取者还有 `eof`、`how`、`junk`；写入者还有 `reset` |
| 两者都不写 | `x.next`、缓冲区指针 `in` 和 `out`、`strm` 中除 `avail_in` 以外的每个字段；读取者还有 `reset`；写入者还有 `eof`、`how`、`junk`、`start` |

在读取者上，`x.next` 第一次被写入是在产生输出时（透明模式下的 `gz_look`、`gz_decomp`、`gz_fetch`、`gzungetc`）。有两个函数在此之前就计算它：

- `gzseek64`，不在透明模式时：`n` 是目标中落在输出缓冲区里的部分，缓冲区为空时为 0，而代码照样执行 `state->x.next += n`。
- `gz_skip_have`，由 `gzdirect` 在 `gz_look` 之后调用：对 gzip 文件，`gz_look` 不写 `x.next`，而 `gz_skip_have` 以 `n == 0` 执行 `state->x.next += n`。

## 到达它的调用

```c
f = gzopen("data.gz", "rb");      /* gzip 文件 */
gzseek(f, 3, SEEK_SET);           /* 对从未写入的字段执行 x.next += 0 */

f = gzopen("data.gz", "rb");
gzdirect(f);                      /* gz_look（gzip），然后 gz_skip_have：x.next += 0 */
```

每个读取者都会到达它：紧接 `gzopen` 或 `gzdopen` 之后，第一次不在透明模式且输出缓冲区为空的 `gzseek`，或者对 gzip 文件的 `gzdirect`；`gzrewind` 之后也一样，那时 `x.next` 保留着它之前的内容。两者都是文档用法；`zlib.h` 描述的 `gzdirect` 就是 `used immediately after gzopen() or gzdopen()`（紧接 gzopen() 或 gzdopen() 之后使用，`zlib.h:1743`）。

## 证据

按 C 标准的字面规定未定义，并用探针展示。没有 sanitizer 报告这次计算：对任意值做 `p + 0` 既不是越界访问，也不是指针溢出，而 MemorySanitizer 不报告仅被复制的未初始化值。因此复现让 `gzlib.c` 和 `gzread.c` 中每一处 `x.next += n` 都经过一个探针（`probe.h`；计算出的值不变），并打印每一次 `n == 0` 的计算。在仓库根目录、已检出 `zlib/` 子模块时运行：

```sh
ZLIB_SRC=$PWD/zlib bash docs/findings/gz-reset-next-uninitialised/run.sh
```

脚本在 AddressSanitizer 和 UndefinedBehaviorSanitizer 下把 zlib 源码构建两次：一次带 `patches/*.patch` 中除 0005 以外的补丁，一次带全部补丁。成功时最后一行是 `ok: after the fix: x.next is never evaluated with n == 0`。修复之前探针打印两行。摘自 [report.txt](report.txt)，x86_64 Linux；在 AddressSanitizer 下，新分配的内存被填为 `0xbe`：

```
x.next + 0 at gzlib.c:435, x.next = 0xbebebebebebebebe
x.next + 0 at gzread.c:313, x.next = 0xbebebebebebebebe
```

在带补丁 0001 至 0004 的源码中，`gz_skip_have` 的这条语句位于 `gzread.c:315`。修复之后探针看不到任何这样的计算，两个构建都没有 sanitizer 报告。

Lean 模型看不到这种情形：在模型中，新分配的内存里的指针字段是 `NULL`，而 `NULL + 0` 通过。暴露它的是“指针字段在被读取之前已被写入”这项源码审查（[安全](../../spec/safety.md)，第 3 节）。

## 修复

[补丁 0005](../../../patches/README.md)：在 `gzseek64` 和 `gz_skip_have` 中，只有当 `n` 不为零时才推进 `x.next`。当 `n` 不为零时，`x.have` 不为零，所以该字段在产生那段输出时已被写入。在 `gz_reset` 中把 `x.next` 初始化为 `NULL` 是不行的：`NULL + 0` 在 C 中本身就是未定义的，clang 的 `-fsanitize=pointer-overflow` 会报告它。任何路径上的结果、返回值和状态都不变。同一补丁也修复 [gz-next-dangling-after-direct-read](../gz-next-dangling-after-direct-read/README.md)。

上游：该补丁是本地补丁，没有提交。

## 与证明的关系

[gzip 证明](../../proof/gzip.md)针对的是打过补丁的源码。

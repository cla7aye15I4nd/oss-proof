<!-- source-sha256: 6322304962ca2f849a11638bcf70c91520169ffca72d10eb622a42e04ed3f7f9 -->
# 工具函数：分配与常量查询

`zutil.c` 包含默认分配器（`zcalloc`、`zcfree`）和三个常量查询。两个有文档的查询 `zlibVersion` 和 `zlibCompileFlags` 是安全的。分配器包装函数有精确的所有权效果：成功的分配增加一个存活块，失败的分配不增加任何块，释放恰好移除它的那个块。本页陈述这些结果，并说明流证明从中取用哪些事实，又自己证明哪些事实。

源文件：`zlib/zutil.c` 和 `zlib/zutil.h`；翻译：`ZlibF/Zlib/zutil.c.lean`。公开契约在 [API 页](../spec/api/utility.md)中。术语见[术语表](../glossary.md)。

## 证明了什么

| 结果 | 类别 | 定理 | 模块 |
| --- | --- | --- | --- |
| `Goal.zlibVersion_safety`、`Goal.zlibCompileFlags_safety`（`ZlibF/Spec/Safety/Queries.lean`） | 安全，必需 | `zlibVersion_safety`、`zlibCompileFlags_safety` | `ZlibF/Proof/public-stateless-safety.lean` |
| `Goal.zlibVersion`、`Goal.zlibCompileFlags` | 功能 | `zlibVersion`、`zlibCompileFlags` | `ZlibF/Proof/public-zlib-version.lean`、`ZlibF/Proof/public-zlib-compile-flags.lean` |
| `Goal.zError` | 非必需：`zlib.h` 把 `zError` 列为未写入文档的函数 | `zError` | `ZlibF/Proof/public-zerror.lean` |
| 分配器包装函数 `zcalloc` 和 `zcfree` | 内部，供每个流证明使用 | `zcalloc_safe`、`zcalloc_correct_some`、`zcalloc_correct_size`、`zcalloc_correct_none`、`zcfree_safe`、`zcfree_correct`、`zcfree_correct_null`、`zcalloc_zcfree_no_leak` | `ZlibF/Proof/zutil.c.lean` |

以上全部[已登记](../checking/README.md)在 `tests/audit/theorems.txt` 中，并[已在提交 `bde170e9` 上验收](../checking/README.md)（[进度，范围](../progress.md#scope)）。

`zcalloc` 和 `zcfree` 不是公开函数。流的无泄漏性是 [inflate](inflate.md) 和 [deflate](deflate.md) 的序列安全定理中的一个子句，这些定理在每次分配和释放处使用这些包装函数的结果。

## 包装函数定理陈述了什么

在这个构建上，`zcalloc` 尽管叫这个名字，调用的却是 `malloc`，并且不把块清零。

| 定理 | 陈述 |
| --- | --- |
| `zcalloc_safe` | 在 `Fresh` 的堆上，对每个 `items` 和 `size`，调用都返回。它要么返回 `NULL`，只有分配计数器变动；要么返回一个新的可写字节块的起始位置，并恰好把这个块加入存活块。 |
| `zcalloc_correct_some` | 当预言让调用成功时，块是可写的，它的大小是 `items * size` 模 `2^32` 的结果，内容是任意的。 |
| `zcalloc_correct_size` | 当 `items * size` 小于 `2^32` 时，块恰好有 `items * size` 个字节。 |
| `zcalloc_correct_none` | 当预言拒绝时，结果是 `NULL`，堆只在调用计数器上有变化。 |
| `zcfree_safe` | 对于 `NULL`，或者一个存活的可写字节块的起始位置，调用都返回：`NULL` 什么都不改变，否则恰好移除那个块。 |
| `zcfree_correct`、`zcfree_correct_null` | 释放一个存活块，恰好把这个块从存活块中移除；释放 `NULL` 什么都不改变。 |
| `zcalloc_zcfree_no_leak` | `zcalloc` 之后对其结果调用 `zcfree`，会返回，分配失败时也是如此，并且存活块的集合与之前相同。 |

## 流证明自己证明什么

包装函数定理对下面这些事什么都没有说。[inflate](inflate.md) 和 [deflate](deflate.md) 的初始化、复制和结束定理逐一证明它们。

- **乘积不回绕。** `zcalloc(opaque, items, size)` 按 32 位 `unsigned` 算术计算 `items * size`。依赖普通乘积的调用者要证明它小于 `2^32`，然后使用 `zcalloc_correct_size`。下表给出流的各次分配中最大的乘积。
- **字段先写后读。** 新分配的块里是任意整数，而在模型中，新分配的记录里是 `NULL` 指针（[未初始化内存](../spec/safety.md#uninitialised-memory)）。分配并不使指针字段可以安全读取。
- **每个块恰好释放一次。** 非 NULL 的释放要求这个块是存活的。堆记录存活性；证明中的 `Owns` 关系把存活块指派给一个流，结束证明和失败清理证明把每个被拥有的块释放一次。
- **分配失败之后的清理。** `deflateInit2_` 分配一个状态和四个缓冲区，并在四次调用全部完成之后，把四个缓冲区的结果放在一起测试。所以较早的分配失败并不阻止较晚的分配，清理会释放这次尝试中每一个成功的分配。`inflateInit2_`、解码器窗口的延迟分配以及两个复制函数各有自己的失败情形。

| 这个构建上的流分配 | 以字节计的最大 `items * size` |
| --- | --- |
| 压缩器窗口：`w_size * 2` | 65536 |
| 压缩器 `prev`：`w_size * sizeof(Pos)` | 65536 |
| 压缩器 `head`：`hash_size * sizeof(Pos)` | 131072 |
| 压缩器待输出缓冲区：`lit_bufsize * 4` | 131072 |
| 解码器窗口：`(1U << wbits) * 1` | 32768 |
| `deflateCopy`、`inflateCopy` | 上面相应的缓冲区大小 |

状态记录（`deflate_state`、`inflate_state`）是作为模型的记录分配的，所以它们的 `sizeof` 不进入任何乘积。缓冲区的界来自经过验证的参数，以及流不变量中保存的大小等式。这张表覆盖所列出的流分配；它不是 gz 函数或其他路径的最大值。

## 常量查询与错误查询

| 函数 | 结果与帧 |
| --- | --- |
| `zlibVersion` | 它返回指向版本字符串的指针，这是一个只读的静态对象，内容就是契约给出的内容。堆保持不变。 |
| `zlibCompileFlags` | 它返回由这个构建的类型宽度和启用的源码分支导出的标志：169。堆保持不变。 |
| `zError(err)`（非必需） | 越界分支选择十项消息表中的第 9 项。否则 `-6 ≤ err ≤ 2`，所以 `2 - err` 在 `[0, 8]` 内，没有有符号溢出。它返回那一项，这是一个只读的静态对象。堆保持不变。 |

`zError` 在计算 `2 - err` 之前测试 `err` 的范围；如果先做减法，对任意的 `int` 可能溢出。169 这个值只对这个构建成立：其他的类型宽度或构建选项给出其他的标志。

常量返回值仍然是一个精确的契约：错误的版本指针或者改动的一个标志位，都会让这个函数的证明变异体检查失败（[证明变异体](../checking/proof-mutants.md)）。

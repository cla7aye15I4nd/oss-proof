<!-- source-sha256: bc663ad9df8e529c7a58e8a7202cbbbed748c49252dccea81fb5b7dc18e71508 -->
# 工具函数：分配与常量查询

源文件为 `zlib/zutil.c` 和 `zlib/zutil.h`，翻译为 `ZlibF/Zlib/zutil.c.lean`。这些函数支持两个流实现。公开契约见 [API 页面](../spec/api/utility.md)，所有权角色由[安全规范](../spec/safety.md)定义。

两个有文档的查询函数是安全的，分配器包装函数具有准确的所有权效果。本页解释流证明从分配器取得的大小算术，以及常量查询。

## 已证明什么

| 结果 | 类别 | 定理 | 模块 |
| --- | --- | --- | --- |
| `Goal.zlibVersion_safety`、`Goal.zlibCompileFlags_safety`（`ZlibF/Spec/Safety/Queries.lean`） | 安全，必需 | `zlibVersion_safety`、`zlibCompileFlags_safety` | `ZlibF/Proof/public-stateless-safety.lean` |
| `Goal.zlibVersion`、`Goal.zlibCompileFlags` | 功能性，保留 | `zlibVersion`、`zlibCompileFlags` | `ZlibF/Proof/public-zlib-version.lean`、`ZlibF/Proof/public-zlib-compile-flags.lean` |
| `Goal.zError` | 非必需：`zlib.h` 把 `zError` 列为无文档函数 | `zError` | `ZlibF/Proof/public-zerror.lean` |
| 分配器包装函数 `zcalloc` 和 `zcfree` | 内部，每个流证明都用到 | `zcalloc_safe`、`zcalloc_correct_some`、`zcalloc_correct_size`、`zcalloc_correct_none`、`zcfree_safe`、`zcfree_correct`、`zcfree_correct_null`、`zcalloc_zcfree_no_leak` | `ZlibF/Proof/zutil.c.lean` |

这些都登记在 `tests/audit/theorems.txt` 中，并在提交 `bde170e9` 上被接受（[进度，范围](../progress.md#scope)）。

`zcalloc` 和 `zcfree` 不是公开函数。流的无泄漏性是 [inflate](inflate.md) 和 [deflate](deflate.md) 序列安全定理的一个子句，这些定理在每次分配和释放处使用上述包装结果。

默认 LP64 分配器分支使用 `malloc`，尽管函数名为 `zcalloc`。它不会清零块。初始化证明必须建立所需字段写入，包括模型不追踪的指针写入。

## 调用者的大小算术

分配请求包含“多少个元素”和“每个元素多少字节”。在 `zcalloc(opaque, items, size)` 中，它们分别是 `items` 和 `size`；`opaque` 是传入分配器的调用者上下文。只有先证明乘积未溢出，才能把返回块的模型容量解释为期望的总字节数。

此分支中，`zcalloc(opaque, items, size)` 以 32 位 `unsigned` 算术计算 `items * size`。`zcalloc_correct_size` 忠实描述该乘积。若调用者期望普通乘积，它在依赖分配容量之前证明该乘积低于 `2^32`。

| 默认流分配 | 最大字节乘积 |
| --- | --- |
| `deflateInit2_` 状态 | LP64 `sizeof(deflate_state)` |
| 压缩器窗口：`w_size * 2` | 65536 |
| 压缩器 `prev`：`w_size * sizeof(Pos)` | 65536 |
| 压缩器 `head`：`hash_size * sizeof(Pos)` | 131072 |
| 压缩器待输出缓冲区：`lit_bufsize * 4` | 131072 |
| `inflateInit2_` 状态 | LP64 `sizeof(inflate_state)` |
| 解码器窗口：`(1U << wbits) * 1` | 32768 |
| `deflateCopy`, `inflateCopy` | 上述相应状态和缓冲区大小 |

表中的窗口尺度 `w_size`、哈希桶数 `hash_size` 和符号容量尺度 `lit_bufsize` 都在初始化参数校验后确定；`sizeof(Pos)` 是每个位置表项占用的字节数。因此，容量按“表项数乘以每项字节数”换算成字节。状态大小必须来自所选 ABI 布局，并与 C 布局检查一致；它们不是跨配置的数学常量。缓冲区界限从已验证参数和流不变量保留的大小等式推出。此表只涉及所列流分配，不声称给出了所有 gz 或其他 API 路径的最大分配。

## 成功与失败效果

分配成功时增加一个指定模型大小的新鲜存活块；失败时返回空指针，不增加存活块。两种情况都不能让尚未写入的新指针字段变得可安全读取。未初始化整数依据[运行时规则](../spec/safety.md#uninitialised-memory)取任意值。

`zcfree` 接受空指针，或分配器接口允许的块。非空释放要求对应的存活所有权声明。End 和失败清理证明必须恰好提供一次。堆记录存活性和分配历史；证明的 `Owns` 关系把存活块归属于流。

`deflateInit2_` 分配一个状态和四个缓冲区。合并的缓冲区失败检查在各次分配之后，因此前面一次失败不表示之后的分配从未尝试。清理必须释放该次尝试中所有成功分配，按源代码规定清除或保留字段，并恢复先前存活块集合。`inflateInit2_`、延迟解码窗口分配，以及两个复制函数，都需要各自的失败情形组合。仅分配器包装定理不能证明任何这些生命周期清理。初始化和复制定理证明了它：见 [inflate](inflate.md) 和 [deflate](deflate.md)。

## 常量与错误查询

| 函数 | 要求的结果与帧性质 |
| --- | --- |
| `zError(err)` | 越界分支选择第 9 项。否则 `-6 ≤ err ≤ 2`，故 `2 - err` 位于 `[0, 8]`，没有有符号溢出。返回十项消息表的准确项，保持堆不变。 |
| `zlibVersion` | 返回所选版本字符串指针，静态内容满足契约，保持堆不变。 |
| `zlibCompileFlags` | 从所选类型位宽和启用的源分支推出准确数值标志，保持堆不变。 |

常量返回仍是准确契约：错误的版本指针或改变的标志位会使该函数的证明变异失败（[检查指南](../checking/README.md)）。

## C 对应检查

`zError` 在求值 `2 - err` 前检查错误范围。提前执行减法可能对任意 `int` 溢出。`zlibCompileFlags` 在已审查配置中得到 169；应保留产生它的源代码判断，不能把这个数当作普遍常量。返回的版本与错误字符串是只读静态对象。

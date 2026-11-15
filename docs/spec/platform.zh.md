<!-- source-sha256: dee8df589f94fbc5a02823810963e91ab267e7bc9ca6ca1a0031e76ae7c6ac31 -->

# 已接受的平台假设

范围是默认 x86_64 Linux/LP64 静态构建，使用默认分配器。
本页陈述目标所取的唯一环境前提：没有哪个字节对象达到或超过 `2^63` 字节。
操作系统、编译器和硬件的性质不在证明之内；[可信基础](../trusted-base.md)列出了它们。

## 字节对象大小

每个被表示的字节对象都少于 `2^63` 字节。该上界作为系统环境的一部分被接受。它就是 LP64 的 `PTRDIFF_MAX` 对象大小限制：没有分配器返回更大的对象。
它覆盖调用者提供的存储、原始字节块、静态数组和嵌入的字节数组视图。

用 `h` 表示执行前的堆，`ref` 表示一个字节对象的引用，`a` 表示该引用对应的字节数组。`Space.get h ref` 查询这个对象，`a.size` 给出它的字节数。精确谓词是 [PlatformMemory.lean](../../ZlibF/Spec/PlatformMemory.lean) 中的
`ZlibF.PlatformMemory.ByteObjectsFit`：

```text
对每个被表示的字节引用 ref 及其数组 a：
    若 Space.get h ref = some a，则 a.size < 2^63
```

它分别约束每个对象，不约束所有分配的总大小，也不约束重复调用累计处理的长度。
默认、常见和全部支持的[输入范围](input-configurations.md)共享这一假设；
它不是额外的颜色，也不是压缩参数。

## 目标在哪里使用它

每个需要这一前提的安全目标都把它明确写出。它写在调用开始时的堆上，也写在调用者每次交还的堆上。

| 目标 | 前提所在位置 |
| --- | --- |
| 对流的一次调用（`Goal.<function>_safety`、`Goal.inflate_sequence_safety`、`Goal.deflate_sequence_safety`） | `StreamCallDomain` 以及 `StreamSequenceSafety` 的第 2 条：写在这次调用的堆上。inflate 的历史（`StreamReachable .inflate`）在每次调用时和每次调用者编辑之后也带着它。deflate 的历史不带。 |
| `compress*`、`uncompress*` | `CompressorSafety`、`UncompressCountedSafe` 和 `UncompressSingleSafe` 的前提。 |
| gzip 文件接口 | `GzHistory`：写在每次打开时的堆上，以及每次调用者编辑之后。`GzOpenSafe` 和 `GzDopenSafe` 也取这一前提。 |
| 回调解码器 | `BackSafeReachable` 和 `Goal.inflate_back_sequence_safety`：写在每次 `inflateBack` 调用的堆上。`BackPlatform` 要求回调保持它。 |
| 校验和、查询、初始化、结束、复制、拒绝 | 不需要，也没有写。 |

这一上界使同一对象内两个有效偏移量的差处于有符号 64 位范围。
快速解码器的入口证明从中推导对象大小方面的事实。

库自己的分配保持这一前提：运行时分配器拒绝超过 `PTRDIFF_MAX` 的请求，所以新块满足上界
（`ByteObjectsFit.allocB`，[Proof/PlatformMemory.lean](../../ZlibF/Proof/PlatformMemory.lean)）。
对调用者的存储和任意的堆，它是假设，不是推导出来的。[偏差](../deviations.md)的“平台字节对象范围”一行记录了它。

没有写出这一前提的目标，不需要它就成立。本页不向任何陈述添加假设。

## 其他指针义务

大小上界不能证明指针仍然存活、已初始化、与另一个指针属于同一对象，或偏移有效。
这些是独立的[安全性义务](safety.md)。运行时关于空指针算术的选择仍记录在
[模型比较](safety.md#null-pointers-and-pointer-differences)和[可信基础](../trusted-base.md)中。

<!-- source-sha256: c7d15b2690eff58fe57c9fb0026b5c90baee91bd19d17927636b568c6f9aa1ca -->

# 平台假设：对象大小

目标对系统只取一条前提：**没有哪个字节对象达到或超过 `2^63` 字节。**
这是目标平台（默认 x86_64 Linux LP64 构建）的事实：在这个平台上，没有分配器会返回大于 `PTRDIFF_MAX` 的对象。
它不需要调用者去检查。本页陈述这条前提，说明为什么需要它，并列出带有它的目标。

操作系统、编译器和硬件的性质没有被证明；它们列在[可信基础](../trusted-base.md)中。

## 前提

模型中每个字节对象都少于 `2^63` 字节：调用者提供的缓冲区、库分配的块、静态数组，以及内嵌在记录里的字节数组。

Lean 谓词是 [PlatformMemory.lean](../../ZlibF/Spec/Common/PlatformMemory.lean) 中的
`ZlibF.PlatformMemory.ByteObjectsFit`：

```text
对每个字节对象引用 ref 及其数组 a：
    若 Space.get h ref = some a，则 a.size < 2^63
```

| 这条前提说了什么 | 这条前提没有说什么 |
| --- | --- |
| 每个单独的对象都少于 `2^63` 字节。 | 它不涉及所有分配的总和，也不涉及一个流在多次调用中处理的总长度。 |
| | 它不说明指针合法、已初始化或没有越界。那些是另外的[安全义务](safety.md#the-obligations)。 |

**为什么需要它。** 指向同一个对象的两个指针之差是 `ptrdiff_t`，一个有符号 64 位整数。
在达到或超过 `2^63` 字节的对象里，这个差可能溢出，而这是未定义行为。有了这条前提，每个这样的差都放得下。
快速解码器（`inflate_fast`）的入口证明就是从它推出各自的大小事实的。

**哪里不必假设它就成立。** 模型的分配器拒绝 `2^63` 字节及以上的请求，所以库分配的每个块都满足它
（`ByteObjectsFit.allocB`，[Proof/PlatformMemory.lean](../../ZlibF/Proof/PlatformMemory.lean)）。
对调用者的内存，以及历史起点的堆，这条前提是假设的。
[偏离记录](../deviations.md)中有“平台字节对象范围”一行。

## 哪些目标带有它

需要这条前提的目标会明确写出它：写在调用开始时的堆上，以及调用者每次交回的堆上。
没有写出它的目标，不靠它也成立。

| 目标 | 前提出现在哪里 |
| --- | --- |
| 对流的一次调用：`Goal.<function>_safety`、`Goal.inflate_sequence_safety`、`Goal.deflate_sequence_safety` | 在这次调用的堆上（`StreamCallDomain`，以及 `StreamSequenceSafety` 的子句 2）。 |
| inflate 历史（`StreamReachable .inflate`） | 还出现在历史中此前的每次调用上，以及调用者每次修改之后。 |
| deflate 历史（`StreamReachable .deflate`） | 不出现在此前的堆上。不论此前的堆是否满足这个上界，deflate 流都可达。所以 deflate 目标覆盖的历史更多。 |
| `compress*`、`uncompress*` | `CompressorSafety`、`UncompressCountedSafe` 和 `UncompressSingleSafe` 的一条前提。 |
| gzip 文件接口 | 在每次打开时的堆上，以及调用者每次修改之后（`GzHistory`；`GzOpenSafe` 和 `GzDopenSafe` 也带有它）。 |
| 回调解码器 | 在每次 `inflateBack` 调用的堆上（`BackSafeReachable`、`Goal.inflate_back_sequence_safety`）。回调必须保持它（`BackPlatform`）。 |
| 校验和、`zlibVersion`、`zlibCompileFlags`、初始化、End、复制、拒绝 | 没有写出：这些目标不靠它也成立。`inflateEnd` 和 `inflateCopy` 从 inflate 历史出发，而 inflate 历史如第二行所说带有它。 |

这条前提对每个[输入范围](input-configurations.md)都相同。它不是压缩参数。

## 这条前提不涵盖什么

模型对 NULL 指针算术的处理是另一条限制，说明见
[安全性，空指针与指针差](safety.md#null-pointers-and-pointer-differences)和[可信基础](../trusted-base.md)。

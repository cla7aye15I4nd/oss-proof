<!-- source-sha256: 449ceae1e81d97058d8128059114ed7a09fbbc6b82ba5ff664a2db9d5b47c312 -->
# Adler-32：有界的和与模细化

Adler-32 函数在下面所陈述的定义域上是安全的：它们会返回，只读调用者的缓冲区，并且让堆保持不变。它们还返回 Adler-32 的值；那一部分是功能性的，不是安全结果所必需的。本页解释 `adler32_z` 的论证，其他入口都归结到它。

源文件：固定版本的 `zlib/adler32.c`；翻译：`ZlibF/Zlib/adler32.c.lean`。数学契约是[格式指南](../spec/format/README.md)中的 `F-adler-incremental`。[API 页](../spec/api/checksums.md)规定空缓冲区、包装函数和合并操作。术语见[术语表](../glossary.md)。

## 证明了什么

| 结果 | 类别 | 定理 | 模块 |
| --- | --- | --- | --- |
| `Goal.adler32_safety`、`Goal.adler32_z_safety`、`Goal.adler32_combine_safety`、`Goal.adler32_combine64_safety`（`ZlibF/Spec/Safety/Checksums.lean`） | 安全，必需 | `adler32_safety`、`adler32_z_safety`、`adler32_combine_safety`、`adler32_combine64_safety` | `ZlibF/Proof/public-stateless-safety.lean` |
| `Goal.adler32`、`Goal.adler32_z` | 功能 | `adler_public`、`adler_z_public` | `ZlibF/Proof/public-adler-update.lean` |
| `Goal.adler32_combine`、`Goal.adler32_combine64` | 功能 | `combine_public`、`combine64_public` | `ZlibF/Proof/public-adler-combine.lean` |
| 它们背后的局部执行结果 | 两者 | `adler32_z_safe`、`adler32_z_correct`、`adler32_z_correct_ne_one`、`adler32_combine_safe`、`adler32_combine_correct` | `ZlibF/Proof/adler32.c.lean` |

以上全部[已登记](../checking/README.md)在 `tests/audit/theorems.txt` 中，并[已在提交 `bde170e9` 上验收](../checking/README.md)（[进度，Scope 一节](../progress.md#scope)）。

安全目标说的是：调用在没有故障的情况下返回，并且让堆与原来完全一样。每个安全定理都是同一个函数的完整契约去掉值之后的部分。所以在下面关于值的论证中，只有“无故障”的部分是必需的。

## 假设了什么

缓冲区是一个 `len` 字节的可读范围，或者是 `len = 0` 时的 `NULL`（`AdlerBufferBytes`）。

这比 `zlib.h` 窄，后者的文字接受任意长度下的 `NULL`。`adler32_z` 的 C 代码这样处理 `NULL` 缓冲区：

```c
    if (len == 1) {
        adler += buf[0];        /* reads through NULL */
        ...
    }
    if (buf == Z_NULL)
        return 1L;
```

长度不为 1 时，C 不做读取就返回 1。长度为 1 时，它在测试 `NULL` 之前读取 `buf[0]`，这是未定义行为。这些目标排除了每一种非零长度下的 `NULL`。这一收窄在[偏离记录](../deviations.md)中有一行（“Adler 初始化查询”），那里也记录了向上游提交的报告。

合并函数没有前提：它们对每个参数都是安全的，包括伪造的校验和与负的长度。

## 一个字节步骤保持什么

记 `B = 65521`，`NMAX = 5552`。把输入的累加器拆成 `a = adler & 0xffff` 和 `s = (adler >> 16) & 0xffff`。对一个字节 `b`，数学上的步骤是

```
α' = (α + b) mod B
σ' = (σ + α') mod B
```

未取模的机器步骤是 `a' = a + b; s' = s + a'`。如果机器上的和没有回绕，那么由 `a ≡ α (mod B)` 和 `s ≡ σ (mod B)` 可以推出这一步之后同样的同余式。随后模 B 取余，就恢复出精确的数学值对。

因此证明有两个不同的部分。安全部分：机器在没有故障的情况下遍历了正确的字节。功能部分：在所陈述的起始值定义域上，它的和细化了模递推。

## 读取与终止

对于非 NULL 的缓冲区，前提说整个范围 `[off, off + len)` 可读。消耗了 `k` 个字节之后的循环不变量是：游标为 `off + k`，剩余计数为 `len₀ - k`，并且 `k ≤ len₀`。每次读取发生时都有 `k < len₀`，所以它在范围之内。每次指针自增都停在“尾后一位”的位置或其之前。结果就是 `adler32_z_safe`。

| 分支 | 消耗的字节 | 度量 |
| --- | --- | --- |
| `len == 1` | 一个字节 | 没有循环 |
| `len < 16` | 字节循环的每个循环体消耗一个 | 测试之前的剩余计数 |
| 整批 | `347 × 16 = 5552` | 剩余的批数和展开组的组数 |
| 尾部 | 先是 16 个一组，然后是单个字节 | 剩余计数 |

测试 `while (len--)` 在它最后那次失败的测试上使局部的无符号计数器回绕。翻译按原样保留这个测试；回绕后的值不会引发又一次迭代。每个度量都远低于循环燃料，所以证明既说明了数学上的终止，也排除了 `Fault.outOfFuel`。

如上所示，单字节快速路径先于空缓冲区检查。在这些目标的定义域上，`NULL` 缓冲区有 `len == 0`，调用不读内存就返回 1。这个函数不写调用者的内存，也不分配任何块。

## 为什么在默认构建上各批不会回绕

两次取模之间至多有 5552 个字节步骤。从 16 位的分量出发，经过 `j` 个这样的步骤之后，一个方便的界是

```
a ≤ 65535 + 255 j
s ≤ 65535 + j (65535 + 255 × 5552)
```

对于 `j ≤ 5552`，这给出 `a ≤ 1481295` 和 `s ≤ 8224215375`，低于 `2^64`。因此默认 LP64 下 `unsigned long` 的加法与普通的自然数算术一致。这个宽松的界是 64 位论证专用的；别的字宽需要为它自己的分支找一个合适的界。

16 字节的展开把字节步骤的不变量保持十六次。把它应用到每个整批和尾部，然后取模，就得到按 `a | (s << 16)` 打包的结果。移位和打包都不超出 64 位，因为取模之后两个分量都小于 `2^16`。

## 精确的起始值范围

正常的增量校验和从已取模的分量开始。公开函数还接受任意整数作为累加器，所以关于值的陈述必须说明非规范的分量怎样解释。

在短分支中，低分量满足 `a ≤ 65535 + 15 × 255 = 69360 < 2B`；一次条件减法就把它约化了。高分量则模 B 取余。在单字节分支中，两个分量都只做一次条件减法。用这种方式约化高分量，要求传入的 `s < B`，因为新的低分量小于 B，这时两者之和小于 `2B`。

因此，递推论证在 `len ≠ 1` 时覆盖任意的累加器字（`adler32_z_correct_ne_one`），在传入的高分量小于 B 时覆盖单字节情形（`adler32_z_correct`）。空缓冲区的返回是另一种单独的情形。安全性对每个分支中的每个累加器字都成立（`adler32_z_safe`）。公开的值目标 `Goal.adler32_z` 覆盖每个种子：它的规格 `adlerValue` 按 C 的算法描述单字节分支。

这一区别是可以观察到的。对于 `adler32_z(0xFFFFFFF0, "\0", 1)`，掩码后的低分量是 65520，高分量是 65535。字节步骤之后它们的和是 131055。一次减法剩下 65534，函数返回 `0xFFFEFFF0`。完全的模约化会得到高分量 13。这个调用是内存安全的；而一个把任意起始字都约化的规格会给出不同的值。正因为有这个反例，公开的值没有陈述为完全的模约化。

## 包装函数与合并

`adler32` 就是转换它的 32 位长度参数之后的 `adler32_z`。

`combine` 函数有一个单独的算术证明。它展开拼接时的两个累加和，计入初始值修正，并证明翻译后的取模运算计算的就是这个公式。`adler32_combine_correct` 陈述这个结果：对于 `|B| < 2^63` 的字节串 `A` 和 `B`，从初始值 1 出发，有 `adler32_combine64(adler32(A), adler32(B), |B|) = adler32(A ++ B)`。`adler32_combine_safe` 证明这些函数对每个参数都不会出故障。负的长度返回文档规定的哨兵值。

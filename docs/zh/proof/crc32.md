<!-- source-sha256: 1a69070d011c866f1ef1804e89feedfaf589e60419baef99d6201ada524190a2 -->
# CRC-32：字节范围、编织与多项式含义

CRC-32 函数在其文档给出的定义域上是安全的：它们会返回，只读调用者的缓冲区和静态表，并且让堆保持不变。它们还返回 CRC-32 的值；那一部分是功能性的，不是安全结论所必需的。本页解释为什么每次读取都在范围之内，对齐测试是怎样建模的，以及各个值定理陈述了什么。

源文件：`zlib/crc32.c`；翻译：`ZlibF/Zlib/crc32.c.lean`。被翻译的分支是默认 x86_64 Linux 的那一个：小端字，没有硬件 CRC 指令，以及“编织”（braid）的字循环，参数取源码中的 `W = 8`（每个字的字节数）和 `N = 5`（每个块的字数）。[API 页](../spec/api/checksums.md)给出公开定义域；[格式指南](../spec/format.md)规定这个值（那里名为 `F-crc-incremental` 的子句）。术语见[术语表](../glossary.md)。

## 证明了什么

| 结论 | 类别 | 定理 |
| --- | --- | --- |
| `Goal.crc32_safety`、`Goal.crc32_z_safety`、`Goal.crc32_combine_safety`、`Goal.crc32_combine64_safety`、`Goal.crc32_combine_gen_safety`、`Goal.crc32_combine_gen64_safety`、`Goal.crc32_combine_op_safety` | 安全，必需 | 去掉 `Goal.` 之后的同名定理 |
| `Goal.crc32`、`Goal.crc32_z` | 功能 | `crc32`、`crc32_z` |
| 五个合并目标 | 功能 | `gen`、`gen64`、`op`、`combine`、`combine64` |
| 同样的结论，针对模型拥有的每一种字节数组（堆块、静态数组、记录内的数组），在每一种对齐下 | 两者 | `crc32_z_all_byte_views`、`crc32_all_byte_views` |
| 堆上的字节块以及辅助函数 | 两者 | `crc32_z_safe`、`crc32_z_correct`、`multmodp_safe`、`multmodp_correct`、`x2nmodp_safe`、`x2nmodp_correct`，以及合并的各项结论 |
| `get_crc_table` | 非必需：`zlib.h` 把它列为未文档化的函数 | `get_crc_table` |

安全目标说的是：调用在没有故障的情况下返回，并且让堆与原来完全一样。每个安全定理都是同一个函数的完整契约去掉值之后的部分。

## 假设了什么

- 静态表是库自己的表（`CrcGlobals`）。
- 缓冲区是一个 `len` 字节的可读范围，或者是 `NULL`（`BufferBytes`）。
- `crc32_combine_op` 接收由 `crc32_combine_gen` 或 `crc32_combine_gen64` 返回的算子。这就是 `zlib.h` 文档给出的定义域。在它之外 C 可能挂起：见[辅助函数的契约](#helper-contracts)。
- 受信任、但不在命题之中的：对齐测试背后的地址模型，以及把 C 的字加载解读为八次字节读取（[见下文](#alignment-and-represented-addresses)）。地址模型属于运行时，字加载属于手工翻译，分别是[可信基础](../trusted-base.md)的第 2 项和第 3 项。描述这两者的是[模型的限制](../model-limits.md#conditions-on-the-model-that-goals-state)中“CRC 地址与字访问”一行。

相应的行在[偏离记录](../deviations.md)中。

## 为什么每次读取都在范围之内

`NULL` 缓冲区返回 0。否则函数对传入的 CRC 取反并掩码，视情况处理编织的字块，然后处理剩余字节，并返回取反后的结果。

```mermaid
flowchart LR
    Start["非 NULL 的字节范围"] --> Threshold{"len 至少为 47？"}
    Threshold -->|是| Align["至多消耗 7 个字节以对齐"]
    Align --> Blocks["blks = len / 40，至少为 1"]
    Blocks --> Braids["读取 blks 个块，每块 5 个字"]
    Braids --> Tail["字节尾部"]
    Threshold -->|否| Tail
    Tail --> Result["最后取反"]
```

阈值是 `N*W + W - 1 = 47`。在至多七个对齐字节之后，至少还剩 40 个字节，所以在 `while (--blks)` 之前有 `blks ≥ 1`。循环处理 `blks₀ - 1` 个块，循环之后的代码处理最后一个块。如果 `blks = 0`，前置自减会使计数器回绕；阈值排除了这种情况。

每个块读取五个 8 字节的字，并前进五个字。因为 `40 * blks₀ ≤ len_after_alignment`，所有的字读取都落在原来的范围内。剩余长度小于 40。尾部先是在 `len ≥ 8` 时运行的一个展开的字节循环，然后是一个字节循环；其中没有更多的字读取。每个循环体消耗的字节数恰好等于它从 `len` 中减去的数。

`crc32_z_safe` 对堆上的字节块陈述这个结论：调用会返回，堆保持不变，所以每次加载都在范围之内，也没有哪个循环耗尽燃料。`crc32_z_all_byte_views` 对模型的每一种字节数组陈述它。

查表同样在范围之内。对于字节查表，`x & 0xff < 256`。编织表的行下标是 `k < W = 8`，每行有 256 项。提取字节的移位使用 `8k ≤ 56`，小于 64 位的字宽。循环度量是剩余字节数、剩余块数或固定的行计数器；每一个都远低于运行时的燃料上界。

## 对齐与被表示的地址

C 通过 `buf` 的地址测试它的对齐：`while (len && ((z_size_t)buf & (W - 1)) != 0)`。模型中的指针没有地址。模型只提供低三位：

- 堆上的字节块从一个对齐的地址开始，所以指向它内部的指针的低位就是其偏移量的低位；
- 静态字节数组，或者记录内的字节数组，从模 8 的任意余数处开始。这个余数对于给定的堆是固定的，证明并不知道它是多少。

有四条定理陈述这个模型给出了什么。这里的*布局*是指给每个字节数组指派一个基地址。

- `every_layout_is_representable`：对每一种让每个堆字节块都起始于 8 的倍数的布局，都有某个堆具有这种布局的余数。没有哪个静态数组或内嵌数组被强制对齐。
- `mask_refines_base_plus_offset`：在余数与某个布局一致的堆里，模型给一个指针的低三位，就是它的基地址加偏移量的低三位。这个和超出 64 位时也成立。
- `pointer_advance_preserves_low_bits`：在每一个堆里，把指针前移 `count` 个字节，就是把它的低三位加上 `count` 再模 8。
- `first_aligned_offset`：在每一个堆里，对每一个低三位为 `r` 的指针，向前 `(8 - r) mod 8` 个字节（至多 7 个）的位置低三位为 0，而更早的位置都不是。这是关于位置的算术：它没有说那些字节在缓冲区之内。

CRC 目标对每一个堆做全称量化，所以它们对每一种余数都成立，也没有给它们添加对齐前提。

翻译后的字读取按小端顺序拼接八个字节。在 C 中，这次读取是通过一个转换为 `z_word_t *` 的指针做的加载。两者一致（包括对这个转换按严格别名规则的解读），以及真实地址背后一般的 ABI 布局，都是受信任的；它们没有被证明。[模型的限制](../model-limits.md#representation-gaps-and-proof-obligations)在“地址与布局模型不完整”一行记录了这一点。C 还读取一个局部字节序标记的低字节来选择分支；在这个目标平台上它选择小端分支，大端分支不会运行。大端辅助函数中只证明了 `crc_word_big_safe`。

## 值（功能）

`crc32_z_correct` 对堆上的字节块陈述这个值：对每个种子、每个长度和偏移量的每一种对齐，`crc32_z` 返回字节列表的 `ZlibF.Spec.crc32Update`，并且让堆保持不变。`crc32_z_all_byte_views` 把它推广到静态数组和内嵌数组。规格 `crc32Update` 是一个逐位的寄存器，不提及翻译。

论证如下：

- CRC 寄存器的一步（`crcBit`）在 GF(2) 上是线性的（`crcBit_xor`）。把 `m` 步记作 `pw m`；它就是在模 CRC 多项式的意义下乘以 `x^m`。
- 表的内容是在内核中通过求值检查的，不是假设的：`crc_table[n] = pw 8 n`（`crc_table_eq`），`crc_braid_table[j][n] = pw (8 * (40 - j)) n`（`braid_eq`），以及 `x2n_table` 的平方链和 `x^(2^32) = x`（`Xt_sq`、`Xt_wrap`）。
- `crc_word` 的字步骤是 64 位字上的一个线性映射。它在 64 个单位向量上与它的闭式一致，因此处处一致（`Phi_eq_Psi`）。
- 编织循环保持一个不变量，它把五个进行中的 CRC 与迄今已消耗字节的寄存器联系起来（`loopBlk_ok`）。随后最后那一串 `crc_word` 调用按 C 的顺序把它们合并。
- `crc32_append` 是用于拆分输入的拼接律。

## 辅助函数的契约

本表中每个 `_safe` 和 `_correct` 定理还陈述堆保持不变。两个 `_diverges` 定理陈述的则是故障：运行以 `Fault.outOfFuel` 结束，不返回堆。

| 函数 | 证明了什么 |
| --- | --- |
| `crc32` | `crc32_safe`、`crc32_correct`：包装函数转换它的 32 位长度，并调用 `crc32_z`。 |
| `crc_word` | `crc_word_safe`：它对每个 64 位字都返回。`crc_word_correct`：对于寄存器 `c` 和堆块中按小端字读出的八个字节，`crc_word(c ^ word)` 是经过这八个字节之后的寄存器。 |
| `crc_word_big`、`byte_swap` | 只有 `crc_word_big_safe`。它们是大端辅助函数，目标平台不运行它们；它们没有值定理。 |
| `multmodp(a, b)` | C 从第 31 位向下扫描一个掩码，并在 `a` 的最低置位处停止。`multmodp_safe`：当 `a` 的低 32 位不全为零且 `b < 2^32` 时，它返回一个小于 `2^32` 的值。`multmodp_diverges`：当 `a` 的低 32 位为零时，循环永不结束（运行结果是 `Fault.outOfFuel`）。`multmodp_correct`：对于 `a = x^n`，结果是 `b` 乘以 `x^n` 再模 CRC 多项式。每个调用者从自己的定义域提供这条前提。 |
| `x2nmodp(n, k)` | `x2nmodp_safe`、`x2nmodp_correct`：对于 `n ≥ 0` 和每个 `k`，它返回 `x^(n·2^k)` 模多项式的结果。下标 `k & 31` 在 32 项的表之内。负的 `n` 由调用者排除：循环 `while (n)` 对 `n` 做算术右移，不会结束。 |
| `crc32_combine_gen64`、`crc32_combine_gen` | `crc32_combine_gen64_safe`、`crc32_combine_gen_safe`：对每个 `len2` 它都返回；`len2 < 0` 时结果为 0，`len2 ≥ 0` 时结果小于 `2^32` 且非零。`_correct` 定理：对于 `len2 ≥ 0`，算子是 `x^(8·len2)` 模多项式的结果。 |
| `crc32_combine_op` | `crc32_combine_op_safe`：对每个为 0 或者低 32 位中有置位的 `op`，它都返回；每个生成出来的算子都是这样的。`crc32_combine_op_diverges`：对于低 32 位为零的非零 `op`，运行结果是 `Fault.outOfFuel`。`Goal.crc32_combine_op_safety` 是针对生成出来的算子写出的。 |
| `crc32_combine64`、`crc32_combine` | `crc32_combine64_safe`、`crc32_combine_safe`：它们对每个参数都返回，长度为负时返回 0。`_correct` 定理：对于字节串 `A` 和 `B`，以 `B` 的长度作为 `len2` 合并 `crc32(A)` 和 `crc32(B)`，得到 `crc32(A ++ B)`。 |
| `get_crc_table` | `get_crc_table_safe`、`get_crc_table_correct`：它返回指向只读静态表的指针，表项就是规定的那些；没有分配。 |

校验和函数不写内存，也不分配任何东西。其他构建分支（动态表初始化、硬件 CRC）没有被翻译；[偏离记录](../deviations.md)中有关于构建的那一行。

### `crc32_combine_op` 在定义域之外的挂起

`multmodp` 扫描它第一个操作数的第 31 位到第 0 位，在最低的置位处离开循环。`crc32_combine_op` 在调用 `multmodp` 之前对 `op == 0` 返回 0，而 `crc32_combine_gen` 或 `crc32_combine_gen64` 返回的算子要么是 0，要么在低 32 位中有置位。`Goal.crc32_combine_op_safety` 说的是：对每个这样的算子，调用都会返回；它不覆盖任何别的 `op`。对于低 32 位为零的非零 `op`，例如 `crc32_combine_op(1, 2, 1UL << 32)`，定理 `crc32_combine_op_diverges` 证明翻译会耗尽燃料。对 C 而言，这是对源码的解读，源码里是同一个循环：掩码变成零，循环永不结束。

## 静态表的证据

一次源码审查重新生成了 CRC 头文件，并报告各表逐字节相同：256 项的 CRC 表、八行的编织表和 32 项的多项式幂表。那是忠实度的证据，不是证明。上面的值定理并不依赖它：它们在内核中检查表的内容。同一次审查还覆盖了 `trees.h` 和 `inffixed.h` 的静态表（288 项的字面量树、30 项的距离树、512 项的距离映射和 256 项的长度映射）。

<!-- source-sha256: d3722267d8b80b4f06aff7cc107dd3941be07a29fe483d1814c6f44f7b1942cb -->

# 安全性：目标陈述了什么

本页定义“安全”。本项目对默认 x86_64 Linux 构建中 zlib 每个有文档的公开函数证明的，就是这一性质。
一次安全的调用没有未定义行为，会返回，只写它的目标点名的内存，并且不泄漏。
本页依次给出定义、一个完整的例子、已证明的内容和所作的假设，最后说明定理所在的模型有哪些限制。

## 定义

每条定理说的都是 C 源码的 Lean 翻译，它运行在一个内存模型上（**堆**：一张由**块**组成的表，
每个分配出来的对象或调用者的对象占一个块）。**目标**是针对一个函数或一个调用序列、需要证明的 Lean 命题。
一次调用**安全**，指下面四个子句全部成立。

| # | 子句 | 用 C 的话说 | 在模型中 |
| --- | --- | --- | --- |
| 1 | 没有未定义行为，没有内存错误 | 没有越界读写，没有空指针解引用，没有释放后使用，没有重复释放，没有有符号溢出，没有非法移位，也没有[义务表](#the-obligations)列出的其他操作。 | 执行不以 `Fault.ub` 结束。 |
| 2 | 终止 | 调用会返回。 | 执行不以 `Fault.outOfFuel` 结束：没有循环达到 `2^64` 次迭代的上限。 |
| 3 | 帧性质 | 调用只写它的目标点名的内存：对 `inflate` 来说，是 `z_stream`、库为这个流分配的存储、`next_out` 处的 `avail_out` 个字节，以及（如果挂有 gzip 头记录）这个记录和它的三个缓冲区。其他对象的内容都不变。 | `Frame`、`BufferFrame`。 |
| 4 | 无泄漏 | 调用返回时，已分配的块等于调用前已分配的块，加上流新拥有的块，减去流原先拥有而现在放弃的块。没有别的块出现或消失。 | `LiveChange`，其中的所有权由状态里的指针读出。 |

API 页面把子句 1 和 2 合起来写作“调用**返回**”：在模型中，执行以 `.ok` 结束，带有一个返回值和一个堆。
C 的错误码也是正常返回，同样在覆盖范围内，例如输入畸形时的 `Z_DATA_ERROR`，或 `malloc` 失败后的 `Z_MEM_ERROR`。

这些目标对每个参数值、每个输入字节序列、每次 `malloc` 的每种结果都成立，并且覆盖调用序列能到达的每个状态。
输出字节是什么、返回哪个码，属于功能行为。它不是安全性的一部分，
也不是安全结论所必需的（见[进度，范围](../progress.md#scope)）。

## 一个完整的例子

对同一个流做三次调用：

```c
z_stream s;                           /* 自动存储：没有清零 */
s.zalloc = Z_NULL; s.zfree = Z_NULL; s.opaque = Z_NULL;
s.next_in = Z_NULL; s.avail_in = 0;

int r = inflateInit2(&s, 15);         /* 调用 1 */
if (r != Z_OK) return r;

s.next_in  = in;   s.avail_in  = n;   /* 调用者的修改 */
s.next_out = out;  s.avail_out = m;

r = inflate(&s, Z_NO_FLUSH);          /* 调用 2 */
inflateEnd(&s);                       /* 调用 3 */
```

**调用 1。** `inflateInit2` 是宏，展开为 `inflateInit2_(&s, 15, ZLIB_VERSION, sizeof(z_stream))`。
它的目标是 `Goal.inflateInit2__safety`
（[Safety/Initialisation.lean](../../ZlibF/Spec/Safety/Initialisation.lean)），
由定理 `InitSafetyProof.inflateInit2__safety`
（[Proof/public-init-safety.lean](../../ZlibF/Proof/public-init-safety.lean)）证明。

- 适用条件：`s.zalloc` 和 `s.zfree` 各自是 `Z_NULL` 或默认分配器的函数（`InitArguments`）。
  `s` 的其他字段可以是任意值：这个记录不需要清零。
  目标还覆盖流指针为 `NULL` 的情况、每个 `windowBits`、每个 `stream_size`，
  以及为 `NULL` 或有一个可读字节（值任意）的版本指针。堆必须是库堆；
  这是对模型的条件（见[对象表示](#object-representation)），不是对调用者的要求。
- 调用返回，并且只写 `s`。如果返回 `Z_OK`，`s` 就是一个可达流，
  这次调用分配而没有释放的每个块都归这个流所有。
  返回其他码时，已分配的块与调用前相同（`InitResultSafe`）。

**调用者的修改。** 在两次调用之间，调用者可以改 `next_in`、`avail_in`、`next_out` 和 `avail_out`，
也可以改流不拥有的任何内存（`Rebuffer`）。流仍然可达。
（对模型的两个条件保持不变：堆是库堆，并且满足平台大小上界。）

**调用 2。** 目标是 `Goal.inflate_safety`
（[Safety/Streams.lean](../../ZlibF/Spec/Safety/Streams.lean)），
由 `StreamCallSafetyProof.inflate_safety`
（[Proof/public-stream-call-safety.lean](../../ZlibF/Proof/public-stream-call-safety.lean)）证明。

- 适用条件：流可达；`in` 是 `NULL` 或有 `n` 个可读字节；`out` 是 `NULL` 或有 `m` 个可写字节；
  两个范围不重叠，并且都不在库为这个流分配的内存里（`StreamCallDomain`）。
  它还带有[平台大小上界](platform.md)这一前提。
- 对每个 `flush` 值、`in[0..n)` 的每种内容（不论格式是否正确），调用都返回。
  流仍然满足不变量，所以可以接着再调用。调用只写 `s`、流自己的块和 `out[0..m)` 这些字节。
  `in` 的字节、`out[m)` 之后的字节以及其他所有对象都不变。
  如果这次调用分配了滑动窗口，调用后窗口归流所有（`StreamCallSafe`）。
- 不论返回哪个码，流仍然可达，所以调用 3 也在覆盖范围内。

**调用 3。** 目标是 `Goal.inflateEnd_safety`（文件与调用 2 相同）。
在每个可达流上，调用返回 `Z_OK`，把 `s.state` 置为 `NULL`，只写 `s` 和流自己的块，
并且恰好释放流拥有的那些块。

**合起来。** 三次调用中任何一次分配的块，在 `inflateEnd` 返回时都已释放：
初始化和 `inflate` 只会留下归流所有的新块，而 `inflateEnd` 释放流拥有的每个块。

```mermaid
flowchart LR
    A["初始化之前：没有为这个流分配任何块"] -->|"inflateInit2 返回 Z_OK"| B["流拥有它的状态"]
    B -->|"inflate：可能分配窗口"| C["流拥有它的状态，以及（如果已分配）它的窗口"]
    C -->|"inflateEnd"| D["没有为这个流分配的块"]
```

这些定理不说 `r` 是多少，也不说 `inflate` 往 `out` 写了什么。那些是功能性事实。

## 已证明的内容与所作的假设

**已证明。** 必需目标共 63 个，列在 `tests/audit/public-api.json` 中：
54 个是某个函数的 `safety_goal`，另有 5 个在 `safety_goals` 列表里（两个序列目标和三个拒绝目标），
还有 4 个 `nonvacuity_goals`。每个目标都有一条类型与它完全相同的定理，列在 `tests/audit/theorems.txt` 中；
目标本身列在 `tests/audit/proved-goals.txt` 中。这一层级叫**已登记**。
只有验收套件也在一个指明的提交上全部通过，结果才是**已验收**；
[进度](../progress.md#scope)写明了这个提交。各层级的定义见[术语表](../glossary.md#status)。

**假设。**

- [平台大小上界](platform.md)：没有哪个字节对象达到或超过 `2^63` 字节。
- 下文的[调用者义务](#4-caller-obligations)。凡是比 `zlib.h` 窄的前提，
  在[偏离记录](../deviations.md)中都有一行。
- 下文的[模型的限制](#3-faults-undefined-behaviour-and-model-gaps)：在这些情形下，关于模型的证明不能对 C 作出定论。
- [可信基础](../trusted-base.md)：运行时、手工翻译、编译器、操作系统。

**没有单独陈述的。** gzip 文件函数（从 `gzopen` 到 `gzclose`）和三个回调解码函数
（`inflateBackInit_`、`inflateBack`、`inflateBackEnd`）没有各自的目标。
每一族由一个已登记的、针对每个调用序列的目标覆盖：`Goal.gz_sequence_safety` 和 `Goal.inflate_back_sequence_safety`。
为每个函数各立一个目标是剩余工作（见[进度](../progress.md#remaining-work)）。
回调目标的每个序列都从一次成功的 `inflateBackInit_` 开始；
对失败或被拒绝的初始化调用，它什么也没有说（见[回调契约](api/inflate-back.md)）。

这些目标怎样证明，见[证明方法](../proof/method.md)。

## 需要分清的六种情形 {#terms-and-reading-guide}

**未定义行为（UB）**是 C 标准不作任何保证的程序动作
（[C 草案 N1570 第 3.4.3 节](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf)）。
它不一定导致崩溃。一次执行成功了，或者与测试一致，并不说明这个动作有定义。

| 情形 | 在本项目中的含义 |
| --- | --- |
| 有定义的错误返回 | C 通过文档规定的结果拒绝一个请求。畸形的压缩字节可以返回 `Z_DATA_ERROR` 而没有 UB。安全性覆盖这些调用。 |
| 在目标的前提之外 | 目标对这次调用什么也不说。仅凭这一点，不能说 C 的执行是 UB。 |
| C 的 UB | C 的规则对这个操作不作任何保证。 |
| `Fault.ub` | 模型检测到一次违规。模型并不能检测 C 的每一种 UB（见[模型的限制](#3-faults-undefined-behaviour-and-model-gaps)）。 |
| `Fault.outOfFuel` | 模型里的某个循环用完了 `2^64` 次迭代。不终止不是 C 的 UB，但在这里算安全性失败。 |
| 泄漏 | 一个块仍然处于已分配状态，而目标的账本没有点到它。即使没有任何 C 操作是 UB，泄漏在这里也算安全性失败。 |

由实现定义的选择，按所选构建来陈述。未指明的结果，凡是影响调用结果的，都要对每一种容许的结果给出证明。
这两类都不是 UB。

下文用到的一些术语在[术语表](../glossary.md)中：目标、历史、拒绝、非空性、已登记。
其余术语在首次出现的地方定义。

## 一次调用 {#1-what-a-function-theorem-must-say}

安全目标的形式是：对满足前提的每个堆和每个参数，翻译后的调用返回 `.ok`，带有一个值和一个堆，
并且调用后的堆满足下面各子句。模型中一次执行的类型是 `Heap → Except Fault (value × Heap)`
（[Runtime/Monad.lean](../../ZlibF/Runtime/Monad.lean)）：它要么以故障结束，
要么以 `.ok` 结束，带有一个值和调用后的堆。

| 子句 | Lean 定义 | 含义 |
| --- | --- | --- |
| 调用返回 | `call = .ok (value, after)` | 执行既不是 `Fault.ub`，也不是 `Fault.outOfFuel`。 |
| 不变量 | `StreamInvariant`、`GzInv`、`BackValid` | 调用后的状态可以作为下一次调用的起点。 |
| 帧性质 | `Frame`、`BufferFrame`、`CallbackFrame` | 点名集合之外的对象不变。 |
| 分配账本 | `LiveChange` | 调用后已分配的块，等于调用前的块减去移除集合，再加上新建集合。 |

这些子句没有一条是按定义成立的：翻译错了，或者 zlib 错了，每一条都可能不成立。

### 帧

一个块**存活**，指它处于已分配状态：它存有一个对象，并且没有被释放。

`Frame before after changed`（[Public/Initialisation.lean](../../ZlibF/Spec/Public/Initialisation.lean)）说：
调用前存活、且不在集合 `changed` 中的每个块，调用后内容相同，只读标志也相同。
它还说模型的三个部分不变：库的常量表、决定以后哪些分配失败的函数（**分配预言**），
以及给未初始化整数取值的函数（见[未初始化内存](#uninitialised-memory)）。
新块归分配账本管，不归帧管。

`BufferFrame before after changed regions`（[Public/History.lean](../../ZlibF/Spec/Public/History.lean)）
加上了调用者的字节范围。一个区域是一个指针加一个长度。调用可以写区域之内；
同一对象中所有区域之外的字节不变，对象的大小也不变。
目标就是这样表达“`inflate` 在 `next_out` 处至多写 `avail_out` 个字节”的。

一次流调用的帧（`StreamCallSafe`，[Safety/Streams.lean](../../ZlibF/Spec/Safety/Streams.lean)）是：

| 部分 | 内容 |
| --- | --- |
| 可以改变的块 | `z_stream` 记录（`StreamRoot`）。流拥有的块（`StreamOwned`）。一个 gzip 头记录：传给 `inflateGetHeader` 的那个，或者在 `inflate` 期间挂在流上的那个（`StreamHeaderRecord`）。 |
| 可以写的调用者范围（`StreamWriteRegions`） | 对 `inflate`、`deflate` 和 `deflateParams`：`next_out` 处的 `avail_out` 个字节；对 inflate 流，还有所挂头记录的 `extra`、`name` 和 `comment` 缓冲区。对 `inflateGetDictionary` 和 `deflateGetDictionary`：字典指针处的 32768 个字节。其他调用：没有。 |

### 分配账本 {#the-leak-ledger}

`LiveChange before after created removed`（[Public/Initialisation.lean](../../ZlibF/Spec/Public/Initialisation.lean)）是

```text
对每个块 b：
    b 在调用后存活  ⇔  （b 在调用前存活，且不属于 removed）或 b 属于 created
```

下文把分配账本简称为**账本**。它是一个等价式，所以两个方向都是精确的。
一个块只有被目标点名为移除，才会消失。一个块要保持已分配状态，要么调用前就已分配，要么被目标点名为新建。
“无泄漏”就是后一个方向加上所有权：

| 调用 | 新建 | 移除 |
| --- | --- | --- |
| 一次流调用 | 调用后流拥有、而调用前不存活的块 | 调用前流拥有、而调用后不再拥有的块 |
| 返回 `Z_OK` 的初始化 | 一组块，全部归新流所有 | 无 |
| 返回其他码的初始化 | 无 | 无 |
| `inflateEnd`、`deflateEnd` | 无 | 恰好是流拥有的那些块 |
| 返回 `Z_OK` 的复制 | 新状态拥有的块 | 无 |
| 返回 `Z_MEM_ERROR` 的复制 | 无 | 无 |
| 被拒绝的 `NULL` 流或不一致的流 | 无 | 无 |
| 校验和、`zlibVersion`、`zlibCompileFlags` | 调用后的堆就是调用前的堆 | |

**所有权**（`StreamOwned`、`GzOwned`）是从调用后状态里的指针读出来的：
状态记录、窗口，以及这些指针指向的其他缓冲区。证明无法自行选择它。
所以，如果库分配了一个块又丢失了对它的引用，这个块就是存活的、不被拥有的，
也不在 `created` 中：账本就不成立。

**在已经持有一个流的记录上初始化或复制。** 四个初始化目标对记录的 `state` 字段没有任何条件（`InitArguments`），
两个复制目标对目的记录也没有，所以当这个记录还持有一个存活的流时，这些目标同样成立。
这次调用不会释放旧状态。旧状态的块在调用前存活，调用后仍然存活，账本允许这一点，而记录不再指向它们。
因此对初始化和复制来说，“无泄漏”的意思是：调用不泄漏它自己分配的东西。
在重新使用一个记录之前先结束其中的流，是调用者的责任，与 C 中一样。

对 `compress*` 和 `uncompress*`，目标用另一种形式表达同样的内容。
调用后的堆等于调用前的堆写入输出字节之后的样子（对 `uncompress*` 还要写入长度单元），其他都不变。
临时的流和它的分配都已消失：没有新的存活对象留下
（`SameObjectsUpToTableShape`，[Public/Memory.lean](../../ZlibF/Spec/Public/Memory.lean)）。
“除表形状外”只容许模型自己的簿记有所不同：内部的某张表可以多出一些空表项，
下一个块编号和分配计数器可以已经前进。空表项不是存活的块，
也没有任何 C 操作能观察到表的长度或这两个计数。只读标志只对调用前存活的块作比较。

### 初始化与被调用函数

初始化从调用者的内存出发建立不变量；没有哪个目标假设不变量。
被调用函数的规格是一条关于翻译后的被调用函数的定理，从来不是调用它的函数的假设。

```mermaid
flowchart LR
    I[初始化] -->|建立| V[不变量]
    V --> A[允许的调用]
    A -->|保持| V
    V --> E[结束]
    E --> Z[流拥有的块都不再存活]
    I -->|分配失败：不留下存活的块| Z
```

## 调用与调用序列 {#2-calls-and-sequences}

关于一次调用的目标，必须说明这次调用可以从哪些状态开始。
目标使用**可达**状态：由一段真实的调用序列产生的状态。这样一段序列叫作**历史**。

一个流可达（`StreamReachable`，[Public/History.lean](../../ZlibF/Spec/Public/History.lean)），
指它是下面某一步的结果：

| 步骤 | 条件 |
| --- | --- |
| 初始化 | `inflateInit2_` 或 `deflateInit2_` 返回了 `Z_OK`。当时堆是库堆，记录的 `zalloc` 和 `zfree` 各自是 `NULL` 或默认分配器的函数，版本字符串以 `'1'` 开头，`stream_size` 等于 `sizeof(z_stream)`。 |
| 调用者的修改（`Rebuffer`） | 从一个可达流出发：调用者替换了 `next_in`、`avail_in`、`next_out` 或 `avail_out`，或者改了流不拥有的内存。堆仍然是库堆。 |
| 调用 | 从一个可达流出发：一次允许的调用（`StreamOperation`）带着合法的参数（`StreamArguments`）返回了，返回码任意。 |
| 复制 | `inflateCopy` 或 `deflateCopy` 从一个可达的源复制到另一个记录，并返回了 `Z_OK`；目的流可达。 |

对 inflate 流，调用者的修改和调用这两步还带有[平台大小上界](platform.md)。

不假设之前任何调用的规格：历史是一串真实的执行。

`StreamSequenceSafety`（[Public/Sequences.lean](../../ZlibF/Spec/Public/Sequences.lean)）有三个子句。
`Goal.inflate_sequence_safety` 和 `Goal.deflate_sequence_safety`
（[Safety/Sequences.lean](../../ZlibF/Spec/Safety/Sequences.lean)）就是这个命题分别用于两种流。

1. 每个可达流都满足不变量。
2. 在可达流上再做一次允许的调用，调用返回，保持不变量，并具有上文所述的帧和分配账本。
3. 在可达流上，End 调用返回 `Z_OK`（对 deflate 还可能是 `Z_DATA_ERROR`，即流在完成之前被结束），
   把状态指针置为 `NULL`，只写记录和流拥有的块，并且恰好移除流拥有的块。

单个函数的目标 `Goal.<function>_safety` 是子句 2 限于该函数的调用；
对 `inflateEnd` 和 `deflateEnd` 则是子句 3。对子句 2，它的前提是 `StreamCallDomain`：
流可达，每个字节对象少于 `2^63` 字节（见[平台](platform.md)），并且 `StreamArguments` 成立。
两个 End 目标只有一个前提：流可达。

**非空性。** 如果没有任何流可达，针对“每个可达流”的目标就会平凡地成立。
非空性目标排除了这种情况：有一个具体的堆满足初始化的前提，
初始化在它上面成功，并给出一个可达流
（`Goal.inflate_initialisation_domain`、`Goal.deflate_initialisation_domain`）。

gzip 文件接口和回调解码器的结构相同，各有自己的历史：
`GzHistory`（[Public/GzSafety.lean](../../ZlibF/Spec/Public/GzSafety.lean)）和
`BackSafeReachable`（[Public/Sequences.lean](../../ZlibF/Spec/Public/Sequences.lean)）。
gz 历史在两次调用之间还有一步留给外部：文件系统和描述符（即**世界**）可以变成任何良构的状态。
具体命题见 [gzip 文件契约](api/gz-file.md)和[回调契约](api/inflate-back.md)。

### 终止与循环燃料

翻译中的每个循环至多运行 `2^64` 次迭代（`C.fuel`，[Runtime/Monad.lean](../../ZlibF/Runtime/Monad.lean)）。
这个上限叫作**燃料**。每个循环在进入时得到这份燃料；它不是整次调用共用的一份预算。
用完燃料的循环使执行以 `Fault.outOfFuel` 结束。
所以，一个结论为 `.ok` 的目标就证明了调用中的每个循环都在 `2^64` 次迭代之内结束。这就是终止性结论。

这个上限不会掩盖 C 的任何行为：没有哪次真实执行会让一个循环迭代 `2^64` 次。
随迭代次数增长的未定义行为，例如每次迭代都前进的有符号 64 位计数器，会在 `2^63` 次迭代之内发生，
并在燃料用完之前报告为 `Fault.ub`（见[可信基础第 2 项](../trusted-base.md#2-runtime-and-object-schema)）。

流目标，初始化、结束和复制目标，校验和与查询目标，以及整缓冲区目标，结论都是 `.ok`，不带关于终止的前提。
有两族需要这样的前提，因为 C 本身在那里可能不终止：

| 族 | 命题 | 原因 |
| --- | --- | --- |
| 读 gzip 文件：`gzread`、`gzfread`、`gzgetc`、`gzgetc_`、`gzgets`、`gzungetc`（`NeedsReadBound`） | 不带前提时：执行不以 `Fault.ub` 结束；它唯一可能的错误结局是燃料用完。带上前提 `ReadsFinite`（描述符还能交付的字节少于 `2^61`）时：执行是 `.ok`。 | 一个不断交付空 gzip 成员的数据源，会让 C 中的一次 `gzread` 永远运行下去。`2^61` 是模型的数字：它让各循环的度量保持在 `2^64` 以下。 |
| `inflateBack` | 带上 `protocol.inputBound < 2^48`（这次调用总共得到的输入少于 `2^48` 字节）时：执行是 `.ok`。 | `zlib.h` 没有限制 `in` 回调提供多少数据。 |

`ReadsFinite` 还说描述符编号不是负数。`gzopen` 只返回这样的句柄（写在 `GzOpenSafe` 中），
而 `gzdopen` 对负的描述符返回 `NULL`（`zlib/gzlib.c`）。

所以，已登记的安全目标恰好只容许一种错误结局：燃料用完，而且只出现在那六个 gzip 读取调用上，
只在不假设读取预算的时候。对这些调用，目标分成两半：在每个世界里都没有未定义行为、没有内存错误；
在该前提下终止。其他每个 gz 调用在每个世界里都终止。
这两个前提在[偏离记录](../deviations.md)中各有一行。

## 调用者义务 {#4-caller-obligations}

每个目标都明确写出它的前提。下表列出前提的种类；以 Lean 定义为准，
每个 [API 条目](api/README.md)的“证明目标”段落列出该函数的前提。
`zlib.h` 文档规定会被拒绝的值在定义域之内，得到一个干净的错误返回；它不是调用者的义务。

| 编号 | 义务或范围 | Lean 前提 |
| --- | --- | --- |
| A1 | **初始化。** 流指针是 `NULL`，或者指向一个 `z_stream`，其 `zalloc` 和 `zfree` 各自是 `NULL` 或默认分配器的函数。其他字段（包括 `state`）可以是任意值。版本指针是 `NULL` 或有一个可读字节。**之后的调用。** 流可达。`NULL` 流或不一致的流，由两个拒绝目标列出的那些函数拒绝，返回 `Z_STREAM_ERROR`（见[附录](#where-the-goals-are)）。拒绝什么也不改，只有一个例外：从被拒绝的源复制时，`dest->state` 被置为 `NULL`。 | `InitArguments`；`StreamReachable`；`RefusedInflate`、`RefusedDeflate` |
| A2 | 调用者提供这次调用要用的可读输入范围和可写输出范围。 | `StreamBuffers`、`CallerRange`、`Bytes`、`Writable` |
| A3 | 没有理由重叠的调用者区域互不重叠：输入、输出、字典、gzip 头记录及其缓冲区、长度单元。它们可以位于同一个对象中。`zlib.h` 并没有对每一对都这样规定；每个这样的前提在[偏离记录](../deviations.md)中都有一行。 | `Separate`、`ActiveHeader`、`UtilitySeparation` |
| A4 | 对同一个流的调用不并发。 | 模型是顺序的。 |
| A5 | 使用默认分配器。它的失败在范围之内：不论哪些 `malloc` 调用失败，每个目标都成立。带自定义 `zalloc` 或 `zfree` 的初始化调用，以及带有这种分配器的存活流，都在所有目标之外。带自定义分配器而 `state` 为 `NULL` 的记录，仍按 A1 被拒绝。 | `DefaultOrNull`、`DefAlloc` |
| A6 | 结束或关闭之后不再使用。新的一次初始化开始新的生命周期。 | 历史在 End 处结束；End 之后的记录属于拒绝的定义域。 |
| A7 | 每个标量值都有归类：正常使用、文档规定的拒绝，或者明确写出的调用者限制。从不为了回避错误路径而丢掉一个非法值。 | 目标对每个 `flush`、`level`、`windowBits` 等取值全称量化。 |
| A8 | 每个字节对象少于 `2^63` 字节。这是平台的事实，不是调用者的责任。 | `ByteObjectsFit`（见[平台](platform.md)） |

对初始化之后的调用，有三种记录在 A1 之外，既不可达，也不被拒绝
（见[偏离记录](../deviations.md)的“被拒绝的流”一行）：
`state` 字段里是一个垃圾地址的记录，例如从未初始化的 `z_stream`；
`state` 指向一个已释放状态的记录；
`state` 指向另一种状态的记录（把 deflate 状态传给 inflate 函数）。
在 C 中，这几种调用都会通过那个坏指针去读，这是未定义行为。

## 模型的限制 {#3-faults-undefined-behaviour-and-model-gaps}

**“模型不出故障”这样一条定理，单凭它自己并不能证明 C 没有未定义行为。**
模型能检测到大多数未定义行为，并抛出 `Fault.ub`。
本节列出它能检测什么、检测不到什么。主要的缺口是：两种空指针操作、未初始化的指针，以及对象布局和类型。
每一处都是结论的一条明确限制，也记录在[可信基础第 2 项](../trusted-base.md#2-runtime-and-object-schema)中。

### 各项义务

| 编号 | 义务 | 模型能检测到违规吗？ |
| --- | --- | --- |
| U1 | 不在对象之外读写 | 能。 |
| U2 | 指针运算停留在对象之内或其末尾后一位 | 能，`NULL + 0` 除外（见[下文](#null-pointers-and-pointer-differences)）。 |
| U3 | 不解引用空指针 | 能。 |
| U4 | 不在释放后使用，不重复释放 | 能。已释放的块编号从不复用，所以悬空指针会出故障。 |
| U5 | 不非法使用未初始化数据 | 整数：每条定理对每个取值都成立。指针：不能；证明用手工论证来说明（见[下文](#uninitialised-memory)）。 |
| U6 | 没有有符号溢出 | 能，前提是翻译在该处用了带检查的有符号运算。如果同一函数中前面的一个判断已把操作数限制在范围之内，翻译就用普通运算符（见[工作规则的“翻译”一节](../../AGENTS.md#translation)）；这时排除溢出的是那个判断，模型不作检查。 |
| U7 | 没有非法移位 | 能，靠翻译中带检查的移位运算。 |
| U8 | 不写只读对象 | 部分能：字节对象和静态表带有只读标志，其他对象没有。 |
| U9 | `memcpy` 的范围不重叠 | 能，对每次 `memcpy` 调用都检查。 |
| U10 | 访问遵守 C 的类型和对齐要求 | 不能。模型没有类型标签，没有对齐，也没有完整的 ABI 布局（见[下文](#object-representation)）。 |
| U11 | 每次调用都终止 | 能：`Fault.outOfFuel`。 |
| U12 | 没有内存泄漏 | 这不是故障。由每个目标的分配账本来陈述。 |

和 C 一样，无符号运算在翻译中回绕。U6 和 U7 的检查在翻译所用的运算里，
所以每一处是否用了正确的运算，属于对翻译的审查（见[可信基础第 3 项](../trusted-base.md)）。
U1 到 U10 是 C 的义务。U11 和 U12 增加了终止和资源两项；其中一项不成立并不是 C 的 UB。

### 空指针与指针差

**模型接受两种 C 未加定义的空指针操作：`NULL + 0`，以及只在 `compress` 的辅助函数中出现的 `NULL - NULL`。
一条“不出故障”的定理并不说明 C 避开了它们。**
[模型的限制](../model-limits.md#conditions-on-the-model-that-goals-state)中有“NULL 指针算术”一行。

| 操作 | 模型怎么做 | 关于 C 的结论还需要什么 |
| --- | --- | --- |
| 空指针加整数零 | `Ptr.add` 返回空指针，不出故障。 | 需要论证：按所选的 C 规则，每一处可达的使用都有定义。 |
| 空指针加非零整数 | `Ptr.add` 抛出 `Fault.ub`。 | 不需要：“不出故障”的定理已排除它。 |
| 空指针减空指针 | `Ptr.diff` 抛出 `Fault.ub`。`Zlib.Compress.ptrDiff` 则返回零。 | 对 `compress` 的辅助函数：需要论证这个 C 表达式有定义。 |
| 指向同一个存活数组的两个非 NULL 指针 | `Ptr.diff` 检查两个偏移，允许末尾后一位，并检查差值能放进有符号 64 位。 | 模型里的对象就是 C 的对象。 |
| 指向不同对象的指针，或悬空指针 | `Ptr.diff` 抛出 `Fault.ub`。 | 不需要：“不出故障”的定理已排除它。 |

定义见 [Ptr.add 和 Ptr.diff](../../ZlibF/Runtime/Ptr.lean) 以及[压缩器辅助函数](../../ZlibF/Zlib/compress.c.lean)。
这张表说的是指针值，不是 `NULL` 这个写法；`NULL` 也可以是一个整数常量。

这两种操作为什么没有定论：C11
（[N1570 第 6.5.6 节](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf)）和 C23 草案
（[N3096 第 6.5.6 节](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf)）
只对指向数组内部的指针定义了指针运算和指针减法，而空指针不指向任何数组元素。
[N3261](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3261.pdf) 提议在以后的修订中给这两种空指针操作下定义；
提案不是本项目 C 目标的规则。差分测试结果一致、sanitizer 没有报告，同样不能定论。
运行时里 `Ptr.diff` 的注释说 C23 把 `NULL - NULL` 定义为零；这条注释不准确，
它既不改变定义，也不改变 C 的规则。

### 未初始化内存

**整数是任意的。** 新分配的内存里的整数取自 `Heap.garbage`，定理对这个函数一无所知。
每个目标都对整个堆全称量化，所以它对每个这样的函数都成立：
没有哪个证明能依赖未初始化整数里的内容。

有一条限制：模型在一次执行中给每个单元固定一个值，所以对同一个单元的两次读取结果相同。
它没有刻画“每次读取都得到一个新的未指明的值”。证明不得用这种一致性来论证 C 的行为。
复制字节时，这些值也被原样复制。

这一点在两个地方有影响：`slide_hash` 会访问从未写过的 `prev` 表项，
`longest_match` 会比较真实输入之后的字节。对这些单元的每个取值，安全目标都成立：
`Goal.deflate_safety` 已登记，而且它对每个堆全称量化。
至于压缩输出不依赖这些值，那是一个功能性命题。安全性不需要它，本项目也不声称它成立。

**新分配内存中的指针在模型中是 NULL。这比 C 弱。** 模型的分配器造出的记录，每个指针字段都是 `NULL`
（[Runtime/Schema.lean](../../ZlibF/Runtime/Schema.lean) 中的 `ZStream.garbage` 及其同类）。
在 C 中，从未初始化内存读出的指针是不确定值，使用它是未定义的。
在模型中，同样的读取得到一个合法的空指针：与 `NULL` 比较、复制、`free(NULL)` 都会成功。
所以模型检测不到“某个指针字段漏写了”。

证明用手工论证补上这个缺口：对一次调用读取的每个指针字段，证明翻译中有一条更早的语句写过它。
两个初始化函数像 C 那样，显式地把新分配的状态记录清零。这并不会初始化调用者的记录或自动变量记录。
`compress` 内部的自动 `z_stream` 一开始有任意的整数字段和模型里为 NULL 的指针；它的字段像 C 中那样被写入。

### 对象表示

模型把每一类对象存在各自的表里，没有记录的字节级布局。由此带来的后果：

| C 有什么 | 模型有什么 | 对定理的后果 |
| --- | --- | --- |
| 有声明长度的数组 | 任意长度的 Lean 数组；C 的长度是另外的谓词（`WellFormed`、`Heap.RecordsWellFormed`、`Statics.WellFormed`）。 | 目标要么把这个谓词作为前提，要么证明它。常量表必须等于翻译出来的 C 表（`LibraryGlobals`）。 |
| 地址互不相同的分配 | 块编号。新块得到下一个未用的编号。`Fresh` 说从下一个编号起都没有被占用；`Uniq` 说一个编号只存一个对象。 | 同时具有这两条性质和库常量表的堆叫作**库堆**（[偏离记录](../deviations.md)称之为良构的堆）。它是对历史起点的堆、以及调用者每次交回的堆的前提。它是对模型的条件，不是 C 调用者的责任。 |
| 已初始化和未初始化的字节 | 没有初始化位。 | 见[未初始化内存](#uninitialised-memory)。 |
| `const` 对象 | 字节对象和静态表上有只读标志。记录和 16 位字数组没有。 | 对 `const` 记录的写入检测不到。 |
| 指针相等 | 对象相同且偏移相同时相等。指向不同对象的指针比较为不等。比较悬空指针不出故障。 | 证明不得依赖 C 不保证的结果，例如两个相邻对象交界处的相等。 |
| 地址与对齐 | 只有地址的低三位，而且只供 CRC 代码使用，它一次读八个字节。堆上的字节块从对齐的地址开始；静态的或内嵌的字节数组有一个任意但固定的余数。 | 校验和目标对每个余数都成立。其他证明都不得使用地址。 |
| 有效类型与别名规则 | 没有建模。读一个字是由字节拼出来的。 | 一个 C 强制转换是否遵守别名规则，在定理之外。 |

这些限制记录在[模型的限制](../model-limits.md#conditions-on-the-model-that-goals-state)的“堆的良构性”和“CRC 地址与字访问”两行，
以及[可信基础第 2 项](../trusted-base.md#2-runtime-and-object-schema)中。

## 安全性之外

- **功能正确性。** 输出字节是什么，调用返回哪个码。它不是安全结论所必需的；
  哪些功能结论在计划之内，见[进度，范围](../progress.md#scope)。
  功能目标在 `ZlibF/Spec/Functional/` 中；已经证明的仍保持已登记，
  安全证明所依赖的功能性事实在范围之内。
  预期的行为见[格式](format/README.md)和 [API 契约](api/README.md)。
- **其他配置。** 自定义分配器，以及默认 x86_64 Linux LP64 静态构建之外的每一种构建。
- **环境。** 编译器和操作系统的正确性、性能、栈深度，以及针对解压炸弹的限制。
  这些边界记录在[可信基础](../trusted-base.md)中。

畸形输入在安全性的定义域之内：错误返回不得掩盖故障。

## 附录：目标在哪里 {#where-the-goals-are}

每个安全目标都是一个 Lean 定义 `ZlibF.Spec.Public.Goal.<name>`。它位于 `ZlibF/Spec/Safety/`；
gzip 文件接口和回调解码器的目标位于 `ZlibF/Spec/Public/`。
`ZlibF/Spec/Public/` 还存放目标用到的定义。有两个例外和一点补充：

- `Goal.compressBound` 和 `Goal.compressBound_z` 在 `ZlibF/Spec/Functional/Queries.lean` 中（见下表中的那一行）。
- 不变量和一些 gz 前提是与证明放在一起定义的：`Good` 在 `ZlibF/Proof/inflate.c.base.lean`，
  `DGood` 在 `ZlibF/Proof/deflate.c.base.lean`，
  `GzInv`、`ReadsFinite` 和 `NeedsReadBound` 在 `ZlibF/Proof/gz.inv-model.lean`。

这两个目录中的模块都不得导入功能规格（`ZlibF/Spec/Functional/`）。
快速关卡运行 `scripts/check-spec-layers.py`，它会拒绝这样的导入。
脚本容许一处导入：`Public/GzState.lean` 从 `ZlibF/Spec/Api/Gz.lean` 导入 gz 模式解码器。
gz 和回调的功能目标（`Goal.gz_sequence`、`Goal.inflate_back_sequence`、各个 `Goal.gz*` 结果契约）
也在 `ZlibF/Spec/Public/` 中；它们不是必需的（见[拆分设计](../design/safety-functional-split.md)第 4 步）。

| 函数 | 安全目标 | 文件 |
| --- | --- | --- |
| `inflate`、`deflate` 以及对存活流的其他调用 | `Goal.<function>_safety`：在可达流上再做一次调用（见[调用与调用序列](#2-calls-and-sequences)） | [Safety/Streams.lean](../../ZlibF/Spec/Safety/Streams.lean) |
| `inflateEnd`、`deflateEnd` | `Goal.<function>_safety`：流释放它拥有的块 | [Safety/Streams.lean](../../ZlibF/Spec/Safety/Streams.lean) |
| `inflateInit_`、`inflateInit2_`、`deflateInit_`、`deflateInit2_` | `Goal.<function>_safety`：`zlib.h` 允许的每一次调用，包括流为 `NULL` 的情况 | [Safety/Initialisation.lean](../../ZlibF/Spec/Safety/Initialisation.lean) |
| `inflateCopy`、`deflateCopy` | `Goal.<function>_safety` | [Safety/Copy.lean](../../ZlibF/Spec/Safety/Copy.lean) |
| 每个 inflate 或 deflate 调用序列 | `Goal.inflate_sequence_safety`、`Goal.deflate_sequence_safety` | [Safety/Sequences.lean](../../ZlibF/Spec/Safety/Sequences.lean) |
| `NULL` 流或不一致的流 | `Goal.inflate_refusal`、`Goal.deflate_refusal`（各目标列出的函数；其余见[进度，无故障覆盖](../progress.md#no-fault-coverage-of-zlibh-functions)） | [Safety/Refusals.lean](../../ZlibF/Spec/Safety/Refusals.lean) |
| 校验和 | `Goal.<function>_safety`：调用返回，堆不变 | [Safety/Checksums.lean](../../ZlibF/Spec/Safety/Checksums.lean) |
| `zlibVersion`、`zlibCompileFlags` | `Goal.<function>_safety`：调用返回，堆不变 | [Safety/Queries.lean](../../ZlibF/Spec/Safety/Queries.lean) |
| `compress*`、`uncompress*` | `Goal.compress*_safety`、`Goal.uncompress*_safe` | [Safety/Utilities.lean](../../ZlibF/Spec/Safety/Utilities.lean) |
| `compressBound`、`compressBound_z` | `Goal.compressBound`、`Goal.compressBound_z`：完整契约。翻译是一个纯函数，不涉及堆，也不会出故障，所以单独的安全目标会按定义成立。 | [Functional/Queries.lean](../../ZlibF/Spec/Functional/Queries.lean) |
| gzip 文件接口 | `Goal.gz_sequence_safety`；`NULL` 句柄：`Goal.gz_refusal` | [Public/GzSafety.lean](../../ZlibF/Spec/Public/GzSafety.lean)、[Public/GzRefusal.lean](../../ZlibF/Spec/Public/GzRefusal.lean) |
| `inflateBackInit_`、`inflateBack`、`inflateBackEnd` | `Goal.inflate_back_sequence_safety` | [Public/Sequences.lean](../../ZlibF/Spec/Public/Sequences.lean) |
| 非空性 | `Goal.inflate_initialisation_domain`、`Goal.deflate_initialisation_domain`、`Goal.inflate_back_initialisation_domain`、`Goal.gz_sequence_nonvacuity` | [Safety/Domains.lean](../../ZlibF/Spec/Safety/Domains.lean)、[Public/Domains.lean](../../ZlibF/Spec/Public/Domains.lean)、[Public/GzSafety.lean](../../ZlibF/Spec/Public/GzSafety.lean) |

`tests/audit/public-api.json` 是审计所用的清单。它为每个函数给出一个 `safety_goal` 和一个 `functional_goal`。
必需集合是每个 `safety_goal`、`safety_goals` 列表和 `nonvacuity_goals` 列表。
`open_safety` 列表列出还没有已登记定理的必需目标；它是空的。
`zlib.h` 在“undocumented functions”（未文档化的函数）注释之下声明的函数没有必需目标。

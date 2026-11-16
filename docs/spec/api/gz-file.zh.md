<!-- source-sha256: fa054fd0dc4fbf26429d804a27f2a35f812350db9335bd66e9ed405fcdd51d6f -->

# Gzip 文件

[API 手册](README.md) · [契约约定](contracts.md) · [流式压缩](deflate-stream.md) · [流式解压](inflate-stream.md)

使用 `gzFile` 句柄进行带缓冲的 gzip 文件 I/O。打开时取得文件描述符和私有状态；
数据操作按需初始化缓冲区和编解码器状态；即使最终 I/O 失败，关闭也会释放句柄。
读取还可接受透明的未压缩输入：文件中的字节不经解压，直接作为结果交付。

| 任务 | 入口 |
| --- | --- |
| 打开或配置 | [打开路径](#gzopen)、[打开描述符](#gzdopen)、[缓冲区大小](#gzbuffer)、[压缩参数](#gzsetparams) |
| 读取 | [字节](#gzread)、[数据项](#gzfread)、[字符](#gzgetc)、[回退字节](#gzungetc)、[行](#gzgets) |
| 写入 | [字节](#gzwrite)、[数据项](#gzfwrite)、[字符](#gzputc)、[字符串](#gzputs)、[格式化文本](#gzprintf)、[刷新](#gzflush) |
| 位置 | [定位](#gzseek64)、[回到起点](#gzrewind)、[未压缩位置](#gztell64)、[文件偏移](#gzoffset64) |
| 查询或清除状态 | [文件末尾](#gzeof)、[透明模式](#gzdirect)、[错误](#gzerror)、[清除错误](#gzclearerr) |
| 关闭 | [任意模式](#gzclose)、[读取句柄](#gzclose_r)、[写入句柄](#gzclose_w) |

本页的契约依据固定版本的源码（加上列出的补丁）和 `zlib.h`。

**已证明的内容。** 句柄每一段历史的安全性：没有未定义行为、没有内存错误、没有泄漏，并且终止（见[安全目标](#the-safety-goal)）。
各条目描述的返回值、字节和位置属于功能行为：它们读自 C 源码，凡是没有定理陈述的，都**尚未由证明确认**。
它们不在计划的证明目标之内。哪些目标已完成见[进度](../../progress.md)。

## 安全目标

本页中默认构建所编译的每个函数，都有自己的必需安全目标 `Goal.<function>_safety`
（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)），它的条目在**证明目标**下陈述这个目标。
`gzopen_w` 只存在于 Windows 上，没有这样的目标。
每个这样的目标都把序列目标 `Goal.gz_sequence_safety`
（[GzSafety.lean](../../../ZlibF/Spec/Safety/GzSafety.lean)）的一个子句限制到一个函数的调用上。
接受句柄的函数，其目标还带有 `Goal.gz_refusal` 中属于该函数的子句，即对 NULL 句柄的拒绝。
序列目标同样是必需的。它多出下表中的不变量子句，这个子句说的是历史，而不是某一次调用。

本节描述序列目标，因为各条目要引用它的历史、参数条件和读取预算。这些目标各有一条类型完全相同的定理。
它们针对打过补丁的源码（见[注意事项](#scope-and-source-caveats)）。

**历史（`GzHistory`）。** 目标覆盖一个句柄的每一段历史。历史从一次成功的 `gzopen`、`gzopen64` 或 `gzdopen` 开始：
堆良构，字节对象都小于 `2^63` 字节，字符串参数（`path`、`mode`）以 NUL 结尾。此后可以接着发生以下任何一种情况：

- 对该句柄调用一个非关闭的 gz 函数，参数满足下表的条件，并且调用返回，结果不限；
- 使用一次 `gzgetc()` 宏；
- 调用者编辑：对不归句柄所有的存储作任意修改。调用者可以释放自己的缓冲区，包括上一次 `gzread` 用的缓冲区；
- 外部世界的一步：文件系统变成任意一个良构状态。别人可以关闭句柄的描述符，或者用同一个编号打开另一个文件。
  下一次读写要么得到错误，要么读写到那个文件，与 C 中一样。

**目标陈述的内容。**

| 子句 | 命题 |
| --- | --- |
| 不变量 | 每段历史之后，世界良构，句柄满足其不变量（`GzInv`）。 |
| 无故障 | 下一次调用在每个世界里都不会以未定义行为或内存错误结束。它唯一可能的错误是循环燃料耗尽。除参数条件外没有前提。 |
| 终止 | 下一次调用返回。`gzread`、`gzfread`、`gzgetc`、`gzgetc_`、`gzgets` 和 `gzungetc` 为此需要下面的读取预算。其他调用在每个世界里都返回。 |
| 帧性质与账本 | 返回的调用保持打开的描述符集合不变，保持 `GzInv`、模式和描述符，只写句柄自有的块和下面点名的调用者区域，并且存活块的变化与句柄的账本完全一致（`GzStepPost`）。 |
| `gzerror` | 它返回的指针在调用后的堆里是一个可读的、以 NUL 结尾的字符串。在 C 中它是字面量或句柄的消息；目标只陈述它是一个可读的字符串。 |
| 关闭 | `gzclose`、`gzclose_r` 和 `gzclose_w` 在每个世界里都返回。模式不符的关闭调用拒绝，并且什么都不改变。否则句柄记录和每个自有块都被释放，其余内容不变，描述符被释放，即使系统的 `close` 失败也是如此。对返回码不作陈述。 |
| 打开 | `gzopen`、`gzopen64` 和 `gzdopen` 对每个世界和每一种分配结果都返回，并且不改变任何已有的块。返回 NULL 时不留下新块；`gzopen` 和 `gzopen64` 此时还保持打开的描述符集合不变。返回的句柄满足 `GzInv`，恰好拥有新块。`gzdopen` 不打开也不关闭任何描述符。 |

**参数条件（`GzArguments`）。** 调用者的范围必须在句柄拥有的块之外（`GzOwned`：句柄记录、路径、消息、缓冲区和编解码器状态）。
`gzerror` 返回的字符串就是句柄的消息。清除错误的条目在使用自己的缓冲区之前会先释放这条消息：写入类条目在每次通过模式和错误检查的调用中都这样做，读取类条目只在上一次读取停顿之后才这样做
（见[偏离记录中的表](../../deviations.md#why-the-handles-own-strings-are-excluded)）。这时把它再传回来，在 C 中可能是释放后使用
（见[偏离记录](../../deviations.md)的“Gz 调用者缓冲区”和“Gz printf 字符串”两行）。

| 调用 | 条件 |
| --- | --- |
| `gzread(file, buf, len)` | `len > INT_MAX`：无。否则 `len == 0`，或者 `buf` 覆盖 `len` 个可写字节且在句柄的块之外。 |
| `gzwrite(file, buf, len)` | `len > INT_MAX`：无。否则 `len == 0`，或者 `buf` 覆盖 `len` 个可读字节且在句柄的块之外。 |
| `gzfread`、`gzfwrite` | `size * nitems >= 2^64`：无。否则乘积为零，或者 `buf` 覆盖这么多字节（`gzfread` 要求可写，`gzfwrite` 要求可读）且在句柄的块之外。 |
| `gzgets(file, buf, len)` | `buf == NULL` 或 `len < 1`：无。否则 `buf` 覆盖 `len` 个可写字节且在句柄的块之外。 |
| `gzputs(file, s)` | `s` 是以 NUL 结尾的字符串，且在句柄的块之外。 |
| `gzprintf`、`gzvprintf` | 格式串是以 NUL 结尾的字符串，并且模型的格式化器能用这些参数对它求值（`Formatted`）。格式串和每个字符串参数都在句柄的块之外。 |
| `gzerror(file, errnum)` | `errnum` 为 NULL，或覆盖 4 个可写字节且在句柄的块之外。 |
| 其他调用 | 无：每个标量参数的每个取值都被覆盖。 |

`gzprintf` 的条件在每个 `gzprintf` 步骤上都要求成立，包括读句柄和处于错误状态的句柄，尽管那时 C 并不读格式串。
格式化器覆盖整数、字符和字符串转换。浮点转换、`%p`、`%n`、`h` 和 `hh` 修饰符以及 `*` 宽度不在定义域之内
（见[偏离记录](../../deviations.md)的“格式化”一行）。

**读取预算（`ReadsFinite`）。** 六个读调用的终止子句假设：句柄的描述符还能交付的字节少于 `2^61`。
这个前提是必要的：一个不断交付空 gzip 成员的数据源，会让 C 中的一次 `gzread` 永远运行。
它按调用名取用，所以即使 C 会立刻返回（例如在写句柄上，或长度为零）也要求成立。
`2^61` 是模型的数字，不是 zlib 的：它让循环度量保持在 `2^64` 次迭代的循环燃料以下
（见[安全性](../safety.md#2-calls-and-sequences)）。这个前提还说描述符编号不是负数（`HasBudget`）；库返回的每个句柄都有这样的编号，因为 `gzdopen` 对负的描述符返回 `NULL`。
无故障子句以及帧性质与账本子句不使用这个前提。

**`gzgetc` 宏。** `zlib.h` 把 `gzgetc` 定义成宏，应用程序通常就是这样调用它的。目标里另有一条针对这个宏
（`Zlib.ZlibH.gzgetc`）。有缓冲输出（`have != 0`）时，宏直接从缓冲区取一个字节，不调用库函数，不需要前提就返回。
`have == 0` 时它调用函数 `gzgetc`，在读取预算下返回。它的帧性质和账本与函数相同，而函数不写任何调用者区域。
对 NULL 句柄使用宏会读取 `file->have`，在 C 中是未定义行为；只有函数才拒绝 NULL。

**长度为零的读不点名任何区域。** 对 `len == 0` 的 `gzread` 和乘积为零的 `gzfread`，帧性质不点名任何调用者区域
（`GzWriteRegions`），`buf` 可以是任意指针，包括指向这次调用所释放的块的指针。如果帧性质点名了 `buf`，它在那种情形下就是假的。
`len >= 1` 时 `gzgets` 点名 `buf` 处的 `len` 个字节，
`gzerror` 点名 `errnum` 处的 4 个字节。

**NULL 句柄与非空性。** `Goal.gz_refusal`
（[GzRefusal.lean](../../../ZlibF/Spec/Safety/GzRefusal.lean)）说明：每个接受句柄的 gz 函数在句柄为 NULL 时返回文档规定的值，
堆和世界都不变。每个这样的函数自己的目标都重复了属于它的那个子句。`Goal.gz_sequence_nonvacuity` 表明前提可以满足：一个带有限读取预算的 `gzopen` 读句柄加一次一字节的
`gzread`，以及一个 `gzdopen` 写句柄加一次一字节的 `gzwrite`。

**功能契约。** 逐函数目标 `Goal.gzread`、`Goal.gzwrite` 等说明读写了哪些字节、返回了什么值。
它们针对没有外部干扰的普通文件（`RegularOs`），并依赖一个手工建立的文件系统模型。
它们不在计划内。每个条目说明它的功能目标是否已有定理证明。

## 通用句柄条件

先分清两种位置。**逻辑位置**以未压缩字节计数；普通读写按已消费或接受的数量推进，定位还可以登记尚未执行的前移。底层文件另有**物理偏移**，它以文件中的字节计数。`gztell` 查询前者，`gzoffset` 查询后者。库会预读和缓冲，因此两个值通常不同；单次压缩率也不能用来换算它们。

例如，没有额外定位或字节回退时，读取句柄已向应用交付 1000 个解压字节，逻辑位置就是 1000；为了完成这些输出，底层可能已预读更靠后的压缩字节。相反，写入成功表示库接受了输入，不能据此推断这些字节已全部写入描述符。

后面的参数沿用这套单位：`len` 和缓冲区配置 `size` 按字节计；数据项接口中的 `size` 是每项字节数，`nitems` 是项数，总请求为 `size * nitems` 字节。`offset` 是有符号的未压缩字节位移；`whence` 指定从起点（`SEEK_SET`）还是当前位置（`SEEK_CUR`）计算。`INT_MAX` 是本构建中有符号 `int` 能表示的最大值，即 `2^31 - 1`。

本页把可直接重试的非阻塞停顿与其他已记录的“硬错误”分开描述。这个区别说明本次调用怎样返回；它不免除错误后的状态、重试和清理要求。

本页使用默认 x86_64 Linux 构建。`int` 和 `unsigned` 为 32 位。
`long`、`z_off_t`、`z_off64_t` 和 `z_size_t` 为 64 位。大文件声明已启用。
这里普通入口和 `*64` 入口的偏移范围相同。其他配置需要单独契约。
`gzopen_w` 仅适用于 Windows，下文另行限定其范围。

**受限定义域**指满足下列通用要求的普通用法：

- 非 NULL 句柄由成功打开返回、仍存活且尚未关闭。串行使用它，调用者不修改其私有状态。
- 读取或写入句柄具有入口指定的访问模式。NULL 和错误模式的拒绝情形分别说明。
  已失效或任意指针不在本定义域内；检查模式字段不等于验证指针。
- 缓冲区覆盖请求的可读或可写范围，并与句柄拥有的内存分离。
  字符串具有可读的终止 NUL。调用者保留这些对象的所有权。
- 位置运算和请求范围能由指定 C 类型表示。下述契约仍包括显式的超大请求和乘法溢出拒绝。
- 描述符在关闭前属于句柄。调用期间，没有其他操作改变其数据或位置。
  操作系统失败和分配失败仍可能发生；成功打开不保证后续 I/O 成功。
  前两句只是功能契约的条件。安全目标允许外部世界在两次调用之间改变任何描述符。

每个入口均带定义域标签。“完整标量范围”仅在上述指针和生存期要求下，
适用于所指明的标量参数。文档中的限制不免除已知失败路径的义务。
特别地，部分读取错误和字节回退形成的负位置都在安全目标之内。

**效果。** 读、写、打开、定位、控制和关闭均为有状态操作，包括没有调用者输出缓冲区的操作。
位置查询（`gztell`、`gzoffset`）和文件末尾查询（`gzeof`）读取状态；`gzerror` 还可能写入可选错误码输出。
`gzdirect` 可读取文件并分配内存，因此也是有状态操作。

```mermaid
stateDiagram-v2
    state "新建句柄" as Fresh
    state "已开始数据处理" as Active
    state "已关闭" as Closed
    [*] --> Fresh: 成功打开
    Fresh --> Active: 首次 I/O 或格式检查
    Active --> Active: 读、写、定位、控制
    Fresh --> Closed: 关闭
    Active --> Closed: 关闭，包括最终 I/O 失败
    Closed --> [*]
```

**格式与缓冲。** 打开时不对载荷执行 I/O。缓冲区和编解码器状态按需分配，
默认请求的缓冲区大小为 8192 字节。请求大小是配置量，实际内部存储还包括下述双倍缓冲区和编解码器状态。首次使用或后续解压期间都可能分配失败。
即使最终 I/O 失败，关闭也释放拥有的分配。

普通读取句柄根据合理的四字节头部识别 gzip；否则原样返回输入。
空输入属于透明输入。非阻塞输入在获得四字节前停顿时，检测保持等待。
一个 gzip 成员是一段带有自身头部、压缩数据和尾部校验信息的完整流；一个文件可以顺序放置多个成员。读取输出按顺序拼接各成员的未压缩数据。若尝试解码下一个成员时，在格式错误前未产生输出，
则忽略尾随的非成员数据。`G` 要求 gzip；`T` 选择透明输出，不能用于读取。

**读取结果。** 读取按已消费字节数推进未压缩位置，包括最终的部分数据项。
已缓冲字节可能在已记录错误被报告之前返回。`gzeof` 表示曾尝试读取可用数据之后的内容，
而不只是已交付最后一个字节。`gzerror` 区分 EOF、损坏（`Z_DATA_ERROR`）、
截断（`Z_BUF_ERROR`）、分配失败（`Z_MEM_ERROR`）和系统失败（`Z_ERRNO`）。
零长度读取不消费输入，也不执行待处理定位。

**写入结果。** 成功表示句柄已接受输入；数据仍可能在缓冲区内。
后续刷新或关闭仍可能失败。硬错误可能在消费一个前缀后返回失败；
仅凭返回值不总能确定重试偏移。非阻塞停顿则可能返回至今已消费的数量。

错误通常持续到被清除。已记录的非阻塞停顿允许下次数据 I/O 重试。
定位和回到起点仍拒绝该已记录的 `Z_ERRNO`。构造错误消息本身可能失败，
并将错误码改为 `Z_MEM_ERROR`。`errno` 只对关联的系统失败有意义，
不能普遍解释每个失败的 API 调用。

源码为 [gzlib.c](../../../zlib/gzlib.c)、[gzread.c](../../../zlib/gzread.c)、
[gzwrite.c](../../../zlib/gzwrite.c)、[gzclose.c](../../../zlib/gzclose.c) 和
[zlib.h](../../../zlib/zlib.h)。序列安全目标是 `Goal.gz_sequence_safety`
（[GzSafety](../../../ZlibF/Spec/Safety/GzSafety.lean)），各函数的安全目标是
`Goal.<function>_safety`（[GzCalls](../../../ZlibF/Spec/Safety/GzCalls.lean)），
NULL 句柄目标是 `Goal.gz_refusal`（[GzRefusal](../../../ZlibF/Spec/Safety/GzRefusal.lean)）。
抽象契约是定义在抽象句柄 `GzHandle` 上的关系
（[Functional/Api/Gz.lean](../../../ZlibF/Spec/Functional/Api/Gz.lean)）。
功能目标是 `Goal.<function>`
（[GzOpen](../../../ZlibF/Spec/Functional/GzOpen.lean)、
[GzRead](../../../ZlibF/Spec/Functional/GzRead.lean)、[GzWrite](../../../ZlibF/Spec/Functional/GzWrite.lean)、
[GzControl](../../../ZlibF/Spec/Functional/GzControl.lean)、
[GzClose](../../../ZlibF/Spec/Functional/GzClose.lean)）。

## gzopen

打开路径，用于读取、写入或追加。

```c
gzFile ZEXPORT gzopen(const char *path, const char *mode);
```

### 返回值与后续调用 {#api-gzopen-returns}

**返回值类型。** `gzFile` — 拥有资源的句柄或失败标记

返回值说明打开操作是否取得新的 gzip 文件句柄。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `file != NULL`<br>**已取得句柄** | 模式解析、状态／路径分配和文件打开成功。位置为零，错误已清除，I/O 缓冲区尚未分配。 | 按所选模式使用句柄，并且只关闭一次。检查后续 I/O 及关闭结果。 |
| `NULL`<br>**未取得句柄** | 路径或模式为 NULL、模式无效、分配失败，或操作系统无法打开文件。 | 没有可关闭或查询的句柄。解决原因后再打开；errno 仅解释相关的操作系统打开失败。 |

**判读要点。**

- 打开不进行载荷 I/O，也不验证输入格式；缓冲区和编解码器延迟初始化。

### 调用条件与效果 {#api-gzopen-contract}

**定义域：** 受限定义域：字符串和文件环境；模式解析包括无效字符串。
**效果：** 有状态打开并取得所有权。

**前置条件：** 非 NULL 的 `path` 和 `mode` 是可读、以 NUL 结尾的字符串。

**证明目标。**

- **目标。** `Goal.gzopen_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzopen_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。它的命题是 `GzOpenSafe`（[Safety/GzSafety.lean](../../../ZlibF/Spec/Safety/GzSafety.lean)），即[序列目标](#the-safety-goal)中针对这个函数的打开子句。
- **适用条件**（`GzOpenSafe`）：
    1. 堆是库堆（`Fresh`、`Uniq`、`LibraryGlobals`）；
    2. 平台大小上界成立（`ByteObjectsFit`）；
    3. 世界是良构的文件系统（`FileSystem`）；
    4. `path` 为 NULL，或是以 NUL 结尾的字符串；`mode` 也是如此（`CString`）。
- **无条件覆盖。** `path` 或 `mode` 为 NULL；每一个路径和每一种模式文本，无论是否合法；每个文件系统世界，包括系统的 `open` 的每一种失败；每一种分配结果。
- **保证。**
    - *返回。* 调用返回，结果是 NULL 或一个句柄。
    - *状态。* 世界良构。返回 NULL 时，打开的描述符集合不变（`FdsKept`）。返回的句柄满足其不变量（`GzInv`）；它的描述符编号不是负数，并且在调用前没有打开；其他每个描述符是否打开都与调用前相同。
    - *写入。* 调用前已有的块都不改变（`Frame`）。
    - *分配。* 返回 NULL 时，已分配的块与调用前相同：失败的打开不留下任何东西。返回句柄时，新块恰好是句柄自己的块，并且不释放任何块（`LiveChange`）。
- **不在本目标内。** `path` 或 `mode` 在其所在对象之内没有以 NUL 结尾：在本目标之外，与 C 中一样。哪些调用返回句柄，以及该句柄的模式、位置和缓冲区：功能目标 `Goal.gzopen`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzopen"><summary>完整返回条件与边界</summary>

**后置条件：** 非 NULL 结果拥有描述符、状态和复制的路径。
未压缩位置为零，无错误，缓冲区尚未分配。
读取时保存初始描述符位置，供回到起点使用。
写入会创建或截断；追加保留现有数据，并在写入时增加一个新成员。

**错误与边缘情形：** NULL 参数、分配失败、无效模式或操作系统打开失败返回 NULL。
打开失败不遗留拥有的分配或描述符。只有系统打开失败保证关联的 `errno`。

最后一个 `r`／`w`／`a`、级别数字和策略字母生效。拒绝 `+`；没有访问字母也拒绝。
数字 `0`–`9` 选择级别，`f`、`h`、`R`、`F` 选择策略。
最后一个 `G`／`T` 生效：读取配合 `T`、写入配合 `G` 均被拒绝。
忽略 `b` 和未知字母。`e`、`x`、`N` 分别请求执行时关闭、独占创建和非阻塞模式
（在支持的平台上）；`x` 对读取无效果。打开不验证文件格式，也不分配 I/O 缓冲区。

</details>

## gzopen64

通过大文件入口打开。

```c
gzFile ZEXPORT gzopen64(const char *path, const char *mode);
```

### 返回值与后续调用 {#api-gzopen64-returns}

**返回值类型。** `gzFile` — 拥有资源的句柄或失败标记

返回值说明打开操作是否取得新的 gzip 文件句柄。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `file != NULL`<br>**已取得句柄** | 模式解析、状态／路径分配和文件打开成功。位置为零，错误已清除，I/O 缓冲区尚未分配。 | 按所选模式使用句柄，并且只关闭一次。检查后续 I/O 及关闭结果。 |
| `NULL`<br>**未取得句柄** | 路径或模式为 NULL、模式无效、分配失败，或操作系统无法打开文件。 | 没有可关闭或查询的句柄。解决原因后再打开；errno 仅解释相关的操作系统打开失败。 |

**判读要点。**

- 打开不进行载荷 I/O，也不验证输入格式；缓冲区和编解码器延迟初始化。
- 在默认 LP64 构建中，gzopen64 与 gzopen 的实现和偏移范围相同；其他构建可能按条件提供其声明。

### 调用条件与效果 {#api-gzopen64-contract}

**定义域：** 与 `gzopen` 相同的受限定义域。**效果：** 有状态打开。

**前置条件：** 满足 `gzopen` 的字符串和环境要求。

**证明目标。**

- **目标。** `Goal.gzopen64_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzopen64_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。它的命题是 `GzOpenSafe`（[Safety/GzSafety.lean](../../../ZlibF/Spec/Safety/GzSafety.lean)），即[序列目标](#the-safety-goal)中针对这个函数的打开子句。
- **适用条件**（`GzOpenSafe`）：
    1. 堆是库堆（`Fresh`、`Uniq`、`LibraryGlobals`）；
    2. 平台大小上界成立（`ByteObjectsFit`）；
    3. 世界是良构的文件系统（`FileSystem`）；
    4. `path` 为 NULL，或是以 NUL 结尾的字符串；`mode` 也是如此（`CString`）。
- **无条件覆盖。** `path` 或 `mode` 为 NULL；每一个路径和每一种模式文本，无论是否合法；每个文件系统世界，包括系统的 `open` 的每一种失败；每一种分配结果。
- **保证。**
    - *返回。* 调用返回，结果是 NULL 或一个句柄。
    - *状态。* 世界良构。返回 NULL 时，打开的描述符集合不变（`FdsKept`）。返回的句柄满足其不变量（`GzInv`）；它的描述符编号不是负数，并且在调用前没有打开；其他每个描述符是否打开都与调用前相同。
    - *写入。* 调用前已有的块都不改变（`Frame`）。
    - *分配。* 返回 NULL 时，已分配的块与调用前相同：失败的打开不留下任何东西。返回句柄时，新块恰好是句柄自己的块，并且不释放任何块（`LiveChange`）。
- **不在本目标内。** `path` 或 `mode` 在其所在对象之内没有以 NUL 结尾：在本目标之外，与 C 中一样。哪些调用返回句柄，以及该句柄的模式、位置和缓冲区：功能目标 `Goal.gzopen64`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzopen64"><summary>完整返回条件与边界</summary>

**后置条件：** 适用 `gzopen` 契约，包括所有权、延迟分配和初始位置。
在此构建中，其实现和偏移范围均相同。

**错误与边缘情形：** 适用相同的 NULL、无效模式、分配和系统失败情形。
若构建的公开头文件对它设置条件，此名称需要相应的大文件声明。

</details>

## gzdopen

包装已有描述符，不打开或复制它。

```c
gzFile ZEXPORT gzdopen(int fd, const char *mode);
```

### 返回值与后续调用 {#api-gzdopen-returns}

**返回值类型。** `gzFile` — 拥有资源的句柄或失败标记

返回值说明现有描述符是否已转交给新句柄。此操作不复制描述符。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `file != NULL`<br>**描述符已转交** | fd 非负，句柄／诊断路径分配与模式解析成功。新的逻辑位置为零，即使描述符位置不为零。 | 让句柄独占 fd，直至关闭时关闭 fd。若原描述符须保持打开，应传入副本。 |
| `NULL`<br>**描述符仍归调用者** | fd 为负、mode 为 NULL 或无效，或分配失败。 | 没有可关闭的句柄。传入的描述符仍归调用者管理。 |

**判读要点。**

- 非负但已关闭或访问模式不符的描述符可能通过此入口，之后 I/O 才失败；非 NULL 不代表 fd 已获验证。
- 追加模式尝试定位到末尾。e／N 尝试更改标志但不报告其系统调用失败；x 不创建或截断现有描述符。

### 调用条件与效果 {#api-gzdopen-contract}

**定义域：** 受限定义域：描述符使用；包括负描述符的拒绝。

**效果：** 有状态所有权转移，并可能修改描述符标志。

**前置条件：** 普通成功情形中，`fd` 已打开，且访问权限与模式匹配。
非 NULL 的 `mode` 满足 `gzopen` 的字符串要求。
句柄拥有该描述符期间，其他使用者不对它读、写、定位或关闭。

**证明目标。**

- **目标。** `Goal.gzdopen_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzdopen_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。它的命题是 `GzDopenSafe`（[Safety/GzSafety.lean](../../../ZlibF/Spec/Safety/GzSafety.lean)），即[序列目标](#the-safety-goal)中针对这个函数的打开子句。
- **适用条件**（`GzDopenSafe`）：
    1. 堆是库堆（`Fresh`、`Uniq`、`LibraryGlobals`）；
    2. 平台大小上界成立（`ByteObjectsFit`）；
    3. 世界是良构的文件系统（`FileSystem`）；
    4. `mode` 为 NULL，或是以 NUL 结尾的字符串（`CString`）。
- **无条件覆盖。** `fd` 的每个取值：无论是否打开，无论是否为负；`mode` 为 NULL；每一种模式文本，无论是否合法；每个文件系统世界；每一种分配结果。
- **保证。**
    - *返回。* 调用返回，结果是 NULL 或一个句柄。
    - *状态。* 世界良构，打开的描述符集合不变（`FdsKept`）：调用不打开也不关闭任何描述符。返回的句柄满足其不变量（`GzInv`），它的描述符是 `fd`。
    - *写入。* 调用前已有的块都不改变（`Frame`）。
    - *分配。* 返回 NULL 时，已分配的块与调用前相同：失败的打开不留下任何东西。返回句柄时，新块恰好是句柄自己的块，并且不释放任何块（`LiveChange`）。
- **不在本目标内。** `mode` 在其所在对象之内没有以 NUL 结尾：在本目标之外，与 C 中一样。哪些调用返回句柄，以及该句柄的模式、位置和缓冲区：功能目标 `Goal.gzdopen`（不在计划内；已有定理证明它）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzdopen"><summary>完整返回条件与边界</summary>

**后置条件：** 成功时创建与 `gzopen` 相同的新状态，错误名称形式为 `<fd:N>`。
即使 `fd` 本身不在零位置，未压缩位置也从零开始。关闭会关闭 `fd`。
若原描述符必须保持打开，应传入复制得到的描述符。

**错误与边缘情形：** 负 `fd`、无效／NULL 模式或分配失败返回 NULL，
描述符所有权仍归调用者。非负但已关闭或权限错误的描述符，不保证在此时被拒绝；
后续 I/O 可能失败。`x` 不会独占创建或截断已有描述符。
追加会尝试定位到末尾。`e`／`N` 尝试改变描述符标志；本入口不报告这些系统调用的失败。

</details>

## gzopen_w

打开 Windows 宽字符路径。

```c
gzFile ZEXPORT gzopen_w(const wchar_t *path, const char *mode);
```

### 返回值与后续调用 {#api-gzopen_w-returns}

**返回值类型。** `gzFile` — 拥有资源的句柄或失败标记

返回值说明打开操作是否取得新的 gzip 文件句柄。此入口仅适用于 Windows WIDECHAR 构建。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `file != NULL`<br>**已取得句柄** | 模式解析、状态／路径分配和文件打开成功。位置为零，错误已清除，I/O 缓冲区尚未分配。 | 按所选模式使用句柄，并且只关闭一次。检查后续 I/O 及关闭结果。 |
| `NULL`<br>**未取得句柄** | 路径或模式为 NULL、模式无效、分配失败，或操作系统无法打开文件。 | 没有可关闭或查询的句柄。解决原因后再打开；errno 仅解释相关的操作系统打开失败。 |

**判读要点。**

- 打开不进行载荷 I/O，也不验证输入格式；缓冲区和编解码器延迟初始化。
- 诊断路径使用当前多字节区域设置；无法表示的宽字符名称可能留下空诊断名。

### 调用条件与效果 {#api-gzopen_w-contract}

**定义域：** 受限定义域：仅限 Windows `WIDECHAR` 构建，不属于默认构建。

**效果：** 有状态打开。

**前置条件：** 非 NULL 的 `path` 是可读且有终止符的宽字符串。
非 NULL 的 `mode` 满足 `gzopen` 的模式要求。Windows 文件环境可用。

**证明目标。** 没有目标：这个入口只属于 Windows 构建，不在默认构建之内。

<details markdown="1" class="ar-return-exact" data-return-exact="gzopen_w"><summary>完整返回条件与边界</summary>

**后置条件：** 适用 `gzopen` 的生存期、缓冲和模式契约，使用宽路径打开。
诊断路径转换为当前多字节区域设置；无法表示的名称可能成为空诊断名称。

**错误与边缘情形：** NULL、无效模式、分配和文件打开失败返回 NULL。
Windows 和区域设置方面的细节另行处理，**尚未由证明确认**；Linux 的翻译和公开目标并不确立这个变体的行为。

</details>

## gzbuffer

在缓冲区存在前选择请求大小。

```c
int ZEXPORT gzbuffer(gzFile file, unsigned size);
```

### 返回值与后续调用 {#api-gzbuffer-returns}

**返回值类型。** `int` — 零／负一控制结果

返回值报告是否记录了后续缓冲区大小请求。本次调用不分配缓冲区。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `0`<br>**已记录请求** | 句柄为读取或写入句柄，缓冲区尚未分配，且 size < 2^31。记录的请求为 max(size, 8)。 | 可继续 I/O 或检查；后续缓冲区分配仍可能失败。 |
| `-1`<br>**请求未改变** | 句柄为 NULL 或模式错误、缓冲区已存在，或 size >= 2^31。 | 若因大小被拒绝，在分配前选择更小的大小。若缓冲区已存在，此调用无法调整该句柄的大小。 |

**判读要点。**

- 应在 gzdirect、字节回退和普通 I/O 前调用；这些操作都可能分配缓冲区。

### 调用条件与效果 {#api-gzbuffer-contract}

**定义域：** 受限定义域：活跃句柄；完整无符号 `size` 范围。

**效果：** 有状态缓冲配置，不分配缓冲区。

**前置条件：** 活跃读取或写入句柄满足通用要求。

**证明目标。**

- **目标。** `Goal.gzbuffer_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzbuffer_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求（这个调用没有参数条件）：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）。
- **无条件覆盖。** `size` 的每个取值；历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界。
- **保证。**
    - *返回。* 句柄为 NULL 时，不论其他参数取什么值，调用都返回 `-1`。对句柄调用时，调用在每个世界里都返回。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。
    - *写入。* 句柄为 NULL 时不写任何内容：堆不变。这个函数的翻译不接受世界，所以无从改变世界。对句柄调用时，只写句柄自己的块。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 对句柄调用时的返回值，以及由此得到的字节、位置和标志：功能目标 `Goal.gzbuffer`（不在计划内；已有定理证明它）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzbuffer"><summary>完整返回条件与边界</summary>

**后置条件：** 缓冲区尚未分配且 `size < 2^31` 时，返回 0，记录 `max(size, 8)`。
读取句柄后续需要输入缓冲区及双倍大小的输出缓冲区；
写入句柄需要双倍大小的输入缓冲区，gzip 写入还需要输出缓冲区。

**错误与边缘情形：** NULL、缓冲区已分配、模式错误或 `size >= 2^31` 时返回 -1，
不改变请求。小大小被提升至八，而不是二。请求成功不保证后续分配成功。
不但要在普通 I/O 前调用，也应在 `gzdirect` 或字节回退前调用。

</details>

## gzsetparams

为后续输入请求新的压缩级别和策略。

```c
int ZEXPORT gzsetparams(gzFile file, int level, int strategy);
```

### 返回值与后续调用 {#api-gzsetparams-returns}

**返回值类型。** `int` — zlib 状态码

状态码报告参数请求是否已传达给句柄，包括必要的旧输入处理。Z_OK 不证明压缩器已采用所请求的参数。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**已接受请求** | 请求未改变、新写入句柄记录请求以便延迟初始化，或活跃写入句柄在处理待办工作后到达参数更新步骤。 | 可使用有效参数继续，但须保留契约中的注意事项：源码忽略 deflateParams 的返回值，实际设置可能与记录的请求不同。 |
| `Z_STREAM_ERROR`<br>**调用被拒绝** | 句柄为 NULL、读取句柄、透明写入句柄，或有待处理硬错误。 | 使用活跃的 gzip 写入句柄。关闭前检查活跃句柄；不能假定清除错误会使请求的设置生效。 |
| `Z_MEM_ERROR / Z_ERRNO / Z_STREAM_ERROR`<br>**待办工作失败** | 待处理零填充或旧缓冲输入处理失败，并返回已记录错误码。 | 在句柄仍存活时检查 gzerror。区分非阻塞停顿与硬错误；请求尚未完成，不能盲目重放。 |

**判读要点。**

- 普通请求使用 -1 至 9 的级别及 Z_DEFAULT_STRATEGY 至 Z_FIXED 的策略。无效值在此不一定被拒绝，可能在后续初始化时以 Z_MEM_ERROR 失败。

### 调用条件与效果 {#api-gzsetparams-contract}

**定义域：** 受限定义域：gzip 写入句柄；普通级别 -1 至 9，策略
`Z_DEFAULT_STRATEGY` 至 `Z_FIXED`。**效果：** 有状态控制，可能执行 I/O。

**前置条件：** 活跃 gzip 写入句柄满足通用要求。拒绝透明写入句柄。
已有硬错误通常阻止调用。

**证明目标。**

- **目标。** `Goal.gzsetparams_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzsetparams_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求（这个调用没有参数条件）：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）。
- **无条件覆盖。** `level` 和 `strategy` 的每个取值；历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界；每一种分配结果。
- **保证。**
    - *返回。* 句柄为 NULL 时，不论其他参数取什么值，调用都返回 `Z_STREAM_ERROR`。对句柄调用时，调用在每个世界里都返回。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。
    - *写入。* 句柄为 NULL 时不写任何内容：堆和世界都不变。对句柄调用时，只写句柄自己的块。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 对句柄调用时的返回值，以及由此得到的字节、位置和标志：功能目标 `Goal.gzsetparams`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzsetparams"><summary>完整返回条件与边界</summary>

**后置条件：** 请求未改变时返回 `Z_OK`。新写入句柄记录请求，供延迟初始化使用。
已活动的写入句柄先用旧参数处理待处理输入，再请求改变参数。
待处理定位可能写入零字节。

**错误与边缘情形：** NULL、读取句柄、透明写入句柄或待处理硬错误返回 `Z_STREAM_ERROR`。
定位／刷新失败返回已记录错误。源码忽略 `deflateParams` 的返回值，可能在记录了
压缩器未应用的参数后报告 `Z_OK`。这一点**尚未由证明确认**，须对照当前固定的源码核对，
包括有效请求；有效标量限制不会消除该问题。无效参数在此并非总被拒绝，还可能使后续初始化失败
被报告为 `Z_MEM_ERROR`。

</details>

## gzread

读取至多 `len` 个未压缩字节。

```c
int ZEXPORT gzread(gzFile file, voidp buf, unsigned len);
```

### 返回值与后续调用 {#api-gzread-returns}

**返回值类型。** `int` — 已读取的未压缩字节数，或失败标记

正数表示本次已交付的字节数。零可能表示零长度请求、EOF 或截断；-1 才是该接口的失败标记。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `0 < n <= len`<br>**已交付 n 字节** | 读取、解压或缓冲数据提供了 n 字节；返回不足或已有错误记录时，已交付前缀仍有效。 | 处理这 n 字节；不足请求时查询 gzerror 和 gzeof，再决定是否继续读取。 |
| `0`<br>**零长度请求** | len 为零且已有状态未使调用失败；不消费输入，也不执行待处理定位。 | 按需要发起非零长度读取；不能由此判断 EOF。 |
| `0`<br>**EOF 或截断，无输出** | 非零请求没有可交付字节；正常末尾和记录为 Z_BUF_ERROR 的截断都可返回零。 | 查询 gzerror 和 gzeof；Z_BUF_ERROR 不表示完整 gzip 成员已成功结束。 |
| `-1`<br>**请求失败或暂时停顿** | NULL、模式错误、len > INT_MAX、无可交付字节的硬错误，或无输出的非阻塞停顿；已有错误状态也可使零请求失败。 | 对有效句柄查询 gzerror。仅在确认是可重试停顿并处理等待后重试；硬错误须按其原因处理。 |

**判读要点。**

- 返回值按字节计数，不是 zlib 状态码。超大请求记录 Z_STREAM_ERROR，但保留已有严重错误。

### 调用条件与效果 {#api-gzread-contract}

**定义域：** 受限定义域：读取句柄和目标；完整无符号 `len` 的拒绝范围。

**效果：** 有状态读取、目标写入，可能分配内存。

**前置条件：** 当 `len <= INT_MAX` 时，`buf` 按共享分离规则覆盖 `len` 个可写字节。
零范围不需要访问任何字节。

**证明目标。**

- **目标。** `Goal.gzread_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzread_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）；
    2. 参数条件（`GzArguments`）：`len > INT_MAX` 时没有要求；否则 `len == 0`，或者 `buf` 覆盖 `len` 个可写字节且在句柄自己的块之外（`GzRange`）。
- **无条件覆盖。** `len` 的每个取值，包括 0 和大于 `INT_MAX` 的值；在这两种情形下 `buf` 可取任意值；历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界；每一种分配结果。
- **保证。**
    - *返回。* 句柄为 NULL 时，不论其他参数取什么值，调用都返回 `-1`。对句柄调用时，在每个世界里，调用都不会以未定义行为或内存错误结束：执行唯一可能的错误是循环燃料耗尽。读取预算成立时（`ReadsFinite`：描述符还能交付的字节少于 `2^61`）调用返回。即使 C 会立刻返回的情形，也要求这个预算。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。
    - *写入。* 句柄为 NULL 时不写任何内容：堆和世界都不变。对句柄调用时，只写句柄自己的块；当 `0 < len <= INT_MAX` 时还有 `buf` 处的 `len` 个字节。长度为零的读不点名任何调用者区域。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 对句柄调用时的返回值，以及由此得到的字节、位置和标志：功能目标 `Goal.gzread`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzread"><summary>完整返回条件与边界</summary>

**后置条件：** 正结果 `n <= len` 给出接下来的 `n` 个字节，
在处理任何待处理跳过后，将位置推进 `n`。格式、成员拼接、透明输入和延迟错误遵循共享读取规则。

**错误与边缘情形：** NULL、模式错误、无法交付数据的硬错误或 `len > INT_MAX` 时返回 -1；
超大请求记录 `Z_STREAM_ERROR`，除非需保留更严重错误。
EOF／截断且无输出时返回零。零请求通常返回零，但已有错误／停顿状态仍可能导致 -1。
应查询 `gzerror`；截断对应 `Z_BUF_ERROR`，不表示成功完成 gzip 成员。
后续错误不抹除已交付字节。阻塞描述符可能等待以填满内部读取。
非阻塞停顿可重试，不是 EOF。透明读取时 `read` 先交付字节然后失败，在未打补丁的 C 中是越界读；补丁 0003 修复了它
（见[注意事项](#scope-and-source-caveats)）。重试会得到什么，**尚未由证明确认**。

</details>

## gzfread

读取至多 `nitems` 个数据项，每项为 `size` 个未压缩字节。

```c
z_size_t ZEXPORT gzfread(voidp buf, z_size_t size, z_size_t nitems, gzFile file);
```

### 返回值与后续调用 {#api-gzfread-returns}

**返回值类型。** `z_size_t` — 已读取的完整数据项数

返回完整 size 字节数据项的数量。末尾不足一项的字节也已写入并消费，却不计入返回值。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `n = nitems > 0`<br>**完整读取请求的数据项** | size 非零，请求乘积可表示，且读到 size * nitems 字节。 | 处理这些完整数据项；这并不检测后续 EOF 或验证尚未读取的成员尾部。 |
| `0 < n < nitems`<br>**读取了部分完整数据项** | 读到 n 个完整数据项，可能还写入并消费了不足一项的尾部；EOF、停顿或错误可使读取停止。 | 查询 gzerror 和 gzeof。不要仅以 n * size 推断实际已消费字节数或安全续读位置。 |
| `0`<br>**请求总长度为零** | size 或 nitems 为零；不消费输入，也不执行待处理定位。 | 如需数据，使用非零大小和项数；零结果不说明 EOF。 |
| `0`<br>**未返回完整数据项** | 非零请求遇到 NULL、模式错误、EOF、停顿、硬错误或乘积溢出；也可能已消费不足一项的字节。溢出记录 Z_STREAM_ERROR，保留已有严重错误。 | 对有效句柄查询 gzerror 和 gzeof；先区分原因，不要把零当作未消费任何字节。 |

**判读要点。**

- 该接口的总请求没有 gzread 的 INT_MAX 限制；乘积仍须能用 z_size_t 表示。

### 调用条件与效果 {#api-gzfread-contract}

**定义域：** 受限定义域：读取句柄／目标；完整标量大小范围，包含溢出拒绝。

**效果：** 有状态读取和目标写入。

**前置条件：** 乘积可表示时，`buf` 覆盖 `size * nitems` 个可写字节，并满足共享分离规则。

**证明目标。**

- **目标。** `Goal.gzfread_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzfread_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）；
    2. 参数条件（`GzArguments`）：`size * nitems >= 2^64` 时没有要求；否则乘积为零，或者 `buf` 覆盖这么多个可写字节且在句柄自己的块之外（`GzRange`）。
- **无条件覆盖。** `size` 和 `nitems` 的每个取值，包括乘积为零和乘积不小于 `2^64` 的情形；在这两种情形下 `buf` 可取任意值；历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界；每一种分配结果。
- **保证。**
    - *返回。* 句柄为 NULL 时，不论其他参数取什么值，调用都返回 `0`。对句柄调用时，在每个世界里，调用都不会以未定义行为或内存错误结束：执行唯一可能的错误是循环燃料耗尽。读取预算成立时（`ReadsFinite`：描述符还能交付的字节少于 `2^61`）调用返回。即使 C 会立刻返回的情形，也要求这个预算。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。
    - *写入。* 句柄为 NULL 时不写任何内容：堆和世界都不变。对句柄调用时，只写句柄自己的块；当乘积非零且小于 `2^64` 时还有 `buf` 处的 `size * nitems` 个字节。长度为零的读不点名任何调用者区域。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 对句柄调用时的返回值，以及由此得到的字节、位置和标志：功能目标 `Goal.gzfread`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzfread"><summary>完整返回条件与边界</summary>

**后置条件：** 返回读到的完整数据项数量。全部已读字节都被消费和写入，
包括未计入返回数量的最终部分数据项。适用共享读取行为及 `gzread` 的恢复注意事项。

**错误与边缘情形：** `size` 或 `nitems` 为零时返回零，不消费输入。
乘积溢出返回零并记录 `Z_STREAM_ERROR`，同时保留此前严重错误。
NULL、模式错误、EOF 和硬错误也可返回零。
数量不足时须通过 `gzerror`／`gzeof` 区分原因；此处总请求没有 `INT_MAX` 限制。

</details>

## gzgetc

将一个未压缩字节作为无符号值读取。

```c
int ZEXPORT gzgetc(gzFile file);
```

### 返回值与后续调用 {#api-gzgetc-returns}

**返回值类型。** `int` — 无符号字节值，或失败／EOF 标记

0–255 是读到的实际字节，-1 表示没有返回字节。该调用会推进读取状态。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `0 <= c <= 255`<br>**读到一个字节** | 从缓冲区或后续读取获得一个字节；完成待处理跳过后，未压缩位置增加一。已有错误可推迟到缓冲字节耗尽后报告。 | 使用该字节；255 和零都是数据值。 |
| `-1`<br>**未返回字节** | NULL、写入句柄、EOF，或没有可交付字节的错误／非阻塞停顿。 | 对有效读取句柄查询 gzerror 和 gzeof；仅对确认可重试的停顿等待后重试。 |

**判读要点。**

- 头文件的宏快路径也会改变同一读取句柄，不能作为只读查询使用。

### 调用条件与效果 {#api-gzgetc-contract}

**定义域：** 受限定义域：读取句柄。**效果：** 有状态读取，可能分配内存。

**前置条件：** 满足共享读取句柄要求。

**证明目标。**

- **目标。** `Goal.gzgetc_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzgetc_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有三个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）；以及对 `zlib.h` 的 `gzgetc()` 宏（`Zlib.ZlibH.gzgetc`）的同样陈述，这个宏是应用程序调用 `gzgetc` 的默认方式。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求（这个调用没有参数条件）：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）。
- **无条件覆盖。** 历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界；每一种分配结果。
- **保证。**
    - *返回。* 句柄为 NULL 时调用返回 `-1`。对句柄调用时，在每个世界里，调用都不会以未定义行为或内存错误结束：执行唯一可能的错误是循环燃料耗尽。读取预算成立时（`ReadsFinite`：描述符还能交付的字节少于 `2^61`）调用返回。即使 C 会立刻返回的情形，也要求这个预算。对句柄使用宏时，同样不会以未定义行为或内存错误结束。有缓冲输出（`have != 0`）时，它不需要前提就返回；`have == 0` 时它调用函数，在读取预算下返回。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。宏返回之后同样如此。
    - *写入。* 句柄为 NULL 时不写任何内容：堆和世界都不变。对句柄调用时，只写句柄自己的块。宏同样不写任何调用者区域。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 对 NULL 句柄使用宏：它读取 `file->have`，在 C 中是未定义行为；拒绝子句说的是函数。对句柄调用时的返回值，以及由此得到的字节、位置和标志：功能目标 `Goal.gzgetc`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzgetc"><summary>完整返回条件与边界</summary>

**后置条件：** 返回 0–255 内的值，消费一个字节，并在待处理跳过后将未压缩位置推进一。
可直接使用缓冲数据，不进行描述符 I/O。适用共享格式和延迟错误规则。

**错误与边缘情形：** NULL、写入句柄、EOF 或没有可交付字节的错误返回 -1。
`gzerror` 区分这些读取结果。字节 255 不是 EOF。
头文件可提供修改同一句柄状态的宏快速路径；调用者不得把该宏当成无状态查询。

</details>

## gzgetc_

提供单字节读取的导出包装函数。

```c
int ZEXPORT gzgetc_(gzFile file);
```

### 返回值与后续调用 {#api-gzgetc_-returns}

**返回值类型。** `int` — 无符号字节值，或失败／EOF 标记

这是单字节读取的导出包装函数，结果与 gzgetc 函数相同。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `0 <= c <= 255`<br>**读到一个字节** | 获得一个字节并消费它；完成待处理跳过后，未压缩位置增加一。缓冲字节可先于已有错误返回。 | 使用该无符号字节值；255 不是 EOF。 |
| `-1`<br>**未返回字节** | NULL、模式错误、EOF，或没有可交付字节的错误／非阻塞停顿。 | 对有效读取句柄查询 gzerror 和 gzeof，再决定结束、处理错误或等待可重试停顿。 |

### 调用条件与效果 {#api-gzgetc_-contract}

**定义域：** 与 `gzgetc` 相同的受限定义域：读取句柄。

**效果：** 有状态读取，可能分配内存。

**前置条件：** 满足 `gzgetc` 的句柄要求。

**证明目标。**

- **目标。** `Goal.gzgetc__safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzgetc__safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求（这个调用没有参数条件）：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）。
- **无条件覆盖。** 历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界；每一种分配结果。
- **保证。**
    - *返回。* 句柄为 NULL 时调用返回 `-1`。对句柄调用时，在每个世界里，调用都不会以未定义行为或内存错误结束：执行唯一可能的错误是循环燃料耗尽。读取预算成立时（`ReadsFinite`：描述符还能交付的字节少于 `2^61`）调用返回。即使 C 会立刻返回的情形，也要求这个预算。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。
    - *写入。* 句柄为 NULL 时不写任何内容：堆和世界都不变。对句柄调用时，只写句柄自己的块。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 对句柄调用时的返回值，以及由此得到的字节、位置和标志：功能目标 `Goal.gzgetc_`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzgetc_"><summary>完整返回条件与边界</summary>

**后置条件：** 适用 `gzgetc` 的字节、位置、缓冲和格式契约。

**错误与边缘情形：** NULL／模式错误／EOF／错误情形返回 -1。
即使公开名称 `gzgetc` 展开为宏，该包装函数仍具有函数行为。

</details>

## gzungetc

将一个字节压回读取句柄的未压缩输入。

```c
int ZEXPORT gzungetc(int c, gzFile file);
```

### 返回值与后续调用 {#api-gzungetc-returns}

**返回值类型。** `int` — 原始非负参数，或失败标记

成功返回原始 c，但只压回它的低八位。未压缩位置减一，物理文件不变。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `c >= 0`<br>**压回一个字节** | 缓冲区有可用空间，且待处理跳过未失败；保存 c & 0xff，返回原始 c，并清除越过 EOF 标志。有已分配空间时，即使检查或读取曾记录错误，也可能成功。 | 后续读取先返回压回的数据，顺序与压回顺序相反；已有读取错误不一定被清除。 |
| `-1`<br>**未压回字节** | NULL、写入句柄、负 c、无压回空间，或设置／跳过失败。空间已满会记录 Z_DATA_ERROR，除非保留已有严重错误。 | 对有效句柄查询 gzerror。检查或跳过可在拒绝负 c 前发生，不能假定位置和状态完全未变。 |

**判读要点。**

- 刚打开后也允许压回，逻辑位置可变为负数；因此 tell 返回 -1 也可能是真实位置。

### 调用条件与效果 {#api-gzungetc-contract}

**定义域：** 受限定义域：读取句柄；完整 `int c` 范围，包括负数拒绝。

**效果：** 有状态字节回退，可能检查输入、分配内存和跳过数据。

**前置条件：** 满足共享读取句柄要求。允许在打开后立即回退字节，
因此逻辑位置可能成为负数。

**证明目标。**

- **目标。** `Goal.gzungetc_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzungetc_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求（这个调用没有参数条件）：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）。
- **无条件覆盖。** `c` 的每个取值；历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界；每一种分配结果。
- **保证。**
    - *返回。* 句柄为 NULL 时，不论其他参数取什么值，调用都返回 `-1`。对句柄调用时，在每个世界里，调用都不会以未定义行为或内存错误结束：执行唯一可能的错误是循环燃料耗尽。读取预算成立时（`ReadsFinite`：描述符还能交付的字节少于 `2^61`）调用返回。即使 C 会立刻返回的情形，也要求这个预算。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。
    - *写入。* 句柄为 NULL 时不写任何内容：堆和世界都不变。对句柄调用时，只写句柄自己的块。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 对句柄调用时的返回值，以及由此得到的字节、位置和标志：功能目标 `Goal.gzungetc`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzungetc"><summary>完整返回条件与边界</summary>

**后置条件：** 成功时存储 `c` 的低八位，返回原始非负 `c`，位置减一，
并清除越过 EOF 标志。压回的字节按压回顺序的逆序读取。物理输入文件不变。

**错误与边缘情形：** NULL、写入句柄、负 `c`、无回退空间或准备／跳过失败时返回 -1。
初始检查和待处理跳过可能在拒绝负 `c` 之前发生。
回退缓冲区满时记录 `Z_DATA_ERROR`，除非需保留严重错误。
已分配空间时，字节回退可能在读取错误后成功；它通常不清除该错误。
位置 -1 可以是成功状态，因此位置查询只返回 -1 时存在歧义。
从这个负位置继续定位，在未打补丁的 C 中会溢出；补丁 0002 修复了它（见[注意事项](#scope-and-source-caveats)）。本契约不排除这个状态。

</details>

## gzgets

读取一个行片段，并以 NUL 结尾。

```c
char * ZEXPORT gzgets(gzFile file, char *buf, int len);
```

### 返回值与后续调用 {#api-gzgets-returns}

**返回值类型。** `char *` — 调用者缓冲区指针，或 NULL

返回 buf 表示已写入 NUL 终止的行片段；返回 NULL 表示没有返回片段。它返回指针，不返回字节数。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `buf`<br>**返回行片段** | len > 1 且已复制至少一个数据字节，至多 len - 1 字节；遇到首个换行时包含该换行，也可因长度、EOF 或错误而停止。 | 处理片段；可能仍有同一行的后续数据。返回前缀时仍可有已记录错误，按需查询 gzerror。 |
| `buf`<br>**返回空字符串** | len == 1 且调用在状态检查和待处理跳过后被接受；只写入 NUL，不复制输入字节，即使已到 EOF 也可成功。 | 使用更大的缓冲区读取数据；此前待处理跳过仍可能已消费输入或改变位置。 |
| `NULL`<br>**请求被拒绝** | NULL 句柄、NULL buf、写入句柄或 len < 1。 | 修正句柄模式或缓冲区参数后再读取。 |
| `NULL`<br>**EOF、停顿或错误，无片段** | 有效请求遇到不可交付的错误或失败的待处理跳过；len > 1 时，无数据的 EOF 或非阻塞停顿也返回 NULL。 | 查询 gzerror 和 gzeof，区分末尾、截断、停顿和硬错误；仅在适合相应状态时继续。 |

**判读要点。**

- 输入中的 NUL 会作为数据复制；strlen(buf) 不能可靠表示本次实际消费的字节数。

### 调用条件与效果 {#api-gzgets-contract}

**定义域：** 受限定义域：读取句柄／目标；完整 `int len` 拒绝范围。

**效果：** 有状态读取和目标写入。

**前置条件：** `buf` 非 NULL 且 `len > 0` 时，目标按共享分离规则覆盖 `len` 个可写字节。

**证明目标。**

- **目标。** `Goal.gzgets_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzgets_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）；
    2. 参数条件（`GzArguments`）：`buf == NULL` 或 `len < 1` 时没有要求；否则 `buf` 覆盖 `len` 个可写字节且在句柄自己的块之外（`GzRange`）。
- **无条件覆盖。** `len` 的每个取值，包括小于 1 的值；`buf` 为 NULL；历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界；每一种分配结果。
- **保证。**
    - *返回。* 句柄为 NULL 时，不论其他参数取什么值，调用都返回 `NULL`。对句柄调用时，在每个世界里，调用都不会以未定义行为或内存错误结束：执行唯一可能的错误是循环燃料耗尽。读取预算成立时（`ReadsFinite`：描述符还能交付的字节少于 `2^61`）调用返回。即使 C 会立刻返回的情形，也要求这个预算。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。
    - *写入。* 句柄为 NULL 时不写任何内容：堆和世界都不变。对句柄调用时，只写句柄自己的块；当 `len >= 1` 时还有 `buf` 处的 `len` 个字节。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 对句柄调用时的返回值，以及由此得到的字节、位置和标志：功能目标 `Goal.gzgets`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzgets"><summary>完整返回条件与边界</summary>

**后置条件：** 返回 `buf`，其中最多含 `len - 1` 个数据字节及一个终止 NUL。
在首个换行符后停止（包括该换行符），或在达到限制／EOF 时停止。
已消费数据推进位置。输入中的内嵌 NUL 也作为数据复制。

**错误与边缘情形：** NULL 句柄／缓冲区、模式错误或 `len < 1` 返回 NULL。
更大长度下，无字节的 EOF 或无法交付数据的错误返回 NULL；
已交付前缀仍可能返回，同时记录错误。
`len == 1` 时，其他条件可接受的调用不向 `buf` 复制输入字节，并返回空字符串，
即使已在 EOF。先执行待处理跳过：它可能消费输入、解压、分配、推进位置，
或失败并返回 NULL。适用共享的延迟错误和部分读取注意事项。

</details>

## gzwrite

接受 `len` 个未压缩字节用于输出。

```c
int ZEXPORT gzwrite(gzFile file, voidpc buf, unsigned len);
```

### 返回值与后续调用 {#api-gzwrite-returns}

**返回值类型。** `int` — 已接受的未压缩字节数

返回值计数本次已接受的字节，数据可能仍在缓冲区中。零可能表示空请求，也可能表示失败。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `n = len > 0`<br>**已接受全部字节** | 在完成待处理零填充后，全部 len 个请求字节已缓冲或压缩；len <= INT_MAX。 | 可继续提交后续输入。检查刷新或关闭，确认是否有延迟输出失败。 |
| `0 <= n < len`<br>**接受前缀后停顿** | 非阻塞写入停顿，返回已接受字节数，可能为零。 | 用 gzerror 确认停顿，处理可写状态后，只重试 buf + n 处未接受的后缀。 |
| `0`<br>**没有请求字节** | len 为零且句柄通过写入模式／错误检查。不写数据，也不执行待处理定位。 | 无需重新提交输入。最终仍须关闭句柄。 |
| `0`<br>**请求失败或被拒绝** | 句柄为 NULL、读取句柄、有硬错误、len 超过 INT_MAX，或分配／定位／输出失败。len 过大会记录 Z_DATA_ERROR。 | 对活跃句柄，关闭前检查 gzerror。硬失败即使返回零也可能已消费前缀；不能把零作为重试偏移。 |

### 调用条件与效果 {#api-gzwrite-contract}

**定义域：** 受限定义域：写入句柄／源；完整无符号 `len` 拒绝范围。

**效果：** 有状态写入、缓冲，可能分配内存。

**前置条件：** `len <= INT_MAX` 时，`buf` 按共享分离规则覆盖 `len` 个可读字节。
所选压缩参数有效。

**证明目标。**

- **目标。** `Goal.gzwrite_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzwrite_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）；
    2. 参数条件（`GzArguments`）：`len > INT_MAX` 时没有要求；否则 `len == 0`，或者 `buf` 覆盖 `len` 个可读字节且在句柄自己的块之外（`GzRange`）。
- **无条件覆盖。** `len` 的每个取值，包括 0 和大于 `INT_MAX` 的值；在这两种情形下 `buf` 可取任意值；历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界；每一种分配结果。
- **保证。**
    - *返回。* 句柄为 NULL 时，不论其他参数取什么值，调用都返回 `0`。对句柄调用时，调用在每个世界里都返回。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。
    - *写入。* 句柄为 NULL 时不写任何内容：堆和世界都不变。对句柄调用时，只写句柄自己的块。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 对句柄调用时的返回值，以及由此得到的字节、位置和标志：功能目标 `Goal.gzwrite`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzwrite"><summary>完整返回条件与边界</summary>

**后置条件：** 通常返回 `len`，在处理任何待处理的零填充定位后，按接受数量推进位置。
输出为 gzip；若指定 `T`，则为原样字节。
接受数据后仍可能保留在缓冲区中；仍要求成功关闭。

**错误与边缘情形：** NULL、读取句柄、硬错误、分配失败或系统写入失败返回零。
`len > INT_MAX` 返回零并记录 `Z_DATA_ERROR`。
零请求不写入，也不执行待处理定位。硬失败即使返回零，也可能已消费一个前缀。
非阻塞停顿可返回不足的已接受数量；处理停顿后，重试尚未接受的后缀。
共享的结束失败恢复注意事项仍适用。

</details>

## gzfwrite

接受至多 `nitems` 个数据项，每项为 `size` 个未压缩字节。

```c
z_size_t ZEXPORT gzfwrite(voidpc buf, z_size_t size, z_size_t nitems, gzFile file);
```

### 返回值与后续调用 {#api-gzfwrite-returns}

**返回值类型。** `z_size_t` — 已接受的完整数据项数

返回值计数每项 size 字节的完整数据项，不是字节数。已接受的最后一个部分项的字节不计入此数。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `n = nitems > 0`<br>**已接受全部数据项** | size 非零、size * nitems 可表示，且全部请求字节已接受。 | 可继续提交后续输入，并检查刷新或关闭时的延迟输出错误。 |
| `0 <= n < nitems`<br>**完整项数不足** | 非阻塞停顿使已接受字节不足。只计完整项，但还可能已消费一个部分项，即使 n 为零。 | 检查 gzerror。仅靠数据项数无法确定安全的字节重试指针；不能简单从 buf + n * size 重新发送。 |
| `0`<br>**未请求数据** | size 或 nitems 为零，且句柄通过写入模式／错误检查。不进行数据 I/O 或待处理定位。 | 无需重新提交输入；保持正常句柄生存期。 |
| `0`<br>**请求失败或被拒绝** | 句柄为 NULL、模式错误或有硬错误，乘积溢出，或分配／定位／输出失败。溢出记录 Z_STREAM_ERROR。 | 关闭前用 gzerror 检查活跃句柄。硬失败可能隐藏已接受前缀，故零不证明可安全重发整个请求。 |

### 调用条件与效果 {#api-gzfwrite-contract}

**定义域：** 受限定义域：写入句柄／源；完整标量大小范围，包含溢出拒绝。

**效果：** 有状态写入和缓冲。

**前置条件：** 乘积可表示时，`buf` 覆盖 `size * nitems` 个可读字节。
满足共享写入句柄和分离要求。

**证明目标。**

- **目标。** `Goal.gzfwrite_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzfwrite_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）；
    2. 参数条件（`GzArguments`）：`size * nitems >= 2^64` 时没有要求；否则乘积为零，或者 `buf` 覆盖这么多个可读字节且在句柄自己的块之外（`GzRange`）。
- **无条件覆盖。** `size` 和 `nitems` 的每个取值，包括乘积为零和乘积不小于 `2^64` 的情形；在这两种情形下 `buf` 可取任意值；历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界；每一种分配结果。
- **保证。**
    - *返回。* 句柄为 NULL 时，不论其他参数取什么值，调用都返回 `0`。对句柄调用时，调用在每个世界里都返回。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。
    - *写入。* 句柄为 NULL 时不写任何内容：堆和世界都不变。对句柄调用时，只写句柄自己的块。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 对句柄调用时的返回值，以及由此得到的字节、位置和标志：功能目标 `Goal.gzfwrite`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzfwrite"><summary>完整返回条件与边界</summary>

**后置条件：** 返回已接受的完整数据项数量。
已接受字节推进位置；部分数据项可能已接受，但未计入返回数量。
输出格式和延迟 I/O 的含义与 `gzwrite` 相同。

**错误与边缘情形：** 任一因子为零时返回零，不进行数据 I/O 或待处理定位。
乘积溢出返回零，并记录 `Z_STREAM_ERROR`。NULL、模式错误和硬失败也返回零。
不足的数据项数量可能隐藏已消费的部分项，硬错误也可能隐藏已接受的前缀；
因此返回数量不足以计算安全重试指针。应查询 `gzerror`。

</details>

## gzputc

接受 `c` 的低八位用于输出。

```c
int ZEXPORT gzputc(gzFile file, int c);
```

### 返回值与后续调用 {#api-gzputc-returns}

**返回值类型。** `int` — 已接受字节值或失败标记

成功返回字节值，不是数量或 zlib 状态码。任意 int 输入均转换为其低八位。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `c & 0xff`<br>**已接受一个字节** | 在完成待处理零填充定位后接受一个字节；返回值为 0 至 255。 | 可继续提交后续输入；此字节可能仍在缓冲区中，应检查刷新或关闭。 |
| `-1`<br>**未确认接受字节** | 句柄为 NULL、读取句柄、有待处理硬错误，或分配、待处理定位或写入失败。 | 关闭前在活跃句柄上检查 gzerror。待办工作可能已改变输出或位置；不能推断状态未变。 |

**判读要点。**

- 负 c 转换后仍为数据，不是 EOF；成功返回字节值 0 不表示失败。

### 调用条件与效果 {#api-gzputc-contract}

**定义域：** 受限定义域：写入句柄；完整 `int c` 范围。

**效果：** 有状态写入，可能分配内存。

**前置条件：** 满足共享写入句柄要求，压缩参数有效。

**证明目标。**

- **目标。** `Goal.gzputc_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzputc_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求（这个调用没有参数条件）：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）。
- **无条件覆盖。** `c` 的每个取值；历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界；每一种分配结果。
- **保证。**
    - *返回。* 句柄为 NULL 时，不论其他参数取什么值，调用都返回 `-1`。对句柄调用时，调用在每个世界里都返回。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。
    - *写入。* 句柄为 NULL 时不写任何内容：堆和世界都不变。对句柄调用时，只写句柄自己的块。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 对句柄调用时的返回值，以及由此得到的字节、位置和标志：功能目标 `Goal.gzputc`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzputc"><summary>完整返回条件与边界</summary>

**后置条件：** 返回 `c & 0xff`，接受一个字节，并在完成待处理零填充定位后将位置推进一。
该字节可能仍在缓冲区中。

**错误与边缘情形：** NULL、读取句柄、待处理硬错误或分配／定位／写入失败返回 -1。
负 `c` 转换为字节，不当作 EOF。失败调用仍可能在处理待处理工作时改变输出或位置。
关闭时应检查延迟输出失败。

</details>

## gzputs

接受以 NUL 结尾的字符串，不包含终止符。

```c
int ZEXPORT gzputs(gzFile file, const char *s);
```

### 返回值与后续调用 {#api-gzputs-returns}

**返回值类型。** `int` — 已接受字符串字节数或失败标记

返回值计数字符串终止符之前已接受的字节。不写入 NUL 终止符。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `n = strlen(s) > 0`<br>**已接受完整字符串** | 非空字符串不超过 INT_MAX 字节，并在完成待处理零填充后接受全部字节。 | 可继续提交后续输入，并检查刷新或关闭时的延迟输出错误。 |
| `0 < n < strlen(s)`<br>**接受前缀后停顿** | 非阻塞停顿返回小于字符串长度的正数。 | 用 gzerror 确认停顿，处理可写状态后，重试 s + n 处未接受的后缀。 |
| `0`<br>**已接受空字符串** | 句柄通过写入模式／错误检查，且 s 为空。不进行数据 I/O。 | 无需重新提交字符串字节；之后仍须在刷新或关闭时检查待处理输出。 |
| `-1`<br>**写入失败或被拒绝** | 句柄为 NULL、读取句柄、有硬错误、字符串超过 INT_MAX，或非空写入报告零，包括未接受字符串字节的停顿。超大字符串记录 Z_STREAM_ERROR。 | 关闭前在活跃句柄上检查 gzerror。硬失败即使返回 -1 也可能已消费字节，故不能由此得到通用重试偏移。 |

### 调用条件与效果 {#api-gzputs-contract}

**定义域：** 受限定义域：写入句柄和可读字符串。

**效果：** 有状态写入，可能分配内存。

**前置条件：** `s` 是可读、以 NUL 结尾、与拥有的状态分离的字符串。
满足共享写入句柄要求，压缩参数有效。

**证明目标。**

- **目标。** `Goal.gzputs_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzputs_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）；
    2. 参数条件（`GzArguments`）：`s` 是以 NUL 结尾的字符串，直到 NUL 为止都可读，且在句柄自己的块之外（`CString`、`GzRange`）；`s` 为 NULL 时不满足这个条件。
- **无条件覆盖。** 历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界；每一种分配结果。
- **保证。**
    - *返回。* 句柄为 NULL 时，不论其他参数取什么值，调用都返回 `-1`。对句柄调用时，调用在每个世界里都返回。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。
    - *写入。* 句柄为 NULL 时不写任何内容：堆和世界都不变。对句柄调用时，只写句柄自己的块。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 对句柄调用时的返回值，以及由此得到的字节、位置和标志：功能目标 `Goal.gzputs`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzputs"><summary>完整返回条件与边界</summary>

**后置条件：** 返回已接受字节数，通常为 `strlen(s)`，不写入 NUL。
在处理待处理零填充定位后，按已接受字节数推进位置。空字符串返回零，不进行数据 I/O。

**错误与边缘情形：** NULL 句柄、读取句柄、硬错误、字符串长于 `INT_MAX`，
或非空写入报告零时返回 -1。超大字符串记录 `Z_STREAM_ERROR`。
非阻塞停顿可返回不足但为正的数量。硬失败可能在消费字节后返回 -1；
该数量不是通用重试偏移。NULL `s` 不属于字符串定义域。

</details>

## gzprintf

格式化参数，并接受所得字节用于输出。

```c
int ZEXPORTVA gzprintf(gzFile file, const char *format, ...);
```

### 返回值与后续调用 {#api-gzprintf-returns}

**返回值类型。** `int` — 格式化字节数、零或 zlib 错误码

正值计数已接受的格式化字节。零与负值含义不同，不能视为简单的成功／失败标志。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `n > 0`<br>**已接受格式化字节** | 格式化结果长度严格小于所配置缓冲区大小，且已接受 n 个字节。不包括 NUL 终止符。 | 可继续提交后续输入；输出可能仍在缓冲区中。检查刷新或关闭时的后续输出错误。 |
| `0`<br>**未接受格式化字节** | 格式化输出为空、格式化器失败，或输出超出本次调用缓冲区。零不一定记录 gzerror 错误码。 | 区分空输出与格式化／大小失败。修正请求后再提交；此前待处理 I/O 或格式化器效果可能已发生。 |
| `Z_STREAM_ERROR`<br>**调用被拒绝** | 句柄为 NULL、模式错误，或有待处理硬错误。 | 使用活跃写入句柄和有效格式化参数。关闭前检查仍存活的句柄；不能推断此前错误已被清除。 |
| `Z_BUF_ERROR`<br>**需重试格式化调用** | 非阻塞停顿导致缓冲区空间不足，必须重试本次格式化调用。 | 处理停顿后重试格式化调用。须考虑此前待处理输出及格式化器效果；此结果不保证状态未变。 |
| `Z_MEM_ERROR / Z_ERRNO / Z_STREAM_ERROR`<br>**初始化或输出失败** | 缓冲区／编解码器初始化、待处理零填充，或格式化前后写入失败，并返回其错误码。 | 关闭前检查 gzerror，区分系统停顿与硬错误。负结果之前可能已改变状态，也不是安全的字节重试偏移。 |

**判读要点。**

- 默认每次调用的格式化长度须严格小于 8192 字节；gzbuffer 可更改此限制。格式参数（包括可写的 %n 目标）须满足完整契约。
- 任何负返回值都不保证位置、缓冲区、输出或格式化器可见内存保持不变。

### 调用条件与效果 {#api-gzprintf-contract}

**定义域：** 受限定义域：写入句柄和类型正确的 C 格式化参数。

**效果：** 有状态格式化写入、分配和格式化器效果。

**前置条件：** `format` 是可读且有终止符的字符串。
参数具有各转换要求的类型；引用对象有效。外部格式化遵循平台的 `vsnprintf` 语义。
任何 `%n` 目标均可写、正确分离，且属于允许的调用者可见效果。压缩参数有效。

**证明目标。**

- **目标。** `Goal.gzprintf_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzprintf_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）；
    2. 参数条件（`GzArguments`）：格式串是以 NUL 结尾的字符串，并且模型的格式化器能用给定的参数对它求值（`Formatted`）：整数、字符和字符串转换，带受支持的标志、宽度、精度和长度修饰符；格式串和每个字符串参数都在句柄自己的块之外。在读句柄和处于错误状态的句柄上也要求这个条件，尽管那时 C 并不读格式串。
- **无条件覆盖。** 历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界；每一种分配结果。
- **保证。**
    - *返回。* 句柄为 NULL 时，不论其他参数取什么值，调用都返回 `Z_STREAM_ERROR`。对句柄调用时，调用在每个世界里都返回。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。
    - *写入。* 句柄为 NULL 时不写任何内容：堆和世界都不变。对句柄调用时，只写句柄自己的块。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 浮点转换、`%p`、`%n`、`h` 和 `hh` 修饰符以及 `*` 宽度：在本目标之外（见[偏离记录](../../deviations.md)的“格式化”一行）。对句柄调用时的返回值，以及由此得到的字节、位置和标志：功能目标 `Goal.gzprintf`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzprintf"><summary>完整返回条件与边界</summary>

**后置条件：** 对创建的参数列表适用 `gzvprintf` 契约。
正结果表示已接受的格式化字节数，并推进未压缩位置。终止 NUL 不输出。
格式化是对外部库的假设，不是 zlib 的定理。

**错误与边缘情形：** NULL、读取句柄或待处理硬错误返回 `Z_STREAM_ERROR`，而不是零。
空或超大的格式化输出返回零。分配、待处理定位和 I/O 可在格式化前后失败；见 `gzvprintf`。
默认每次调用的格式化字节数须低于 8192，该限制随 `gzbuffer` 改变。
非可变参数的旧构建不属于此契约。

</details>

## gzvprintf

格式化 `va_list`，并接受结果用于输出。

```c
int ZEXPORTVA gzvprintf(gzFile file, const char *format, va_list va);
```

### 返回值与后续调用 {#api-gzvprintf-returns}

**返回值类型。** `int` — 格式化字节数、零或 zlib 错误码

正值计数已接受的格式化字节。零与负值含义不同，不能视为简单的成功／失败标志。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `n > 0`<br>**已接受格式化字节** | 格式化结果长度严格小于所配置缓冲区大小，且已接受 n 个字节。不包括 NUL 终止符。 | 可继续提交后续输入；输出可能仍在缓冲区中。检查刷新或关闭时的后续输出错误。 |
| `0`<br>**未接受格式化字节** | 格式化输出为空、格式化器失败，或输出超出本次调用缓冲区。零不一定记录 gzerror 错误码。 | 区分空输出与格式化／大小失败。修正请求后再提交；此前待处理 I/O 或格式化器效果可能已发生。 |
| `Z_STREAM_ERROR`<br>**调用被拒绝** | 句柄为 NULL、模式错误，或有待处理硬错误。 | 使用活跃写入句柄和有效格式化参数。关闭前检查仍存活的句柄；不能推断此前错误已被清除。 |
| `Z_BUF_ERROR`<br>**需重试格式化调用** | 非阻塞停顿导致缓冲区空间不足，必须重试本次格式化调用。 | 处理停顿后重试格式化调用。须考虑此前待处理输出及格式化器效果；此结果不保证状态未变。 |
| `Z_MEM_ERROR / Z_ERRNO / Z_STREAM_ERROR`<br>**初始化或输出失败** | 缓冲区／编解码器初始化、待处理零填充，或格式化前后写入失败，并返回其错误码。 | 关闭前检查 gzerror，区分系统停顿与硬错误。负结果之前可能已改变状态，也不是安全的字节重试偏移。 |

**判读要点。**

- 默认每次调用的格式化长度须严格小于 8192 字节；gzbuffer 可更改此限制。格式参数（包括可写的 %n 目标）须满足完整契约。
- 任何负返回值都不保证位置、缓冲区、输出或格式化器可见内存保持不变。
- va_list 须按格式初始化，并依平台生存期和复制规则使用。

### 调用条件与效果 {#api-gzvprintf-contract}

**定义域：** 受限定义域：写入句柄、有效参数列表和外部格式化。

**效果：** 有状态格式化写入，可能产生格式化器的内存效果。

**前置条件：** 满足 `gzprintf` 的格式、参数和分离要求。
`va` 已按这些参数初始化；其使用遵循平台的 `va_list` 生存期和复制规则。

**证明目标。**

- **目标。** `Goal.gzvprintf_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需，尽管 `zlib.h` 把这个函数列为未文档化：`gzprintf` 经由它实现。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzvprintf_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）；
    2. 参数条件（`GzArguments`）：格式串是以 NUL 结尾的字符串，并且模型的格式化器能用给定的参数对它求值（`Formatted`）：整数、字符和字符串转换，带受支持的标志、宽度、精度和长度修饰符；格式串和每个字符串参数都在句柄自己的块之外。在读句柄和处于错误状态的句柄上也要求这个条件，尽管那时 C 并不读格式串。
- **无条件覆盖。** 历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界；每一种分配结果。
- **保证。**
    - *返回。* 句柄为 NULL 时，不论其他参数取什么值，调用都返回 `Z_STREAM_ERROR`。对句柄调用时，调用在每个世界里都返回。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。
    - *写入。* 句柄为 NULL 时不写任何内容：堆和世界都不变。对句柄调用时，只写句柄自己的块。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 浮点转换、`%p`、`%n`、`h` 和 `hh` 修饰符以及 `*` 宽度：在本目标之外（见[偏离记录](../../deviations.md)的“格式化”一行）。对句柄调用时的返回值，以及由此得到的字节、位置和标志：功能目标 `Goal.gzvprintf`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzvprintf"><summary>完整返回条件与边界</summary>

**后置条件：** 正结果是已接受的格式化字节数，不含终止 NUL。
相应推进位置，数据可能仍被缓冲。格式化长度须严格小于配置的缓冲区大小。
此前待处理定位可在接受任何格式化输出前先输出零字节。

**错误与边缘情形：** NULL、模式错误或待处理硬错误返回 `Z_STREAM_ERROR`。
初始化、跳过或写入失败返回相应错误码。
空输出、格式化器失败或输出放不下时返回零；该零不一定记录错误，
此前待处理 I/O 可能已发生。若本次格式化调用必须重试，非阻塞停顿可返回 `Z_BUF_ERROR`。
不得由负结果推断状态未改变。没有安全有界格式化的构建，可能提供拒绝桩函数或
另行限定范围的不安全实现；两者都不在此默认契约内。

</details>

## gzflush

按请求的刷新模式处理缓冲输出。

```c
int ZEXPORT gzflush(gzFile file, int flush);
```

### 返回值与后续调用 {#api-gzflush-returns}

**返回值类型。** `int` — zlib 状态码

状态码报告所请求刷新工作的结果，句柄仍保持打开。Z_FINISH 成功完成一个成员，不结束句柄生存期。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**刷新工作已完成** | 请求的刷新和待处理零填充成功。Z_SYNC_FLUSH 使待处理数据可供读取；Z_FINISH 完成一个 gzip 成员。透明模式写出缓冲字节。 | 可继续使用活跃句柄；Z_FINISH 后的成功写入可开始另一成员。只关闭一次，并检查关闭结果。 |
| `Z_STREAM_ERROR`<br>**请求被拒绝** | 句柄为 NULL、读取句柄、有待处理硬错误，或 flush 不在 Z_NO_FLUSH 至 Z_FINISH 范围内。 | 在活跃写入句柄上使用有效刷新值。有效写入句柄可能先清除可重试错误，再拒绝无效刷新；不能假定拒绝保留了所有状态。 |
| `Z_MEM_ERROR / Z_ERRNO / Z_STREAM_ERROR`<br>**输出工作失败** | 缓冲区或编解码器初始化、待处理零填充，或压缩／系统输出失败，并返回其已记录错误码。 | 关闭前检查 gzerror，并区分非阻塞停顿和硬错误。失败的 Z_FINISH 未完成成员；仅清除错误不足以按全新输出恢复。 |

### 调用条件与效果 {#api-gzflush-contract}

**定义域：** 受限定义域：写入句柄；完整 `int flush` 拒绝范围。

**效果：** 有状态输出，可能分配内存并处理待处理零填充。

**前置条件：** 满足共享写入句柄要求，压缩参数有效。
普通刷新模式范围为 `Z_NO_FLUSH` 至 `Z_FINISH`。

**证明目标。**

- **目标。** `Goal.gzflush_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzflush_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求（这个调用没有参数条件）：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）。
- **无条件覆盖。** `flush` 的每个取值；历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界；每一种分配结果。
- **保证。**
    - *返回。* 句柄为 NULL 时，不论其他参数取什么值，调用都返回 `Z_STREAM_ERROR`。对句柄调用时，调用在每个世界里都返回。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。
    - *写入。* 句柄为 NULL 时不写任何内容：堆和世界都不变。对句柄调用时，只写句柄自己的块。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 对句柄调用时的返回值，以及由此得到的字节、位置和标志：功能目标 `Goal.gzflush`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzflush"><summary>完整返回条件与边界</summary>

**后置条件：** 请求工作成功时返回 `Z_OK`。`Z_SYNC_FLUSH` 使待处理数据可供读取；
`Z_FINISH` 完成一个 gzip 成员。后续成功写入可开始另一个成员。
`T` 写出缓冲字节，不生成 gzip 尾部。句柄仍存活，仍须关闭。

**错误与边缘情形：** NULL、读取句柄、待处理硬错误或 0–`Z_FINISH` 范围外的刷新值，
返回 `Z_STREAM_ERROR`。分配、定位填充和系统写入失败返回已记录错误码。
有效写入句柄在验证 `flush` 前会清除可重试错误，因此无效刷新不总是保持状态的拒绝。
失败的 `Z_FINISH` 不表示成员完成；仅清除错误不足以把恢复当作全新输出。
见下述注意事项。

</details>

## gzrewind

将读取句柄重置到保存的描述符起点。

```c
int ZEXPORT gzrewind(gzFile file);
```

### 返回值与后续调用 {#api-gzrewind-returns}

**返回值类型。** `int` — 回到起点的成功／失败标记

0 表示读取句柄已回到保存的起点，-1 表示失败。这里的零不是 zlib 状态码。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `0`<br>**已回到保存的起点** | 有效读取句柄处于 Z_OK 或 Z_BUF_ERROR，且描述符定位成功；未压缩位置归零，清除缓冲内容、待处理跳过和错误／EOF，重新检查格式。 | 可以从头再次读取；已有缓冲区仍由句柄拥有，最终仍须关闭。 |
| `-1`<br>**未能回到起点** | NULL、写入句柄、已记录的严重错误，或系统定位失败，例如不可定位的管道。 | 检查句柄模式和已有错误；系统定位失败时检查相应 errno。不要按成功回到起点继续。 |

**判读要点。**

- gzdopen 读取句柄回到打开时的描述符偏移，未必是物理文件偏移零；它不总与 gzseek(file, 0, SEEK_SET) 等价。

### 调用条件与效果 {#api-gzrewind-contract}

**定义域：** 受限定义域：读取句柄和描述符环境。

**效果：** 有状态定位和读取句柄重置。

**前置条件：** 活跃读取句柄满足共享要求。成功要求描述符可定位。
`Z_OK` 和 `Z_BUF_ERROR` 允许该操作。

**证明目标。**

- **目标。** `Goal.gzrewind_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzrewind_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求（这个调用没有参数条件）：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）。
- **无条件覆盖。** 历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界；每一种分配结果。
- **保证。**
    - *返回。* 句柄为 NULL 时调用返回 `-1`。对句柄调用时，调用在每个世界里都返回。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。
    - *写入。* 句柄为 NULL 时不写任何内容：堆和世界都不变。对句柄调用时，只写句柄自己的块。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 对句柄调用时的返回值，以及由此得到的字节、位置和标志：功能目标 `Goal.gzrewind`（不在计划内；已有定理证明它）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzrewind"><summary>完整返回条件与边界</summary>

**后置条件：** 返回 0，将未压缩位置设为零，丢弃已缓冲输入／输出和待处理跳过，
清除错误／EOF，并重新开始格式检查。已有缓冲区仍保持分配，归句柄拥有。

**错误与边缘情形：** NULL、写入句柄、已记录严重错误或系统定位失败返回 -1。
管道通常不能回到起点。`gzdopen` 读取句柄返回其初始描述符偏移，
不一定是物理文件偏移零。它与 `gzseek(file, 0, SEEK_SET)` 并非在所有模式下都可互换。

</details>

## gzseek64

请求相对于起点或当前位置的未压缩位置。

```c
z_off64_t ZEXPORT gzseek64(gzFile file, z_off64_t offset, int whence);
```

### 返回值与后续调用 {#api-gzseek64-returns}

**返回值类型。** `z_off64_t` — 请求的未压缩位置，或失败标记

返回请求的逻辑未压缩位置，不是物理压缩文件偏移。成功时仍可能把后续工作留给读取、写入、刷新或关闭。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `position >= 0`<br>**定位请求已接受** | 目标相对 SEEK_SET 或 SEEK_CUR 有效且可表示。透明读取可立即定位；gzip 读取必要时回到起点并登记剩余前向跳过；写入只允许前移。 | 检查后续 I/O。读取可能还须解压跳过，写入间隙由后续输出、刷新或关闭补零；接受请求不保证这些工作成功。 |
| `-1`<br>**定位失败或被拒绝** | NULL、模式错误、硬错误、无效参考点（含 SEEK_END）、起点之前或范围外的目标、写入向后定位，或所需的回到起点／系统定位失败。 | 区分无效请求、保存的错误和系统定位失败；不要按定位成功继续。 |

**判读要点。**

- Z_OK 和 Z_BUF_ERROR 允许定位；已记录的可重试 Z_ERRNO 仍会阻止定位。定位可立即消费缓冲字节。
- 越过 EOF 的请求可先成功；后续读取发现末尾后，tell 排除尚未满足的跳过。

### 调用条件与效果 {#api-gzseek64-contract}

**定义域：** 受限定义域：活跃读取／写入句柄；完整偏移范围要求源码的范围检查，
包括字节回退形成的负位置。

**效果：** 有状态定位、缓冲区丢弃，可能立即进行描述符 I/O。

**前置条件：** 满足共享要求。普通参考点为 `SEEK_SET` 和 `SEEK_CUR`。
`Z_OK` 和 `Z_BUF_ERROR` 允许该操作。

**证明目标。**

- **目标。** `Goal.gzseek64_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzseek64_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求（这个调用没有参数条件）：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）。
- **无条件覆盖。** `offset` 和 `whence` 的每个取值；历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界；每一种分配结果。
- **保证。**
    - *返回。* 句柄为 NULL 时，不论其他参数取什么值，调用都返回 `-1`。对句柄调用时，调用在每个世界里都返回。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。
    - *写入。* 句柄为 NULL 时不写任何内容：堆和世界都不变。对句柄调用时，只写句柄自己的块。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 对句柄调用时的返回值，以及由此得到的字节、位置和标志：功能目标 `Goal.gzseek64`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzseek64"><summary>完整返回条件与边界</summary>

**后置条件：** 非负结果是请求的未压缩位置。透明读取句柄可立即定位描述符。
gzip 读取句柄在需要时回到起点，将剩余前移延迟至后续解压。
写入句柄允许前移，由后续输出、刷新或关闭补入零字节。
因此成功请求仍可能在后续 I/O 中失败。

**错误与边缘情形：** NULL、无效参考点（包括 `SEEK_END`）、硬错误、起点之前的目标、
范围外目标、写入句柄向后定位，或必需的回到起点／系统定位失败，返回 -1。
定位可立即消费已缓冲字节。定位到输入 EOF 之后可以先成功；后续读取才发现实际末尾。
读取越过文件末尾后，位置查询不计尚未满足的跳过。
对字节回退形成的负位置，范围检查在未打补丁的 C 中会溢出；补丁 0002 修复了它
（见[注意事项](#scope-and-source-caveats)）。起点之前的字节回退在安全目标之内。

</details>

## gzseek

通过普通偏移类型请求未压缩位置。

```c
z_off_t ZEXPORT gzseek(gzFile file, z_off_t offset, int whence);
```

### 返回值与后续调用 {#api-gzseek-returns}

**返回值类型。** `z_off_t` — 请求的未压缩位置，或失败标记

非负值是请求的逻辑未压缩位置。接受定位请求不表示对应的解压、零填充或后续 I/O 已完成。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `position >= 0`<br>**定位请求已接受** | SEEK_SET 或 SEEK_CUR 请求有效且可表示；读取句柄可立即定位、消费缓冲数据或登记后续跳过，写入句柄仅允许前移。 | 继续读取或写入，并检查后续结果；读取的延迟跳过依靠解压完成，写入的间隙由后续输出、刷新或关闭补零。 |
| `-1`<br>**定位失败或被拒绝** | NULL、模式错误、硬错误、无效参考点（含 SEEK_END）、起点之前或范围外的目标、写入向后定位，或所需的回到起点／系统定位失败。较窄构建还拒绝无法用 z_off_t 表示的结果。 | 按请求、保存的错误或系统定位失败分别处理；不要把 -1 用作已到达的位置。 |

**判读要点。**

- 默认 LP64 构建与 gzseek64 使用相同的有符号 64 位位置范围。Z_OK 和 Z_BUF_ERROR 允许定位，已记录的可重试 Z_ERRNO 仍会阻止定位。
- 定位到 EOF 之后可先成功。后续读取发现实际末尾后，tell 不再计入未满足的跳过。

### 调用条件与效果 {#api-gzseek-contract}

**定义域：** 与 `gzseek64` 相同的受限定义域。

**效果：** 有状态定位，可能进行描述符 I/O。

**前置条件：** 满足 `gzseek64` 的句柄、参考点和环境要求。

**证明目标。**

- **目标。** `Goal.gzseek_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzseek_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求（这个调用没有参数条件）：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）。
- **无条件覆盖。** `offset` 和 `whence` 的每个取值；历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界；每一种分配结果。
- **保证。**
    - *返回。* 句柄为 NULL 时，不论其他参数取什么值，调用都返回 `-1`。对句柄调用时，调用在每个世界里都返回。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。
    - *写入。* 句柄为 NULL 时不写任何内容：堆和世界都不变。对句柄调用时，只写句柄自己的块。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 对句柄调用时的返回值，以及由此得到的字节、位置和标志：功能目标 `Goal.gzseek`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzseek"><summary>完整返回条件与边界</summary>

**后置条件：** 适用 `gzseek64` 的位置、延迟跳过、零填充和缓冲契约。
结果转换为 `z_off_t`。

**错误与边缘情形：** 相同的拒绝情形和负位置注意事项适用。
在较窄构建中，超出 `z_off_t` 的结果返回 -1；
默认 LP64 构建与 `gzseek64` 具有相同的有符号 64 位范围。

</details>

## gztell64

查询当前逻辑未压缩位置。

```c
z_off64_t ZEXPORT gztell64(gzFile file);
```

### 返回值与后续调用 {#api-gztell64-returns}

**返回值类型。** `z_off64_t` — 逻辑未压缩位置；-1 也可能是失败标记

返回已消费／接受的位置及有效的待处理前向跳过，不执行跳过或刷新。负数可来自起点前的压回。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `position != -1`<br>**逻辑位置值** | 活跃读取／写入句柄的报告和可表示；读取越过 EOF 后，待处理但未满足的跳过被排除。 | 把它作为未压缩字节位置；若需要物理压缩文件偏移，使用 gzoffset64。 |
| `-1`<br>**可能是真实位置 -1** | 有效句柄在起点之前压回字节，当前逻辑位置为 -1。 | 结合已知句柄有效性和压回历史解释，不要只按 -1 判断失败。 |
| `-1`<br>**查询被拒绝** | 句柄为 NULL 或模式错误。 | 使用活跃读取／写入句柄；单看结果无法与有效位置 -1 区分。 |

**判读要点。**

- 已接受的越过 EOF 的定位，可在后续读取发现实际末尾前被报告。查询不进行描述符 I/O，也不改变句柄。

### 调用条件与效果 {#api-gztell64-contract}

**定义域：** 受限定义域：活跃读取／写入句柄。

**效果：** 只读句柄查询；不进行描述符 I/O。

**前置条件：** 满足共享句柄要求，且报告的和可表示。

**证明目标。**

- **目标。** `Goal.gztell64_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gztell64_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求（这个调用没有参数条件）：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）。
- **无条件覆盖。** 历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界。
- **保证。**
    - *返回。* 句柄为 NULL 时调用返回 `-1`。对句柄调用时，调用在每个世界里都返回。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。
    - *写入。* 句柄为 NULL 时不写任何内容：堆不变。这个函数的翻译不接受世界，所以无从改变世界。对句柄调用时，只写句柄自己的块。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 对句柄调用时的返回值，以及由此得到的字节、位置和标志：功能目标 `Goal.gztell64`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="gztell64"><summary>完整返回条件与边界</summary>

**后置条件：** 返回已消费／接受的位置加上待处理前向跳过，
但读取越过 EOF 后不计待处理跳过。不执行待处理定位或刷新。
句柄及其分配不变。

**错误与边缘情形：** NULL 或模式错误返回 -1。起点前的字节回退可使 -1 成为真实位置。
此前接受的越过 EOF 的定位请求，可在后续读取发现实际末尾前由此处报告。
物理压缩文件偏移是另一种量，由 `gzoffset64` 查询。

</details>

## gztell

使用 `z_off_t` 查询逻辑未压缩位置。

```c
z_off_t ZEXPORT gztell(gzFile file);
```

### 返回值与后续调用 {#api-gztell-returns}

**返回值类型。** `z_off_t` — 逻辑未压缩位置；-1 也可能是失败标记

查询逻辑位置，不执行待处理定位或刷新。起点之前的压回可产生负位置，因此 -1 不足以单独判定失败。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `position != -1`<br>**逻辑位置值** | 活跃读取／写入句柄的可表示位置：已消费／接受的位置加待处理前向跳过；读取越过 EOF 后不计未满足的跳过。压回可产生负值。 | 将其作为未压缩字节位置使用；需要物理文件偏移时调用 gzoffset。 |
| `-1`<br>**可能是真实位置 -1** | 有效句柄在起点之前压回字节，使当前逻辑位置恰好为 -1。 | 结合已知句柄有效性和压回历史解释；不要仅凭返回值将其当作失败。 |
| `-1`<br>**查询被拒绝** | NULL 或模式错误；较窄构建也可能因结果无法用 z_off_t 表示而返回 -1。默认 LP64 构建没有额外缩窄。 | 使用有效句柄和可表示的位置范围；返回值本身不能消除真实位置 -1 的歧义。 |

**判读要点。**

- 此前接受的越过 EOF 的定位，在后续读取发现实际末尾前，仍可反映在此结果中。查询不进行描述符 I/O。

### 调用条件与效果 {#api-gztell-contract}

**定义域：** 与 `gztell64` 相同的受限定义域。

**效果：** 只读句柄查询。

**前置条件：** 满足 `gztell64` 的句柄和可表示性要求。

**证明目标。**

- **目标。** `Goal.gztell_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gztell_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求（这个调用没有参数条件）：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）。
- **无条件覆盖。** 历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界。
- **保证。**
    - *返回。* 句柄为 NULL 时调用返回 `-1`。对句柄调用时，调用在每个世界里都返回。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。
    - *写入。* 句柄为 NULL 时不写任何内容：堆不变。这个函数的翻译不接受世界，所以无从改变世界。对句柄调用时，只写句柄自己的块。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 对句柄调用时的返回值，以及由此得到的字节、位置和标志：功能目标 `Goal.gztell`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="gztell"><summary>完整返回条件与边界</summary>

**后置条件：** 返回转换为 `z_off_t` 的 `gztell64` 结果，不执行待处理工作，也不改变句柄。

**错误与边缘情形：** NULL／模式错误和位置 -1 具有与 `gztell64` 相同的歧义。
在较窄构建中，无法表示的结果返回 -1；默认 LP64 构建没有这项额外缩窄。

</details>

## gzoffset64

查询底层物理文件偏移。

```c
z_off64_t ZEXPORT gzoffset64(gzFile file);
```

### 返回值与后续调用 {#api-gzoffset64-returns}

**返回值类型。** `z_off64_t` — 物理文件偏移，或失败标记

返回底层描述符的当前位置，读取时扣除未使用的压缩输入。此物理量不表示已交付的未压缩字节数。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `offset != -1`<br>**物理文件偏移值** | 有效句柄的系统位置查询成功，偏移计算可表示；读取句柄减去持有的未使用压缩输入。 | 按物理偏移使用；查询不移动描述符、不刷新写入缓冲，也不执行待处理逻辑定位。 |
| `-1`<br>**无法取得物理偏移** | NULL、模式错误或系统位置查询失败，包括不可定位描述符。 | 检查句柄和描述符可定位性；系统失败时查看相应 errno，不要假定 gzerror 会记录本次查询失败。 |

**判读要点。**

- 透明读取句柄的未读输出缓冲不被扣除，因此结果可领先于已交付字节。gzdopen 起点之前已有的文件前缀仍计入偏移。

### 调用条件与效果 {#api-gzoffset64-contract}

**定义域：** 受限定义域：活跃读取／写入句柄及描述符环境。

**效果：** 只读句柄查询和系统位置查询；`errno` 可能改变。

**前置条件：** 满足共享要求。成功偏移计算可表示。

**证明目标。**

- **目标。** `Goal.gzoffset64_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzoffset64_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求（这个调用没有参数条件）：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）。
- **无条件覆盖。** 历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界。
- **保证。**
    - *返回。* 句柄为 NULL 时调用返回 `-1`。对句柄调用时，调用在每个世界里都返回。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。
    - *写入。* 句柄为 NULL 时不写任何内容：堆和世界都不变。对句柄调用时，只写句柄自己的块。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 对句柄调用时的返回值，以及由此得到的字节、位置和标志：功能目标 `Goal.gzoffset64`（不在计划内；已有定理证明它）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzoffset64"><summary>完整返回条件与边界</summary>

**后置条件：** 返回描述符的当前位置，读取句柄须减去持有的未使用压缩输入。
不刷新写入句柄的缓冲数据，也不执行待处理逻辑定位。不改变描述符位置。

**错误与边缘情形：** NULL、模式错误或系统查询失败（包括不可定位描述符）返回 -1。
它不同于未压缩位置。不减去透明读取句柄尚未读取的输出缓冲区，
因此结果可领先于已交付字节。包括 `gzdopen` 句柄初始偏移前已有的任何前缀。

</details>

## gzoffset

使用 `z_off_t` 查询物理文件偏移。

```c
z_off_t ZEXPORT gzoffset(gzFile file);
```

### 返回值与后续调用 {#api-gzoffset-returns}

**返回值类型。** `z_off_t` — 物理文件偏移，或失败标记

查询底层文件位置，读取时减去尚未使用的压缩输入。它不同于 tell 的逻辑未压缩位置。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `offset != -1`<br>**物理文件偏移值** | 有效句柄的系统位置查询成功，偏移计算可表示；读取句柄减去持有的未使用压缩输入，再转换为 z_off_t。 | 按物理文件偏移使用；该查询不移动描述符、不刷新写入缓冲，也不执行待处理逻辑定位。 |
| `-1`<br>**无法取得物理偏移** | NULL、模式错误或系统位置查询失败，包括不可定位描述符；较窄构建还拒绝超出 z_off_t 的结果。 | 检查句柄和描述符可定位性；系统查询失败时查看相应 errno，不能依赖 gzerror 一定保存本次失败。 |

**判读要点。**

- 透明读取句柄尚未交付的输出缓冲不被减去，所以结果可领先于已交付字节；gzdopen 起点之前已有的文件前缀也包含在偏移中。
- 默认构建与 gzoffset64 的位置范围相同，没有额外缩窄。

### 调用条件与效果 {#api-gzoffset-contract}

**定义域：** 与 `gzoffset64` 相同的受限定义域。

**效果：** 只读句柄查询和系统位置查询。

**前置条件：** 满足 `gzoffset64` 的句柄、环境和计算要求。

**证明目标。**

- **目标。** `Goal.gzoffset_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzoffset_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求（这个调用没有参数条件）：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）。
- **无条件覆盖。** 历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界。
- **保证。**
    - *返回。* 句柄为 NULL 时调用返回 `-1`。对句柄调用时，调用在每个世界里都返回。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。
    - *写入。* 句柄为 NULL 时不写任何内容：堆和世界都不变。对句柄调用时，只写句柄自己的块。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 对句柄调用时的返回值，以及由此得到的字节、位置和标志：功能目标 `Goal.gzoffset`（不在计划内；已有定理证明它）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzoffset"><summary>完整返回条件与边界</summary>

**后置条件：** 返回转换为 `z_off_t` 的物理偏移，采用相同缓冲处理，不移动描述符。

**错误与边缘情形：** 相同的 NULL、模式错误和系统查询失败返回 -1。
在较窄构建中，结果超出 `z_off_t` 也返回 -1；默认构建没有更窄的偏移范围。

</details>

## gzeof

查询读取句柄是否曾尝试读取可用数据之后的内容。

```c
int ZEXPORT gzeof(gzFile file);
```

### 返回值与后续调用 {#api-gzeof-returns}

**返回值类型。** `int` — 越过 EOF 标志

它查询是否尝试读取了可用数据之后的内容，不发起读取。读到最后一个字节并不一定设置该标志。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `1`<br>**已尝试越过末尾读取** | 读取句柄的越过 EOF 标志已设置。 | 按需查询 gzerror，区分普通末尾与截断。若文件之后增长，可清除错误后再次尝试读取。 |
| `0`<br>**未设置越过末尾标志** | 读取句柄的标志未设置，或参数是写入句柄／NULL；成功压回和清除错误也会清除此标志。 | 不要据此认定仍有数据或没有错误；读取失败或停顿时另查 gzerror。 |

### 调用条件与效果 {#api-gzeof-contract}

**定义域：** 受限定义域：活跃句柄，包括 NULL 拒绝情形。

**效果：** 只读句柄查询。

**前置条件：** 非 NULL 句柄满足共享要求。

**证明目标。**

- **目标。** `Goal.gzeof_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzeof_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求（这个调用没有参数条件）：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）。
- **无条件覆盖。** 历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界。
- **保证。**
    - *返回。* 句柄为 NULL 时调用返回 `0`。对句柄调用时，调用在每个世界里都返回。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。
    - *写入。* 句柄为 NULL 时不写任何内容：堆不变。这个函数的翻译不接受世界，所以无从改变世界。对句柄调用时，只写句柄自己的块。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 对句柄调用时的返回值，以及由此得到的字节、位置和标志：功能目标 `Goal.gzeof`（不在计划内；已有定理证明它）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzeof"><summary>完整返回条件与边界</summary>

**后置条件：** 返回读取句柄的越过 EOF 标志，写入句柄则返回零。
不读取文件、不分配、不刷新，也不改变状态。

**错误与边缘情形：** NULL 返回零。消费最后一个字节不一定设置该标志。
零结果不排除读取错误或非阻塞停顿。使用 `gzerror` 区分这些情形。
成功字节回退和清除错误会清除此标志；后续读取可再次设置它。

</details>

## gzdirect

报告句柄是否使用透明数据。

```c
int ZEXPORT gzdirect(gzFile file);
```

### 返回值与后续调用 {#api-gzdirect-returns}

**返回值类型。** `int` — 透明模式标志，不是错误状态

返回当前透明模式标志；1 不保证格式检测已完成。新读取句柄的查询可分配内存并读取输入。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `1`<br>**透明标志已设置** | 普通读取句柄检测到非 gzip 或空输入，或写入句柄使用 T 模式；普通读取句柄的初始标志在检测待定或检查失败时也可保持为 1。 | 结合后续读取与 gzerror 解释结果；不要由此认定格式已完成识别或检查期间没有错误。 |
| `0`<br>**未报告透明模式** | 当前透明标志未设置，例如 gzip 模式或 G 读取句柄；NULL 也返回零。 | 对有效句柄按需查询 gzerror；模式标志本身不报告检查的分配或 I/O 失败。 |

**判读要点。**

- 先调用 gzbuffer 设置所需大小。检查可消费待处理跳过涉及的透明缓冲字节，但不向调用者交付数据。

### 调用条件与效果 {#api-gzdirect-contract}

**定义域：** 受限定义域：活跃读取／写入句柄。

**效果：** 有状态格式检查；可能分配、读取并记录错误。

**前置条件：** 满足共享句柄要求。先设置任何所需的缓冲区大小。

**证明目标。**

- **目标。** `Goal.gzdirect_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzdirect_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求（这个调用没有参数条件）：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）。
- **无条件覆盖。** 历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界；每一种分配结果。
- **保证。**
    - *返回。* 句柄为 NULL 时调用返回 `0`。对句柄调用时，调用在每个世界里都返回。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。
    - *写入。* 句柄为 NULL 时不写任何内容：堆和世界都不变。对句柄调用时，只写句柄自己的块。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 对句柄调用时的返回值，以及由此得到的字节、位置和标志：功能目标 `Goal.gzdirect`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzdirect"><summary>完整返回条件与边界</summary>

**后置条件：** 最终模式为透明模式时恰好返回 1，否则为零。
新的普通读取句柄可检查输入以作决定。写入句柄报告是否选择了 `T`。
检查可将待处理跳过应用于新缓冲的透明字节，但不向调用者交付数据。

**错误与边缘情形：** NULL 返回零。普通空输入是透明输入。`G` 读取句柄报告零。
格式检查可能分配或 I/O 失败并记录错误；返回的模式标志本身不报告该失败。
非阻塞输入可使检测保持待处理。按需检查 `gzerror`。

</details>

## gzerror

读取句柄的当前错误码和消息。

```c
const char * ZEXPORT gzerror(gzFile file, int *errnum);
```

### 返回值与后续调用 {#api-gzerror-returns}

**返回值类型。** `const char *` — 借用的消息指针；错误码写入可选输出参数

返回值是消息地址，当前 zlib 错误码通过非 NULL 的 errnum 写出。空消息和错误码是两个不同通道。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `""`<br>**没有保存的消息文本** | 有效句柄没有消息，且当前码不是 Z_MEM_ERROR；提供 errnum 时仍写入当前错误码。 | 读取 `*errnum` 判断状态；不要仅由空字符串推断 Z_OK。 |
| `"out of memory"`<br>**静态内存不足消息** | 有效句柄保存的错误码为 Z_MEM_ERROR，提供 errnum 时写入该码。 | 按内存失败处理；不要修改或释放此静态字符串。 |
| `message`<br>**借用的诊断消息** | 有效句柄保存了非 Z_MEM_ERROR 的诊断字符串，提供 errnum 时写入相应当前码。 | 按 `*errnum` 处理原因。需要保留消息时，在错误改变、清除错误或关闭前复制；不要修改或释放原字符串。 |
| `NULL`<br>**没有可查询的句柄** | 句柄为 NULL；不写入 errnum。 | 不要解引用返回值，也不要把原有 `*errnum` 当成本次查询结果。 |

**判读要点。**

- 常见保存码：Z_OK 无错误；Z_DATA_ERROR 数据损坏；Z_BUF_ERROR 截断；Z_MEM_ERROR 分配失败；Z_ERRNO 系统失败；Z_STREAM_ERROR 请求错误。非阻塞停顿也可记录 Z_ERRNO。
- 查询不分配、不清除错误。有效句柄一旦关闭，即使关闭报告失败，也不能再查询。

### 调用条件与效果 {#api-gzerror-contract}

**定义域：** 受限定义域：活跃句柄和可选可写错误码输出。

**效果：** 只读句柄查询；提供 `errnum` 时写入 `*errnum`。

**前置条件：** 非 NULL `errnum` 指向与拥有的状态分离的可写 `int`。
满足共享句柄要求。

**证明目标。**

- **目标。** `Goal.gzerror_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzerror_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有三个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）；以及关于调用所返回字符串的一个子句。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）；
    2. 参数条件（`GzArguments`）：`errnum` 为 NULL，或者覆盖 4 个可写字节且在句柄自己的块之外（`GzRange`）。
- **无条件覆盖。** `errnum` 为 NULL；历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界。
- **保证。**
    - *返回。* 句柄为 NULL 时，不论 `errnum` 取什么值，调用都返回 `NULL`，并且不写 `*errnum`。对句柄调用时，调用在每个世界里都返回。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。调用返回的指针，在调用后的堆里是一个可读的、以 NUL 结尾的字符串。
    - *写入。* 句柄为 NULL 时不写任何内容：堆不变。这个函数的翻译不接受世界，所以无从改变世界。对句柄调用时，只写句柄自己的块，以及 `errnum` 处的 4 个字节。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 对句柄调用时的返回值，以及由此得到的字节、位置和标志：功能目标 `Goal.gzerror`（不在计划内；已有定理证明它）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzerror"><summary>完整返回条件与边界</summary>

**后置条件：** `errnum` 非 NULL 时存储当前错误码。
返回借用的消息指针：无消息时为空字符串，`Z_MEM_ERROR` 时为静态
`"out of memory"`（内存不足），否则为拥有的诊断字符串。不分配，句柄状态不变。

**错误与边缘情形：** NULL 句柄返回 NULL，不写 `errnum`。
调用者不得释放或修改返回字符串。错误改变、`gzclearerr` 或关闭可使拥有的消息失效；
需要保留时须事先复制。关闭后不得作此查询，包括最终关闭失败的情形。

</details>

## gzclearerr

清除已记录错误信息，并重新启用读取句柄的 EOF 检测。

```c
void ZEXPORT gzclearerr(gzFile file);
```

### 返回值与后续调用 {#api-gzclearerr-returns}

**返回值类型。** `void` — 无返回值的状态重置

清除保存的错误消息和错误码；读取句柄还清除输入 EOF 与越过 EOF 标志。它不报告成功码，也不重建编解码器。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `void`<br>**清除错误，或 NULL 空操作** | 有效句柄设为 Z_OK 并移除旧消息；位置、待处理跳过、缓冲数据和编解码器状态保留。NULL 不做任何事。 | 旧的借用消息可能失效。仅在输入和保留状态允许时再次读取或继续处理；清除错误本身不修复文件或保证重试成功。 |

### 调用条件与效果 {#api-gzclearerr-contract}

**定义域：** 受限定义域：活跃句柄，包括 NULL 空操作情形。

**效果：** 有状态错误重置，可能释放消息内存。

**前置条件：** 非 NULL 句柄满足共享要求。

**证明目标。**

- **目标。** `Goal.gzclearerr_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzclearerr_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次调用（`GzCallSafety`，即[序列目标](#the-safety-goal)的调用子句限制到这个函数的调用上）。
- **适用条件。** 拒绝子句没有条件。对句柄的调用要求（这个调用没有参数条件）：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）。
- **无条件覆盖。** 历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界。
- **保证。**
    - *返回。* 句柄为 NULL 时调用返回。对句柄调用时，调用在每个世界里都返回。
    - *状态。* 对句柄的调用返回之后：世界良构，打开的描述符集合不变（`FdsKept`），句柄保持其不变量、模式和描述符（`GzStepPost`、`GzInv`）。
    - *写入。* 句柄为 NULL 时不写任何内容：堆不变。这个函数的翻译不接受世界，所以无从改变世界。对句柄调用时，只写句柄自己的块。
    - *分配。* 对句柄调用时，按句柄计的精确的分配账本（`LiveChange`）。
- **不在本目标内。** 调用清除句柄的哪些标志：功能目标 `Goal.gzclearerr`（不在计划内；已有定理证明它）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzclearerr"><summary>完整返回条件与边界</summary>

**后置条件：** 将错误设为 `Z_OK`，移除旧诊断消息。
对读取句柄，清除输入 EOF 和越过 EOF 标志。
保留位置、待处理跳过、缓冲数据和编解码器状态；不进行文件读写。

**错误与边缘情形：** NULL 是空操作。清除错误不会修复文件，也不保证重试成功。
它允许再次尝试读取增长中的文件。借用的消息可能失效。
结束失败和部分读取之后重试会得到什么，仍然**尚未由证明确认**，清除错误本身并不解决这个问题；
重试是安全的，这一点属于安全目标。

</details>

## gzclose

关闭读取句柄，或完成输出后关闭写入句柄。

```c
int ZEXPORT gzclose(gzFile file);
```

### 返回值与后续调用 {#api-gzclose-returns}

**返回值类型。** `int` — zlib 关闭状态码

状态码来自按句柄模式选择的读取或写入关闭。即使最终 I/O 报告失败，有效句柄也会销毁。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**句柄已释放** | 读取句柄关闭成功且无已记录截断，或写入句柄最终工作与描述符关闭成功。此结果不重报此前所有错误。 | 句柄已销毁。不得查询、复用或重试关闭。 |
| `Z_BUF_ERROR`<br>**截断后读取句柄已释放** | 所选读取句柄关闭发现已记录截断，且描述符关闭成功。 | 句柄已销毁。不得查询、复用或重试关闭。输入已被记录为不完整。 |
| `Z_MEM_ERROR`<br>**写入句柄最终分配失败** | 写入句柄零填充／结束工作返回内存错误，且描述符关闭未覆盖此结果。 | 句柄已销毁。不得查询、复用或重试关闭。未确认最终输出完整。 |
| `Z_ERRNO`<br>**最终系统操作失败** | 写入句柄最终输出报告系统错误，或读取／写入句柄描述符关闭失败。关闭失败优先。 | 句柄已销毁。不得查询、复用或重试关闭。处理系统失败时不得再使用旧句柄。 |
| `Z_STREAM_ERROR`<br>**结束失败后写入句柄已销毁** | 选择了有效写入句柄，最终工作报告 Z_STREAM_ERROR；描述符关闭成功。 | 句柄已销毁。不得查询、复用或重试关闭。不能把此结果误作写入句柄仍存活的拒绝。 |
| `Z_STREAM_ERROR`<br>**未提供句柄** | 参数为 NULL。 | 此调用未取得句柄，无需清理或重试关闭。 |

**判读要点。**

- 读取诊断须在关闭前检查。有效句柄一经关闭，即使关闭返回错误，也不能再调用 gzerror。

### 调用条件与效果 {#api-gzclose-contract}

**定义域：** 受限定义域：活跃句柄，恰好关闭一次。

**效果：** 有状态最终 I/O、释放内存并关闭描述符。

**前置条件：** 满足共享句柄要求。后续不再使用此句柄。

**证明目标。**

- **目标。** `Goal.gzclose_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzclose_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次关闭（`GzCloseCallSafety`，即[序列目标](#the-safety-goal)的关闭子句限制到这个函数上）。
- **适用条件。** 拒绝子句没有条件。对句柄的关闭要求（没有参数条件，也不需要读取预算）：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）。
- **无条件覆盖。** 历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界，包括系统的 `close` 报告失败的世界；每一种分配结果。
- **保证。**
    - *返回。* 句柄为 NULL 时调用返回 `Z_STREAM_ERROR`。对句柄调用时，调用在每个世界里都返回。对句柄的返回码不作陈述。
    - *状态。* 对句柄调用时，句柄不复存在：它的记录被移除，世界良构，句柄的描述符编号不是负数时，调用之后这个描述符不再打开（即使系统的 `close` 报告失败也是如此），其他每个描述符是否打开都与调用前相同（`GzReleased`）。`gzclose` 两种模式都接受，所以它从不拒绝一个句柄。
    - *写入。* 句柄为 NULL 时不写任何内容：堆和世界都不变。对句柄调用时，只写句柄自己的块。
    - *分配。* 对句柄调用时，恰好释放句柄自己的块（包括句柄记录），并且不分配任何块（`LiveChange`）。
- **不在本目标内。** 在关闭它的那次调用之后再使用句柄：历史已经结束，没有目标覆盖这种使用。返回码，以及关闭之前哪些字节到达文件：功能目标 `Goal.gzclose`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzclose"><summary>完整返回条件与边界</summary>

**后置条件：** 分派至 `gzclose_r` 或 `gzclose_w`。
有效句柄被销毁，拥有的存储被释放，并尝试关闭描述符。
写入句柄关闭还会尝试待处理零填充和完成缓冲输出。

**错误与边缘情形：** NULL 返回 `Z_STREAM_ERROR`。适用下述按模式区分的结果。
最终 I/O 错误不会让有效句柄保持存活：不得重试关闭，也不得随后查询其错误。
模式错误的拒绝与有效写入句柄的最终处理失败不同；后者也可能在销毁句柄后报告
`Z_STREAM_ERROR`。

</details>

## gzclose_r

释放读取句柄并关闭其描述符，不继续解压。

```c
int ZEXPORT gzclose_r(gzFile file);
```

### 返回值与后续调用 {#api-gzclose_r-returns}

**返回值类型。** `int` — zlib 关闭状态码

状态码报告读取句柄清理与描述符关闭；此前已记录的截断有单独结果。每次接受的读取句柄关闭都会销毁句柄。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**读取句柄已释放** | 描述符关闭成功，且已记录错误不是 Z_BUF_ERROR。不返回此前其他读取错误。 | 句柄已销毁。不得查询、复用或重试关闭。此结果不验证未读输入。 |
| `Z_BUF_ERROR`<br>**截断后已释放** | 关闭读取句柄时已记录 Z_BUF_ERROR，且描述符关闭成功。 | 句柄已销毁。不得查询、复用或重试关闭。应将已记录的 gzip 截断视为输入不完整，不能视为可重试的活跃读取句柄状态。 |
| `Z_ERRNO`<br>**描述符关闭失败** | 操作系统描述符关闭失败；其优先级高于已记录的截断。 | 句柄已销毁。不得查询、复用或重试关闭。处理相关系统失败时，不得再对旧句柄调用 gzip API。 |
| `Z_STREAM_ERROR`<br>**未关闭读取句柄** | 参数为 NULL 或活跃写入句柄。不释放写入句柄的资源。 | NULL 没有可关闭的句柄。活跃写入句柄仍由调用者拥有，应改用 gzclose_w 或 gzclose 关闭。 |

**判读要点。**

- 若需要此前读取诊断，应在关闭前检查 gzerror。关闭不进行最终读取或解压来检查未消费输入。

### 调用条件与效果 {#api-gzclose_r-contract}

**定义域：** 受限定义域：读取句柄；包括 NULL 和写入句柄的拒绝。

**效果：** 有状态释放内存并关闭描述符。

**前置条件：** 活跃读取句柄满足共享要求，且只关闭一次。

**证明目标。**

- **目标。** `Goal.gzclose_r_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzclose_r_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次关闭（`GzCloseCallSafety`，即[序列目标](#the-safety-goal)的关闭子句限制到这个函数上）。
- **适用条件。** 拒绝子句没有条件。对句柄的关闭要求（没有参数条件，也不需要读取预算）：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）。
- **无条件覆盖。** 历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界，包括系统的 `close` 报告失败的世界；每一种分配结果。
- **保证。**
    - *返回。* 句柄为 NULL 时调用返回 `Z_STREAM_ERROR`。对句柄调用时，调用在每个世界里都返回。对句柄的返回码不作陈述。
    - *状态。* 句柄不是读句柄时，调用拒绝：堆和世界都不变，句柄保持原样。否则句柄不复存在：它的记录被移除，世界良构，句柄的描述符编号不是负数时，调用之后这个描述符不再打开（即使系统的 `close` 报告失败也是如此），其他每个描述符是否打开都与调用前相同（`GzReleased`）。
    - *写入。* 句柄为 NULL 时以及拒绝时不写任何内容：堆和世界都不变。否则只写句柄自己的块。
    - *分配。* 拒绝时没有分配变化。否则恰好释放句柄自己的块（包括句柄记录），并且不分配任何块（`LiveChange`）。
- **不在本目标内。** 在关闭它的那次调用之后再使用句柄：历史已经结束，没有目标覆盖这种使用。返回码，以及关闭之前哪些字节到达文件：功能目标 `Goal.gzclose_r`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzclose_r"><summary>完整返回条件与边界</summary>

**后置条件：** 结束已分配的 inflate 状态，释放拥有的缓冲区／消息／路径和状态，
并尝试关闭描述符。即使关闭描述符失败，句柄也已销毁。

**错误与边缘情形：** 通常返回 `Z_OK`；若关闭时记录的错误为截断，返回 `Z_BUF_ERROR`。
描述符关闭失败返回 `Z_ERRNO`，优先级更高。不返回此前其他读取错误：
应在关闭前查询 `gzerror`。NULL 或写入句柄返回 `Z_STREAM_ERROR`，
不关闭或释放该写入句柄。不进行最终读取来验证未消费输入。

</details>

## gzclose_w

完成缓冲输出、释放写入句柄并关闭描述符。

```c
int ZEXPORT gzclose_w(gzFile file);
```

### 返回值与后续调用 {#api-gzclose_w-returns}

**返回值类型。** `int` — zlib 关闭状态码

状态码报告最终零填充／结束工作及描述符关闭。一旦接受活跃写入句柄，即使最终输出失败，清理也会销毁它。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**写入句柄已结束并释放** | 待处理零填充、最终输出及描述符关闭成功。最终工作成功时，不会自动返回此前错误。 | 句柄已销毁。不得查询、复用或重试关闭。 |
| `Z_MEM_ERROR`<br>**最终工作分配失败** | 最终零填充或结束工作报告 Z_MEM_ERROR，包括缓冲区／编解码器初始化或诊断消息分配失败，且描述符关闭未覆盖此结果。 | 句柄已销毁。不得查询、复用或重试关闭。未确认最终输出完整。 |
| `Z_ERRNO`<br>**最终系统操作失败** | 最终写入以 Z_ERRNO 失败，或描述符关闭失败。描述符关闭失败优先于此前任何最终处理结果。 | 句柄已销毁。不得查询、复用或重试关闭。应在外部处理系统失败；此码不表示存在可复用的 gzip 句柄。 |
| `Z_STREAM_ERROR`<br>**结束失败后写入句柄已释放** | 有效写入句柄进入最终压缩工作，且该工作报告 Z_STREAM_ERROR；描述符关闭成功。 | 句柄已销毁。不得查询、复用或重试关闭。这与清理前拒绝读取句柄不同。 |
| `Z_STREAM_ERROR`<br>**未关闭写入句柄** | 参数为 NULL 或活跃读取句柄。读取句柄未被销毁。 | NULL 无需清理。活跃读取句柄仍须通过 gzclose_r 或 gzclose 关闭一次。 |

**判读要点。**

- 未使用的 gzip 写入句柄通常输出空成员；未使用的透明写入句柄不输出载荷。关闭成功不解决契约中此前结束失败恢复的注意事项。

### 调用条件与效果 {#api-gzclose_w-contract}

**定义域：** 受限定义域：写入句柄；包括 NULL 和读取句柄的拒绝。

**效果：** 有状态输出，可能分配内存，随后释放内存并关闭描述符。

**前置条件：** 活跃写入句柄满足共享要求，且只关闭一次。

**证明目标。**

- **目标。** `Goal.gzclose_w_safety`（[Safety/GzCalls.lean](../../../ZlibF/Spec/Safety/GzCalls.lean)）；必需。定理：`ZlibF.Spec.Public.GzCallSafetyProof.gzclose_w_safety`（[public-gz-call-safety.lean](../../../ZlibF/Proof/public-gz-call-safety.lean)）。这个目标有两个子句：对 NULL 句柄的拒绝；对句柄的一次关闭（`GzCloseCallSafety`，即[序列目标](#the-safety-goal)的关闭子句限制到这个函数上）。
- **适用条件。** 拒绝子句没有条件。对句柄的关闭要求（没有参数条件，也不需要读取预算）：
    1. `file` 是一个带有历史的句柄（`GzHistory`，见[安全目标](#the-safety-goal)一节）。
- **无条件覆盖。** 历史能让句柄处于的每一种状态，读句柄或写句柄，有或没有待处理的错误；每个文件系统世界，包括系统的 `close` 报告失败的世界；每一种分配结果。
- **保证。**
    - *返回。* 句柄为 NULL 时调用返回 `Z_STREAM_ERROR`。对句柄调用时，调用在每个世界里都返回。对句柄的返回码不作陈述。
    - *状态。* 句柄不是写句柄时，调用拒绝：堆和世界都不变，句柄保持原样。否则句柄不复存在：它的记录被移除，世界良构，句柄的描述符编号不是负数时，调用之后这个描述符不再打开（即使系统的 `close` 报告失败也是如此），其他每个描述符是否打开都与调用前相同（`GzReleased`）。
    - *写入。* 句柄为 NULL 时以及拒绝时不写任何内容：堆和世界都不变。否则只写句柄自己的块。
    - *分配。* 拒绝时没有分配变化。否则恰好释放句柄自己的块（包括句柄记录），并且不分配任何块（`LiveChange`）。
- **不在本目标内。** 在关闭它的那次调用之后再使用句柄：历史已经结束，没有目标覆盖这种使用。返回码，以及关闭之前哪些字节到达文件：功能目标 `Goal.gzclose_w`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="gzclose_w"><summary>完整返回条件与边界</summary>

**后置条件：** 尝试待处理零填充和 `Z_FINISH`，随后释放拥有的编解码器状态、
缓冲区／消息／路径和句柄，并尝试关闭描述符。即使输出失败，也会执行清理。
未使用的 gzip 写入句柄通常输出一个空成员；未使用的透明写入句柄不输出载荷。

**错误与边缘情形：** 最终工作成功时返回 `Z_OK`。
定位填充或结束失败返回相应错误，包括 `Z_MEM_ERROR`、`Z_ERRNO` 或 `Z_STREAM_ERROR`；
描述符关闭失败以 `Z_ERRNO` 优先返回。
如果最终工作成功，不会自动返回此前错误。NULL 或读取句柄返回 `Z_STREAM_ERROR`，
不销毁读取句柄。有效写入句柄即使结果为 `Z_STREAM_ERROR` 也已销毁。
关闭成功不解决下面的结束失败恢复注意事项。

</details>

## 范围与源码注意事项

有文档的错误码本身并不说明重试或恢复是安全的。后续调用的安全性由[安全目标](#the-safety-goal)陈述：
任何一次调用返回之后，无论结果如何，下一次调用仍然安全。这些路径上有四个源码问题由补丁修复。
前三个已用真实 C 在 sanitizer 下复现；第四个只按 C 标准的字面是未定义行为。
本页的契约和安全目标都针对打过补丁的源码（每个问题及其上游状态见 `patches/README.md`）：

| 情形 | 未打补丁的 C | 补丁 |
| --- | --- | --- |
| 一开始就 `gzungetc`（位置为 -1）之后再 `gzseek` | 范围检查中有符号溢出。 | 0002 |
| 透明读取时 `read` 先交付一些字节然后失败 | 读函数通过过期的缓冲指针消费这些部分字节：越界读。 | 0003 |
| 读或写时位置越过 `GZ_OFF_MAX` | 位置发生有符号溢出。 | 0004，本地补丁，尚待提交上游 |
| 对从未写入或已悬空的缓冲指针作零偏移推进 | 对不确定或悬空的指针做算术。 | 0005，本地补丁，尚待提交上游 |

部分读取之后、压缩器未采用的参数更改之后，或结束失败之后，恢复会得到什么（哪些字节到达文件、报告什么位置），
属于功能行为。它仍然**尚未由证明确认**，并且不在计划的证明目标之内。

差分测试提供的是翻译忠实性的证据，不是证明。

私有辅助函数、旧式固定参数的 `gzprintf`，
以及 Windows 错误字符串辅助函数，不在此增加公开入口。
源文件与具体目标的链接位于函数条目之前。

[返回 API 手册](README.md) · [契约约定](contracts.md)

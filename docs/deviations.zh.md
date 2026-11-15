<!-- source-sha256: 49afc23424595d8c6cae18d0a955e509f4c4f81c6ad78748480e88d180b58e9b -->
# 偏离记录：一次调用要满足什么

本页写给调用 zlib 的人，回答一个问题：我的调用被安全定理覆盖了吗？下面的核对清单按函数族、用 C 的说法作答。清单之后的各表给出每一行背后精确的 Lean 前提、陈述它的目标，以及真实的 C 在前提之外会怎样。

满足自己那个函数的各行，调用就被覆盖。不满足的调用不被覆盖：既没有被证明安全，也没有被断言不安全。

- **列出了什么。** 必需的安全目标中每一条比 `zlib.h` 更窄的前提，以及读者容易漏看的前提。只是重复 `zlib.h` 的前提写在目标的 Lean 命题里，以命题为准；每个函数对应哪个目标，见[按函数查覆盖情况](coverage.md)。
- **结果单元。** 有七个函数通过指针写出结果，而翻译把这个指针表示成一个值，不是内存：四个 `compress*` 函数的 `destLen`，两个 `GetDictionary` 函数的 `dictLength`，以及 `deflatePending` 和 `deflateUsed` 的结果指针。它们的目标对这个单元没有前提，对它的内存也什么都没说。核对清单给出调用者必须遵守的那一行，并注明“没有 Lean 谓词”。细节见[“结果单元”](#stream-calls-inflate-and-deflate)和[“整缓冲区压缩”](#whole-buffer-utilities-and-checksums)两行。
- **这里没有列什么。** 调用者无能为力的、对模型的条件，以及功能定理和模型定理的限制：它们在[模型的限制](model-limits.md)中。被信任而没有被证明的东西在[可信基础](trusted-base.md)中。
- **证据。** 已知真实的 C 在某条前提之外会出错时，该行给出复现的链接；[sanitizer 报告](sanitizer-reports.md)列出全部复现。

比 `zlib.h` 更窄的前提，也写在陈述它的 Lean 定义的文档注释里。前提从来不是丢掉一个失败的公开情形的理由：目标错了，就连同反例一起改正；翻译或运行时错了，就在那一层改正（[验证策略](anti-cheating.md)）。

## 给调用者的核对清单

每一行末尾是陈述它的 Lean 谓词；没有谓词陈述的行会注明。只有写明允许 `NULL` 的地方才允许 `NULL`。

**每一次调用**

- 库是默认的 x86_64 Linux 构建：LP64、静态链接，由固定版本的源码加五个补丁编译而成。
- 每个 `z_stream` 的 `zalloc` 和 `zfree` 都是 `Z_NULL`，于是 zlib 使用它的默认分配器（`DefaultOrNull`）。自定义分配器不被覆盖。`malloc` 失败是被覆盖的。
- 内存中没有任何单个对象达到或超过 2^63 字节（`ByteObjectsFit`）。这是 LP64 下单个对象的上限 `PTRDIFF_MAX`；它不限制内存总量，也不限制流的长度。

**`inflateInit`、`inflateInit2`、`deflateInit`、`deflateInit2`**（`zlib.h` 的宏以及宏背后的函数）

- `strm` 是 `NULL`，或者指向一个 `zalloc` 和 `zfree` 都为 `Z_NULL` 的 `z_stream`（`InitArguments`）。
- 除此之外没有要求。`z_stream` 的其他字段，包括 `state`，可以是任何值。`version`（宏会替你传）是 `NULL` 或一个可读的字符串，`stream_size` 可以是任何值：不匹配时调用返回错误码，并且不留下任何分配。每个 `level`、`windowBits`、`memLevel` 和 `strategy` 都被覆盖。

这就回答了最常见的那种调用：

```c
z_stream s;
s.zalloc = Z_NULL;
s.zfree = Z_NULL;
s.opaque = Z_NULL;
int rc = inflateInit(&s);   /* covered by Goal.inflateInit__safety */
```

这次调用被覆盖，结构体不必事先清零。它返回 `Z_OK` 时，定理还说这个流是可达的，所以此后在 `s` 上的每次调用都被下面的目标覆盖。对代码没有设置的字段，模型怎样处理，见[注 1](#note-1-init-and-unset-fields)。

**`inflate`、`deflate`、`deflateParams`**

- `next_in` 是 `NULL`，或指向 `avail_in` 个可读字节。`next_out` 是 `NULL`，或指向 `avail_out` 个可写字节（`StreamBuffers`）。
- 输入范围与输出范围不重叠，并且都不在 zlib 为这个流分配的内存里（`StreamBuffers`）。
- 两次调用之间，你只改 `z_stream` 的 `next_in`、`avail_in`、`next_out` 和 `avail_out`，以及不是 zlib 为这个流分配的内存（`Rebuffer`）。
- 如果挂接了 `gz_header`，下面“gzip 头部”各行成立（`ActiveHeader`）。

**`inflateSync`**

- `next_in` 是 `NULL` 且 `avail_in == 0`，或者指向流自身内存之外的 `avail_in` 个可读字节（`StreamArguments`）。

**字典：`inflateSetDictionary`、`deflateSetDictionary`、`inflateGetDictionary`、`deflateGetDictionary`**

- 字典指针是 `NULL`，或者是流自身内存之外的一个缓冲区：两个 `Set` 调用要求它有 `dictLength` 个可读字节，两个 `Get` 调用要求它对返回的那些字节可写（`CallerRange`）。`zlib.h` 说 32768 字节对 `Get` 调用总是够用。
- 对两个 `Get` 调用，`dictLength` 是 `NULL`，或者指向你自己的一个 `uInt` 变量，它与字典缓冲区、`z_stream` 和流自身的内存都不重叠。这一行没有 Lean 谓词陈述：翻译把长度作为值返回（见[“结果单元”](#stream-calls-inflate-and-deflate)一行）。

**读取 gzip 头部：`inflateGetHeader`**

- `head` 不是 `NULL`。它的 `extra`、`name` 和 `comment` 各自是 `NULL`，或者分别有 `extra_max`、`name_max`、`comm_max` 个可写字节。这个记录和这些缓冲区都在流自身的内存之外（`HeaderMemory`）。
- 此后在这个流上的每次 `inflate` 调用时，记录及其缓冲区都仍然有效，头部读完之后也是如此，直到一次成功的 `inflateReset` 或 `inflateReset2`，或者 `inflateEnd`（`ActiveHeader` 中的 `HeaderMemory`）。
- `inflate` 还在读头部期间，`extra` 缓冲区不与尚未读取的输入重叠，你也不调低记录中的 `extra_len`（`InflateHeaderProgress`）。

**写出 gzip 头部：`deflateSetHeader`、`deflatePrime`、`deflateBound`**

- `deflateSetHeader` 和 `deflatePrime` 在 init 或 reset 之后的第一次 `deflate` 调用之前调用，这是 `zlib.h` 的规定（`DeflateNotStarted`）。
- `head` 是 `NULL`，或者是流自身内存之外的一个记录：它的 `extra` 是 `NULL` 或有 `extra_len` 个可读字节，`name` 和 `comment` 各自是 `NULL` 或以 NUL 结尾的字符串（`HeaderMemory`）。
- 从第一次 `deflate` 调用到头部写完为止，记录及其缓冲区保持有效，你不缩短任何字段，也不把它改成 `NULL`；输入、输出、extra 字段、name 和 comment 两两不重叠；三个头部缓冲区在流自身的内存之外（`DeflateHeaderApart`、`DeflateHeaderProgress`）。此后可以释放它们。
- `deflateBound` 和 `deflateBound_z` 不论何时调用都会读取已设置的头部，所以调用它们时记录及其缓冲区也必须有效（`DeflateHeaderLive`）。

**`inflateCopy`、`deflateCopy`**

- `source` 是下一条所说的那种流，`dest` 指向一个不是 `source` 的 `z_stream`（`source ≠ dest`）。

**其余流调用**（`inflateEnd`、`deflateEnd`、`inflateReset`、`inflateReset2`、`inflatePrime`、`inflateMark`、`deflateReset`、`deflateTune`、`deflatePending`、`deflateUsed`）

- 对参数没有前提。流须是某次 init 或复制返回 `Z_OK` 得到的，并且一直按这份清单使用。
- `deflatePending` 和 `deflateUsed`：每个结果指针（`pending`、`bits`）是 `NULL`，或者指向你自己的一个变量，它与 `z_stream` 和流自身的内存都不重叠。这一行没有 Lean 谓词陈述：翻译把结果作为值返回（见[“结果单元”](#stream-calls-inflate-and-deflate)一行）。

**`NULL` 流或不一致的流**

- `NULL` 流指针、`End` 之后或 init 失败之后的 `z_stream`，以及存活 `z_stream` 的结构体副本，都会被以 `Z_STREAM_ERROR` 拒绝，什么也不改变。这一点已对[注 2](#note-2-refused-streams) 所列的函数证明。
- 不被覆盖：分配器已设置、而 `state` 是过期指针或垃圾指针的 `z_stream`。

**`compress`、`compress2`、`compress_z`、`compress2_z`**

- `source` 有 `sourceLen` 个可读字节，`dest` 有 `*destLen` 个可写字节，两者不重叠（`CompressArguments`）。
- `compress` 和 `compress2` 的 `destLen` 不能是 `NULL`（`CompressArguments`）。
- `destLen` 指向你自己的一个变量，它与 `source` 和 `dest` 都不重叠。这一行没有 Lean 谓词陈述：翻译把 `*destLen` 当作值传入（见[“整缓冲区压缩”](#whole-buffer-utilities-and-checksums)一行）。

**`uncompress`、`uncompress2`、`uncompress_z`、`uncompress2_z`**

- `source` 在源长度范围内可读，`dest` 有 `*destLen` 个可写字节。`destLen`，以及带 `2` 的两个函数的 `sourceLen`，各自指向八个可读可写的字节。
- `source`、`dest` 和各个长度变量两两不重叠（`UtilitySeparation`）。`uncompress` 和 `uncompress2` 的长度指针不能是 `NULL`。

**校验和与查询**

- `adler32`、`adler32_z`：只有 `len == 0` 时 `buf` 才可以是 `NULL`；否则它有 `len` 个可读字节（`AdlerBufferBytes`）。
- `crc32`、`crc32_z`：`buf` 是 `NULL`，或有 `len` 个可读字节。
- `crc32_combine_op`：`op` 是 `crc32_combine_gen` 或 `crc32_combine_gen64` 返回的值，这是 `zlib.h` 的规定。
- 各个组合函数、`compressBound`、`compressBound_z`、`zlibVersion` 和 `zlibCompileFlags` 没有前提。

**回调解码器：`inflateBackInit`、`inflateBack`、`inflateBackEnd`**

- 调用 `inflateBackInit` 时：`zalloc` 和 `zfree` 是 `Z_NULL`，`z_stream` 的 `state` 字段是 `NULL`；`windowBits` 在 8 到 15 之间；`window` 不是 `NULL`，有 `2^windowBits` 个可写字节，并且是一个字节数组或其中一段，而不是结构体里的字节字段（`InitDomain`、`BackSafeReachable.init`）。
- 你的 `in` 和 `out` 函数会返回，只写你自己的内存，不写窗口、`z_stream` 和 zlib 的状态。`in` 交出的每一块输入都可读，是一个字节数组或其中一段，不与窗口重叠，并且在下一次 `in` 调用之前保持可读（`CallbackProtocol`、`BackPlatform`）。
- 一次 `inflateBack` 调用总共得到的输入少于 2^48 字节（`inputBound`）。
- 两次 `inflateBack` 调用之间，你不写窗口，并且只改 `z_stream` 的四个缓冲区字段。

**gzip 文件：各个 `gz*` 函数**

- `path` 和 `mode` 是 `NULL` 或以 NUL 结尾的字符串（`GzOpenSafe`、`GzDopenSafe`）。
- 传给 `gzread`、`gzfread`、`gzgets`、`gzwrite`、`gzfwrite` 或 `gzputs` 的缓冲区、`gzerror` 的 `errnum` 指针，以及 `gzprintf` 的格式串和每个 `%s` 参数，都是你自己的内存。尤其不要把 `gzerror` 返回的字符串再传回同一个文件上的调用（`GzRange`、`GzArguments`）。
- `gzputs` 的参数是以 NUL 结尾的字符串。
- `gzprintf` 的格式串只用整数、字符和字符串转换；不用 `%f`、`%p`、`%n`、`h` 或 `hh` 修饰符，也不用 `*` 宽度（`Formatted`）。
- 两次调用之间，你不写 zlib 为这个文件分配的内存（`GzCallerFrame`）。
- `gzread`、`gzfread`、`gzgetc`、`gzgetc_`、`gzgets` 和 `gzungetc` 的终止，是在文件描述符还能交付的字节少于 2^61 时证明的（`ReadsFinite`）。没有这个条件，证明仍然说明这些调用不会引起未定义行为。
- `NULL` 文件会被每个函数拒绝，什么也不改变（`Goal.gz_refusal`）。对 `NULL` 使用 `gzgetc()` 宏在 C 中是未定义行为，不被覆盖。

## 构建与平台

下面每张表的各列依次是：前提及陈述它的 Lean 谓词；它要求什么；陈述它的目标；前提之外已知的情况。

| 前提 | 要求什么 | 目标 | 前提之外 |
| --- | --- | --- | --- |
| 初始配置 | 默认 x86_64 Linux、LP64、静态构建和默认分配器：`zalloc` 与 `zfree` 各自是 `NULL` 或默认函数（`DefaultOrNull`、`DefAlloc`） | 每个目标 | 其他构建配置不在计划内（[范围](progress.md#scope)）。`zalloc` 或 `zfree` 是自定义函数的流在所有目标之外。默认分配器的失败在目标之内：安全目标对每一种分配结果都成立。 |
| 平台字节对象范围（`ByteObjectsFit`） | 每个字节对象小于 `2^63` 字节，包括调用者的、静态的和内嵌的存储 | 见下面的列表 | 这是一条写明的[系统环境前提](spec/platform.md)：LP64 的对象大小上限 `PTRDIFF_MAX`。它按对象计，不限制内存总量和流的长度。证明操作系统的限制不属于 zlib 的证明。 |

各目标在以下位置陈述 `ByteObjectsFit`：

- 每次流调用所在的堆（`StreamCallDomain`，以及 `StreamSequenceSafety` 的第 2 个子句）；
- 对 inflate 流，还包括历史中此前的每个堆，即每次调用之前和每次调用者修改之后（`StreamReachable.step`、`.rebuffer`）；deflate 的历史只在目标所陈述的那次调用上带有它；
- `compress*` 与 `uncompress*` 的目标（`CompressorSafety`、`UncompressCountedSafe`、`UncompressSingleSafe`）；
- 每次 gz 打开所在的堆，以及 gz 历史中每次调用者修改之后的堆（`GzHistory`、`GzOpenSafe`、`GzDopenSafe`），这就覆盖了调用者的路径串和模式串（[回归](../tests/verification/regressions/gzopen-path-ptrdiff.lean)）；
- 对回调解码器，是每次 `inflateBack` 调用所在的堆和每个回调步骤之后的堆（`BackSafeReachable.step`、`BackPlatform`）。

init、End、校验和与拒绝目标不需要它。这条前提可以被满足：公开的调用者见证具有它（`inflate_default_witness_platform`）。功能目标（`Goal.inflate`、`Goal.inflate_sequence`、各实用函数契约、`Goal.gzopen`、`Goal.gzopen64`、`Goal.gz_initialisation_domain`）以同样的方式陈述它。

目标对模型中的堆提出的条件（`Fresh`、`Uniq`、`LibraryGlobals`、`CrcGlobals`）、循环燃料、CRC 地址模型和空指针算术，都不是调用者的义务。它们在[模型的限制](model-limits.md#conditions-on-the-model-that-goals-state)中。

## 流调用：inflate 与 deflate

流函数的安全目标在每个可达的流（`StreamReachable`）上成立，只要参数满足 `StreamArguments`。`zlib.h` 描述的是调用者让各缓冲区互不重叠时的调用；目标把这种分离写成假设。

| 前提 | 要求什么 | 目标 | 前提之外 |
| --- | --- | --- | --- |
| 流的初始化（`InitArguments`） | `strm` 是 `NULL`，或者是一个可读的记录，其 `zalloc` 与 `zfree` 各自是 `NULL` 或默认函数（`DefaultOrNull`）。`version` 是 `NULL`，或其第一个字节可读。堆是良构的（[模型的限制](model-limits.md#conditions-on-the-model-that-goals-state)）。记录的其他字段（包括 `state`）、`version` 的第一个字节和 `stream_size` 都是任意的。 | `Goal.inflateInit2__safety`、`Goal.inflateInit__safety`、`Goal.deflateInit2__safety`、`Goal.deflateInit__safety` | 只有 `DefaultOrNull` 比 `zlib.h` 更窄。错误的版本、错误的 `stream_size` 和 `NULL` 流都在这些目标之内：调用返回错误码，不留下任何块（`InitResultSafe`）。见[注 1](#note-1-init-and-unset-fields)。 |
| 历史的第一次调用（`StreamReachable.inflateInit`、`.deflateInit`） | 一段历史从一次返回 `Z_OK` 的 init 调用开始：记录可读并满足 `DefaultOrNull`，`version` 的第一个字节是 `'1'`，`stream_size = 112`。 | 两个序列目标，以及通过 `StreamReachable` 涉及的每个单函数流目标 | 这不是收窄：除 `DefaultOrNull` 外，这些正是 C 返回 `Z_OK` 的条件。其中没有关于 `state` 的子句。 |
| 流缓冲区（`StreamBuffers`） | 输入范围（`next_in`、`avail_in`）与输出范围（`next_out`、`avail_out`）互相分离，且都不在流拥有的存储内。每个范围是 `NULL` 或可读，输出范围还须可写。 | `Goal.inflate_safety`、`Goal.deflate_safety`、`Goal.deflateParams_safety`，以及两个序列目标中的这些调用（`StreamArguments`）。功能目标 `Goal.inflate` 与 `Goal.deflate` 也假设它。 | 输入与输出重叠的调用，或缓冲区落在流自身状态内的调用，不被覆盖。 |
| 调用之间调用者的修改（`Rebuffer`） | 在一段历史的两次调用之间，调用者只改变流记录的 `next_in`、`avail_in`、`next_out` 和 `avail_out`，以及流不拥有的内存。 | 两个序列目标；通过 `StreamReachable` 涉及的每个单函数流目标 | 这是 `zlib.h` 的规则：应用程序更新缓冲区字段，其余字段不得由应用程序更新。调用者写了记录的其他字段或流拥有的块，这样的历史在范围之外。 |
| 其他流参数（`StreamArguments`） | `inflateSync`：输入范围是 `NULL` 且 `avail_in = 0`，或者可读且在流的存储之外。`deflatePrime`：还没有任何 `deflate` 调用启动过这个流（`DeflateNotStarted`）；`deflateSetHeader` 有同样的顺序规则（“头部参数”一行）。头部调用和字典调用各有自己的行。其余流调用没有参数前提。 | 该函数的安全目标，以及序列目标中的同一种调用 | 顺序规则来自 `zlib.h`（在第一次 `deflate()` 调用之前）。被排除的顺序是真实 C 的未定义行为（[复现](../tests/regression/deflate-history-domain/README.md)）。 |
| 字典缓冲区（`CallerRange`） | 字典参数是 `NULL`，或是一个可读范围（两个 `Get` 调用还要求可写），其中没有字节落在流拥有的块内。`inflateGetDictionary` 的范围有 `whave` 字节；`deflateGetDictionary` 的范围有 `min(w_size, strstart + lookahead)` 字节。 | `Goal.inflateGetDictionary_safety`、`Goal.deflateGetDictionary_safety`、`Goal.inflateSetDictionary_safety`、`Goal.deflateSetDictionary_safety`，以及序列目标中的这些调用 | 位于流的窗口或其他存储内的字典缓冲区不被覆盖。 |
| 结果单元（`dictLength`、`pending`、`bits`） | 没有前提，也无法陈述前提。翻译把这些标量输出参数当作值传递，而不是内存。`inflateGetDictionary` 接收 `*dictLength` 的值，指针为 `NULL` 时是 `none`（`Option UInt32`，`ZlibF/Zlib/inflate.c.lean`）。`deflateGetDictionary`、`deflatePending` 和 `deflateUsed` 只接收每个指针是否为 `NULL`（`Bool`，`ZlibF/Zlib/deflate.c.lean`）。每个函数都把 C 写入的值作为另一个结果返回。 | `Goal.inflateGetDictionary_safety`、`Goal.deflateGetDictionary_safety`、`Goal.deflatePending_safety`、`Goal.deflateUsed_safety`，以及序列目标中的这些调用 | 这些目标对结果单元的内存什么都没说。非 `NULL` 的指针是否可写，这个单元是否与字典缓冲区、流记录以及流拥有的存储分开，都无法表达。C 用普通赋值通过指针写入（`*dictLength = ...`、`*pending = ...`、`*bits = ...`）。结果单元是调用者自己的普通变量、并且与这些区域分开的调用，才是模型所表示的调用；其他调用不被覆盖。这与 `compress*` 的长度单元是同一个限制（“整缓冲区压缩”一行）。工作规则只对内部函数的输出参数采纳这种表示；这几个是公开函数，它们的翻译是否改为把单元当作内存，所有者尚未决定（[进度](progress.md#no-fault-coverage-of-zlibh-functions)第 4 项）。 |
| 头部参数（`HeaderMemory`、`DeflateNotStarted`、`DeflateHeaderLive`） | `inflateGetHeader`：头记录不是 `NULL`，不归流拥有，其 `extra`、`name` 和 `comment` 缓冲区各自是 `NULL`，或分别有 `extra_max`、`name_max`、`comm_max` 个可写字节。`deflateSetHeader`：头是 `NULL`，或是一个流不拥有的记录，其非 `NULL` 的 `extra` 有 `extra_len` 个可读字节，非 `NULL` 的 `name` 和 `comment` 是短于 `2^64` 字节、以 NUL 结尾的字符串；并且还没有任何 `deflate` 调用启动过这个流。`deflateBound`、`deflateBound_z`：`ActiveHeader`（下面四行），并且已设置的 gzip 头在任何时候都存活，而不只是在写出期间。 | `Goal.inflateGetHeader_safety`、`Goal.deflateSetHeader_safety`、`Goal.deflateBound_safety`、`Goal.deflateBound_z_safety`，以及序列目标中的这些调用 | 头为 `NULL` 的 `inflateGetHeader` 在范围之外：C 会通过这个指针写入（`head->done = 0`）。`deflateSetHeader` 的顺序规则来自 `zlib.h`；在头部写出期间设置 `NULL` 头，真实的 C 会解引用它（[复现](../tests/regression/deflate-history-domain/README.md)）。 |
| 挂接的 gzip 头保持存活（`ActiveHeader` 中的 `HeaderMemory`） | 每次 `inflate` 调用时，在每种模式下，包括头已读完（`done` 已置位）之后：交给 `inflateGetHeader` 的记录仍是一个流不拥有的存活记录，其非 `NULL` 的 `extra`、`name` 和 `comment` 仍分别有 `extra_max`、`name_max`、`comm_max` 个可写字节，并位于流的存储之外。`deflate` 写头期间（`GZIP_STATE` .. `HCRC_STATE`）：交给 `deflateSetHeader` 的记录存活且不归流拥有，其非 `NULL` 的 `extra` 有 `extra_len` 个可读字节，非 `NULL` 的 `name` 和 `comment` 是以 NUL 结尾的字符串。头写完之后调用者可以释放它，但 `deflateBound` 和 `deflateBound_z` 除外（见上一行）。 | `Goal.inflate_safety`、`Goal.deflate_safety`、`Goal.deflateParams_safety`、`Goal.deflateBound_safety`、`Goal.deflateBound_z_safety`，以及两个序列目标中的这些调用 | 对 `inflate`，这条前提要求的比 C 用到的多：`inflate.c` 只在头部模式（`HEAD` .. `HCRC`）中读写 `state->head`，`done` 置位之后不再访问。调用者在 `done` 之后释放该记录或其缓冲区、然后再次调用 `inflate`，这种情形不被覆盖。`inflateReset` 会解除该记录的挂接。对 `deflate`，前提要求 `extra_len` 个可读字节；C 只读 `extra_len mod 2^16` 个。 |
| inflate 的 gzip extra 字段（`InflateHeaderProgress`） | `inflate` 把 gzip 头（`HEAD` .. `HCRC`）读入挂接的 `gz_header` 时，其 `extra` 缓冲区（`extra_max` 字节）与尚未读取的输入分离；在 `EXTRA` 模式中，记录的 `extra_len` 不小于 `state->length`。 | `Goal.inflate_safety`，以及 `Goal.inflate_sequence_safety` 中的每次 `inflate` 调用；功能目标 `Goal.inflate` 与 `Goal.inflate_sequence` 也是如此 | 每个被排除的情形都是真实 C 在 EXTRA 的 `zmemcpy` 中的未定义行为（[复现](../tests/regression/inflate-gzip-extra/README.md)）：重叠的复制，或者调用者在 extra 字段读到一半时调低 `extra_len`，导致写到 `extra_max` 之外。`zlib.h` 没有说明这两种布局是否允许。 |
| deflate 的 gzip 头区域（`DeflateHeaderApart`） | `deflate` 写出挂接的 `gz_header`（`GZIP_STATE` .. `HCRC_STATE`）期间，输入范围、输出范围、extra 字段（`extra_len mod 2^16` 字节）、name 与 comment（各含其 NUL）是两两分离的字节范围，可以位于同一个块中；extra 字段、name 与 comment 位于流拥有的存储之外。 | `Goal.deflate_safety`、`Goal.deflateParams_safety`、`Goal.deflateBound_safety`、`Goal.deflateBound_z_safety`，以及 `Goal.deflate_sequence_safety` 中的每次这类调用；功能目标 `Goal.deflate` 与 `Goal.deflate_sequence` 也是如此 | 这些区域没有重叠的理由。被排除的情形中有两种是真实 C 的未定义行为（[复现](../tests/regression/deflate-gzip-name-output/README.md)）：name 位于输出范围或 `pending_buf` 中时，它的 NUL 会被一次刷新或一个头部字节覆盖，name 循环随即读到缓冲区之外。`zlib.h` 没有说明这些布局是否允许。 |
| deflate 的 gzip 头进度（`DeflateHeaderProgress`） | 在每次写出挂接的 `gz_header` 的 `deflate` 调用时，调用者保留了已经写出的部分：字段仍覆盖已写出的部分（`gzindex`），并且在 `EXTRA_STATE`、`NAME_STATE` 或 `COMMENT_STATE` 中，该字段没有中途被置为 `NULL`（它为 `NULL` 时 `gzindex = 0`）。 | 与上一行相同的目标 | 被排除的修改是真实 C 的未定义行为（[复现](../tests/regression/deflate-history-domain/README.md)）：被缩短的字段会被读到末尾之外；中途置为 `NULL` 的字段会被跳过，而 `gzindex` 没有重置，下一个字符串就从 `gzindex` 处读起，越过它的末尾。`zlib.h` 要求调用者在第一次 `deflate` 调用之前提供头部；它没有说明记录在写出期间能否改变。 |
| 被拒绝的流（`RefusedInflate`、`RefusedDeflate`） | 被拒绝的流是 `NULL`，或者是一个可读的记录：其状态为 `NULL`，或其 `zalloc` 或 `zfree` 为 `NULL`，或其状态是一个被检查拒绝的存活状态记录（反向指针、`mode` 或 `status` 字段有误）。 | `Goal.inflate_refusal`、`Goal.deflate_refusal` | 这涵盖 `End` 之后的记录、init 失败之后的记录、复制失败时的目的记录，以及存活记录的结构体副本。有三类记录在范围之外：见[注 2](#note-2-refused-streams)。 |
| 复制的目的流 | 目的流是一个可读的流记录，并且不是源记录（`source ≠ dest`）。源使用默认分配器（`DefAlloc`）。 | `Goal.inflateCopy_safety`、`Goal.deflateCopy_safety`，以及功能目标 `Goal.inflateCopy`、`Goal.deflateCopy` | 当 `dest == source` 时，C 的 `zmemcpy(dest, source, sizeof(z_stream))` 把一个对象复制到它自身上，这是未定义行为；这种情形不被覆盖。目的记录与源记录、某个缓冲区或某个状态记录部分重叠的情形无法表达：模型把 `z_stream` 记录放在单独的表里（[模型的限制](model-limits.md#how-the-runtime-represents-c)，地址与布局模型）。`zlib.h` 没有说明是否允许这种布局。 |
| 直接调用 `deflateResetKeep` | deflate 的调用历史（`StreamOperation .deflate`）中没有对 `deflateResetKeep` 的直接调用；`deflateReset` 和 `deflateInit2_` 仍在其中。 | `Goal.deflate_sequence_safety`，以及通过 `StreamReachable` 涉及的各个单函数 deflate 目标 | 这不是比 `zlib.h` 更窄的限制：`zlib.h` 把 `deflateResetKeep` 声明在 `undocumented functions (not part of the zlib API)` 之下，它的目标不是必需的公开目标（[进度](progress.md#scope)）。真实的 C 在那里不安全：在 `deflateResetKeep`、`deflate(Z_BLOCK)`、`deflateCopy`，以及副本上的一次 `Z_RLE` 或 `Z_HUFFMAN_ONLY` 刷新之后，后续的 `deflate` 会沿着一个未初始化的 `prev` 槽走下去，读到窗口之外（[问题记录](findings/deflate-copy-pending-prev/README.md)）；不做复制时，后续的匹配可能出错（[问题记录](findings/deflate-resetkeep-stale-hash/README.md)）。单次调用的安全性（不出故障、终止）仍然得到了证明；`deflateReset` 要经过它。 |

### gzip 头部及其缓冲区何时必须有效

| 流 | 时段 | 必须成立的条件 |
| --- | --- | --- |
| inflate | 从 `inflateGetHeader` 到下一次成功的 `inflateReset` 或 `inflateReset2`，或 `inflateEnd`，其间每次 `inflate` 调用时 | 记录存活；`extra`、`name` 和 `comment` 各自是 `NULL`，或在各自的 `_max` 大小内可写 |
| inflate | `inflate` 读头部期间（`HEAD` .. `HCRC`） | 另外：`extra` 不与尚未读取的输入重叠；`extra_len` 没有被调低 |
| deflate | 调用 `deflateSetHeader` 时 | 在第一次 `deflate` 调用之前；`extra` 有 `extra_len` 个可读字节；`name` 和 `comment` 以 NUL 结尾 |
| deflate | 从第一次 `deflate` 调用到头部写完（`GZIP_STATE` .. `HCRC_STATE`） | 记录和缓冲区存活；没有字段被缩短或置为 `NULL`；输入、输出、extra、name 和 comment 两两分离 |
| deflate | 头部写完之后 | 记录和缓冲区可以释放，除非之后还要调用 `deflateBound` 或 `deflateBound_z` |

### 注 1：init 与未设置的字段

在 C 中，`inflateInit` 的调用者没有设置的字段，其值是不确定的。模型里没有这样的值。未设置的整数字段取一个任意的值；未设置的指针字段取模型能够表达的某个值：`NULL`，或对某个模型对象的引用。四个 init 目标对每一个这样的值都成立，因为 `InitArguments` 只约束 `zalloc` 和 `zfree`。C 的行为与这种解读一致：init 函数给 `strm->state` 赋值，而不读取它。模型里没有“未初始化指针”这种值，这是模型的一处限制（[可信基础](trusted-base.md)第 2 项）。

另有两处陈述通过谓词 `InitDomain` 保留了“init 之前 `state = NULL`”这一子句。非空性目标 `Goal.inflate_initialisation_domain`、`Goal.deflate_initialisation_domain` 和 `Goal.inflate_back_initialisation_domain` 说：在每个这样的堆上，只要没有分配失败，init 就返回 `Z_OK`；这一子句在那里不会收窄任何安全目标。回调解码器历史的第一次调用（`BackSafeReachable.init`）则把它当作前提（[回调解码器](#callback-decoder)）。

### 注 2：被拒绝的流

`Goal.inflate_refusal` 覆盖 `inflate`、`inflateEnd`、`inflateReset`、`inflateReset2`、`inflateGetDictionary`、`inflateSetDictionary`，以及源被拒绝时的 `inflateCopy`。`Goal.deflate_refusal` 覆盖 `deflate`、`deflateSetDictionary`、`deflateParams`、`deflateGetDictionary`，以及源被拒绝时的 `deflateCopy`。其余每个流函数的拒绝定理见[按函数查覆盖情况](coverage.md)。

在 `zalloc` 和 `zfree` 已设置的情况下，有三类记录在拒绝目标的定义域之外。

1. **状态字段里是垃圾地址**，例如从未初始化的自动变量 `z_stream`。这无法表达：在模型里，这个字段是 `NULL`、一个 inflate 状态编号或一个 deflate 状态编号，而新分配内存中的指针是 `NULL`（[模型的限制](model-limits.md#how-the-runtime-represents-c)，“未初始化指针变成 NULL”一行）。在 C 中，检查会经由这个指针读取，这是未定义行为。
2. **悬空的状态**：字段指向一个已不存活的状态。这可以表达，被谓词排除。在 C 中，检查会读取已释放的状态，这是未定义行为。
3. **类型不对的状态**：把 deflate 状态交给 inflate 函数，或者反过来。这可以表达，被谓词排除。在 C 中，检查会按另一种结构体类型读取这个状态，这是未定义行为。

## 整缓冲区实用函数与校验和

| 前提 | 要求什么 | 目标 | 前提之外 |
| --- | --- | --- | --- |
| 整缓冲区压缩（`CompressArguments`） | 源与目的缓冲区不重叠：`Separate source n dest c`。源可读，目的缓冲区在其容量范围内可写，除非这次调用是 C 会拒绝的调用（`compressRejected`）。`compress` 与 `compress2` 的长度单元不能是 `NULL`；只有 `_z` 形式允许 `NULL` 单元。 | `Goal.compress_safety`、`Goal.compress2_safety` 及其 `_z` 形式 | 源与目的缓冲区重叠的调用不被覆盖。长度单元 `*destLen` 在翻译中是一个标量值（`Option UInt64`，`ZlibF/Zlib/compress.c.lean`），不是内存：这个单元是否可写、是否与源和目的缓冲区分开，都无法表达；不满足这两点的调用不被覆盖。翻译是否改为把这个单元当作内存，所有者尚未决定，与流调用的“结果单元”一行相同。 |
| 计数解压（`UtilitySeparation`、`UncompressCountedSafe`、`UncompressSingleSafe`） | 源、目的缓冲区、目的长度单元和源长度单元两两分离。`uncompress` 与 `uncompress_z` 需要源与目的缓冲区分离、长度单元与数据分离。长度单元是八个可读可写的字节（`LengthCell`）；`uncompress` 与 `uncompress2` 的单元不能是 `NULL`。 | `Goal.uncompress_safe`、`Goal.uncompress2_safe` 及其 `_z` 形式 | 长度单元与数据缓冲区重叠，或两个单元互相重叠，都不被覆盖。与 `compress*` 不同，单元 `*destLen` 和 `*sourceLen` 在翻译中是内存（`ZlibF/Zlib/uncompr.c.lean`），所以这里的分离是写明的前提，而不是模型的限制。 |
| Adler 初始化查询（`AdlerBufferBytes`） | 只有长度为零时 `buf` 才可以是 `NULL`；非 `NULL` 的可读缓冲区保留完整的长度范围。 | `Goal.adler32_safety`、`Goal.adler32_z_safety`，以及功能目标 `Goal.adler32`、`Goal.adler32_z` | 这比固定版本头文件里对 `NULL` 不加限定的说法更窄。`buf` 为 `NULL` 且 `len = 1` 时，C 会读 `buf[0]`。CRC 目标保留 `BufferBytes`，它允许任意长度下的 `NULL`。见下面的说明。 |
| CRC 组合算子 | 算子是 `crc32_combine_gen` 或 `crc32_combine_gen64` 返回的值。 | `Goal.crc32_combine_op_safety` | 这是 `zlib.h` 为 `crc32_combine_op` 规定的定义域，不是收窄。任意的 `op` 值不被覆盖。 |

关于 `adler32` 与 `NULL` 的说明：上游 [PR #1364](https://github.com/madler/zlib/pull/1364) 报告了对 `NULL` `buf` 的单字节读取。维护者于 2026 年 11 月 6 日关闭了它，保留代码，并宣布将在 `zlib.h` 中加入对 `len` 的限制。`develop` 的头部 `99623ef7097352da7993ba614161fd6a311e046e` 不包含这段文字；它合入之后，本行要与之对照。

## 回调解码器

`Goal.inflate_back_sequence_safety` 在 `BackSafeReachable` 的历史上成立。

| 前提 | 要求什么 | 目标 | 前提之外 |
| --- | --- | --- | --- |
| 回调解码器的初始化（`BackSafeReachable.init` 中的 `InitDomain`） | 流记录可读；`zalloc` 与 `zfree` 各自是 `NULL` 或默认函数；记录的 `state` 字段是 `NULL`；`version` 指向一个可读的字节 `'1'`；`stream_size = 112`；调用返回了 `Z_OK`。 | `Goal.inflate_back_sequence_safety` | `zlib.h` 不要求 `state` 为 `NULL`，C 也是不读 `state` 就覆盖它。`z_stream` 在 `inflateBackInit_` 之前 `state` 不为 `NULL` 的历史，在这个序列目标之外。已登记的功能目标 `Goal.inflateBackInit_` 没有这一子句：它对每个 `state` 值覆盖 init 调用，连同各种拒绝。 |
| 回调（`CallbackProtocol`） | 调用者为它的 `in` 和 `out` 函数提供一个协议；各子句见下面的列表。 | `Goal.inflate_back_sequence_safety` | 这些是调用者代码的契约，不是被假设的库契约，并且一直显式写出。描述符对象可以与窗口共用同一次分配中切片以外的部分。 |
| 调用之间调用者的修改（`BackSafeReachable.caller`） | 两次调用之间，调用者的修改是一次 `Rebuffer`（“调用之间调用者的修改”一行），并且保持窗口切片，以及每个仍存活的块的只读标志。 | `Goal.inflate_back_sequence_safety` | C 代码无法改变只读标志，所以那一子句不排除任何 C 调用者。关于窗口的子句确实排除了一些调用者：调用者在两次 `inflateBack` 调用之间写窗口切片，这样的历史在范围之外。`inflateBack` 在每次调用开始时置 `state->whave = 0`，所以 C 看来不会读取先前的窗口字节（**尚未由证明确认**）；`zlib.h` 并不禁止这样的写入。 |
| 回调输入总量 | `protocol.inputBound < 2^48`：一次 `inflateBack` 调用在它所有的 `in` 调用中总共得到少于 `2^48` 字节。 | `Goal.inflate_back_sequence_safety` | `zlib.h` 对一次调用的总输入没有限制。运行时把每个循环限制在 `2^64` 次迭代以内（[模型的限制](model-limits.md#conditions-on-the-model-that-goals-state)），而解码循环每轮至少读一个比特，所以输入更多的调用可能在 C 还会继续运行时就耗尽燃料。`2^48` 字节远远超过一次调用实际能处理的输入。功能目标 `Goal.inflateBack`（不在计划内，未证明）没有这条前提。 |
| 回调解码器窗口 | `8 ≤ windowBits ≤ 15`，窗口不是 `NULL` 并且有 `2^windowBits` 个可写字节，这是 `zlib.h` 的要求；另外还要求：窗口是某个堆字节块的切片。 | `Goal.inflate_back_sequence_safety`，通过 `BackSafeReachable.init` | `zlib.h` 只要求一个有 `2^windowBits` 个可写字节的窗口。模型中另外唯一一种可写的字节视图是 deflate 状态内部的 depth 数组，那是调用者无法指名的库内存储；窗口位于那里不在已证明的定义域内。 |
| 回调解码器输入块 | 每一块输入都位于某个堆字节块中：调用者给出的第一块（`BackFirstChunk`），以及 `in` 交出的每一块（`BackPlatform`）。 | `Goal.inflate_back_sequence_safety` | C 能处理位于任何可读存储中的输入块。位于模型中其他存储里的输入块，例如结构体的字段或静态数据，不在已证明的定义域内。这与 `inflate` 快速入口的限制相同（[模型的限制](model-limits.md#functional-and-model-statements)，“快速解码辅助函数”）：`inflate_fast` 就运行在这块输入上。把两个解码器推广到任意字节引用不在计划内；[回调解码器骨架记录](history/skeleton-inflate-back.md)把它列为候选工作。 |

`CallbackProtocol` 的各个子句：

- `in` 和 `out` 各自都会返回而不出故障，并且只改变调用者自己的块；这些块不包括状态和流记录。
- 两者都保持窗口切片中的字节。
- `in` 交出的输入块可读，并且与窗口、状态和流记录分离。`out` 保持当前的输入块可读。
- 总输入有一个有限的上界（`inputBound`）。
- 第一块输入（`next_in`、`avail_in`）可读，并且与窗口分离。
- 每个回调都让堆保持良构（`Fresh`、`Uniq`），它新建的每个块都属于调用者自己（`ExternalFrame`）。
- 协议带有一个不变量，说的是堆以及“已供给和已交付字节”的日志。调用 `inflateBack` 时它成立，每个回调都保持它。这个不变量只能依赖调用者自己的块和堆的分配器字段，不能依赖窗口切片中的字节（`CallbackProtocol.local_`）。

## Gzip 文件接口

`Goal.gz_sequence_safety` 在一个句柄的每段历史（`GzHistory`）上、对每个文件系统世界成立。它是针对打过补丁的源码陈述的（[补丁](../patches/README.md) 0002 至 0005）。gz 世界是堆之外的可信语义：[外部 I/O 模型](design/external-io.md)描述它，[可信基础](trusted-base.md)说明对它作了哪些假设。

| 前提 | 要求什么 | 目标 | 前提之外 |
| --- | --- | --- | --- |
| Gz 打开参数（`GzOpenSafe`、`GzDopenSafe`、`GzHistory.open`） | `path` 与 `mode` 各自是 `NULL`，或是短于 `2^64` 字节、以 NUL 结尾的字符串；堆是良构的，其字节对象都不超限；世界是一个良构的文件系统（`FileSystem`）。 | `Goal.gz_sequence_safety` | 任何描述符、任何模式文本、任何世界下的打开都被覆盖，包括每一种失败。在自身对象之内没有 NUL 结尾的路径或模式在范围之外，C 中也是如此。 |
| Gz 调用者缓冲区（`GzArguments` 中的 `GzRange`） | `gzread`、`gzfread`、`gzwrite`、`gzfwrite`、`gzputs`、`gzgets` 与 `gzerror` 的调用者缓冲区可读（读取调用的缓冲区和 `gzerror` 的 `errnum` 还须可写），并且与句柄拥有的块分开（`GzOwned`）。`gzputs` 的参数是以 NUL 结尾的字符串（`CString`），范围包含它的 NUL：没有 NUL 的可读字节，以及 `NULL`，都在范围之外。 | `Goal.gz_sequence_safety` | 见下文“为什么排除句柄自己的字符串”。调用者的缓冲区和字面量都被覆盖。 |
| Gz printf 字符串（`GzArguments`） | `gzprintf` 与 `gzvprintf` 的格式串以及每个字符串参数（`%s`）都与句柄拥有的块分开（`GzOwned`）。 | `Goal.gz_sequence_safety` | 理由与上一行相同。字面量和调用者的字符串都被覆盖。 |
| 格式化（`Formatted`） | 格式串是模型能够表示的：整数、字符和字符串参数，带受支持的标志、宽度、精度和长度修饰符。`GzArguments` 在每个 `gzprintf` 与 `gzvprintf` 步骤上都要求这一点，读取端句柄或处于错误状态的句柄也不例外，尽管 C 在那里根本不读格式串。 | `Goal.gz_sequence_safety` | 范围之外：`%f` 及其他浮点转换、`%p`、`%n`、长度修饰符 `h` 与 `hh`（`%hd`、`%hhu`）、`*` 宽度与精度（`%*d`）、作用于没有 NUL 的数组的 `%.3s`，以及传入 `unsigned` 参数的 `%c` 或 `%d`（值可表示时 `va_arg` 允许这样做）。这些需要扩展模型。 |
| Gz 调用者步骤与世界步骤（`GzCallerFrame`、`GzWorldStep`） | 两次调用之间，调用者可以改变句柄不拥有的任何块，也可以释放自己的缓冲区；堆保持良构，其字节对象都不超限。世界可以变成任何良构的文件系统：别的参与者可以关闭或重用句柄的描述符。 | `Goal.gz_sequence_safety` | 这比真实系统更宽，是有意为之。调用者写了句柄拥有的块，就不在历史之内。`gzbuffer`、`gzclose` 等不涉及调用者内存的调用没有参数前提。 |
| Gz 读取调用的终止（`ReadsFinite`） | 对 `gzread`、`gzfread`、`gzgetc`、`gzgetc_`、`gzgets` 和 `gzungetc`：句柄的描述符有一个小于 `2^61` 字节的有限读取预算（`fs.readBudget fd = some b` 且 `b < 2^61`），即该描述符还能交付的总字节数。这条前提还说描述符编号不为负（`HasBudget`）。 | `Goal.gz_sequence_safety` 中关于终止的那一半，且只针对这六个调用 | 这条前提不排除任何故障：不出故障的那一半和后置条件对每个世界成立，不需要预算。`gzdirect`、写入一侧和 `gzseek` 不需要它。见下文“为什么需要读取预算”。 |
| Gz 操作系统事实 | 非空的 `write` 从不返回 0；`close` 即使失败也会释放描述符。 | `Goal.gz_sequence_safety`，通过世界模型 | 这是 Linux 的行为，被信任，没有检查。`write` 永远返回 0 会让 C 中的 `gz_comp` 空转（[观察记录](progress.md#observations)）。 |

`strerror` 的模型（“外部错误字符串”）是模型的限制，不是调用者的义务：见[模型的限制](model-limits.md#conditions-on-the-model-that-goals-state)。

### 为什么排除句柄自己的字符串

每个 gz 入口都先调用 `gz_error(state, Z_OK, NULL)`，它会释放 `state->msg`，然后才触及自己的参数。`gzerror` 返回的字符串就是 `state->msg`。所以把它再传回同一个句柄上的调用，在 C 中就是释放后使用：在停滞的写入端上执行 `gzputs(f, gzerror(f, &e))`，AddressSanitizer 报告 `strlen` 中的堆释放后使用；`gzprintf(f, "%s", gzerror(f, &e))` 则在 `vsnprintf` 中读取已释放的内存（[复现](../tests/regression/gzprintf-error-string/README.md)，其中也包括 `gzwrite` 和 `gzread`）。`zlib.h` 只提醒说，之后的 `gzerror` 调用可能使这个字符串失效。

### 为什么需要读取预算

`zlib.h` 对输入没有上界。C 里有两个循环在无穷无尽的来源上不会结束：来源永远交付只解码出空内容的数据（空的 gzip 成员）时，`gz_fetch` 会一直循环；待跳过的量极大而来源无穷时，`gz_skip` 会永远读下去。这是 C 真实的不终止，任何有限的循环燃料都覆盖不了。有读取预算时，每个循环都有界。

`2^61` 这个数是模型的限制，不是 zlib 的。模型的每个循环有 `2^64` 次迭代的燃料。读取循环由一些度量限定，这些度量由剩余的输入、读取预算和尚待交付的字节数构成（`fetchRank`，以及 `gz_read` 与 `gz_skip` 的度量）。一次取数会把缓冲区填满，除非它失败、输入结束、到达 `GZ_OFF_MAX`，或者降低了 `fetchRank`；所以预算小于 `2^61` 就能让这些度量以及迭代次数保持在 `2^64` 以下。

这个上界的依据：`tests/verification/regressions/gz-read-budget-fuel.lean` 表明，如果允许任意大小的预算，就存在这样的预算，它所需要的空 gzip 成员轮数超过循环燃料。它只是算术上的核心，并不是对 `gz_fetch` 返回 `outOfFuel` 的一次经过检查的运行。

预算按描述符编号记：`close` 之后被重用的编号继承剩余的预算。`gzdopen` 会拒绝负的描述符，所以没有句柄来自负描述符。gz 调用的终止依赖关于世界的两条规则：读取调用的 `ReadsFinite`，以及“非空的 `write` 从不返回 0”这一操作系统事实（“Gz 操作系统事实”一行），后者约束写入一侧。

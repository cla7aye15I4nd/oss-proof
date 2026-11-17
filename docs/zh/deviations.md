<!-- source-sha256: d566452de823c419bc0143a657fe61a55fa2047cfac8d5e63b41ab4186b76fc9 -->
# 偏离记录：一次调用要满足什么

本页写给调用 zlib 的人，回答一个问题：我的调用被安全定理覆盖了吗？下面的核对清单按函数族、用 C 的说法作答。清单之后的各表给出每一行背后的 Lean 前提、陈述它的目标，以及它的理由。

满足自己那个函数的各行，调用就被覆盖。不满足的调用不被覆盖：既没有被证明安全，也没有被断言不安全。

本页列出安全目标中每一条比 `zlib.h` 更窄的前提，以及读者容易漏看的前提。只是重复 `zlib.h` 的前提写在目标的 Lean 命题里；每个函数对应哪个目标，见[按函数查覆盖情况](coverage.md)。调用者无能为力的、对模型的条件在[模型的限制](model-limits.md)中。被信任而没有被证明的东西在[可信基础](trusted-base.md)中。

## 给调用者的核对清单

每一行末尾是陈述它的 Lean 谓词；没有谓词陈述的行会注明。只有写明允许 `NULL` 的地方才允许 `NULL`。

**每一次调用**

- 库是默认的 x86_64 Linux 构建：LP64、静态链接，由 zlib 1.4（上游提交 `99623ef7`）加六个[补丁](../../patches/README.md)编译而成。
- 每个 `z_stream` 的 `zalloc` 和 `zfree` 都是 `Z_NULL`，于是 zlib 使用它的默认分配器（`DefaultOrNull`）。自定义分配器不被覆盖。`malloc` 失败是被覆盖的。
- 内存中没有任何单个对象达到或超过 2^63 字节（`ByteObjectsFit`）。这是 LP64 下单个对象的上限 `PTRDIFF_MAX`；它不限制内存总量，也不限制流的长度。
- 这些行对整段历史成立。一个流或一个文件上的某次调用被覆盖，前提是从它的初始化或打开算起，此前在它上面的每次调用也都满足各自的行；那些调用返回什么都可以（`StreamReachable`、`GzHistory`、`BackSafeReachable`）。

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

调用失败时，有两种情况下此后在 `s` 上的每次调用都以错误值被拒绝，因而被覆盖：调用返回了 `Z_VERSION_ERROR`，或者你在调用之前已经置 `s.state = Z_NULL`。其他情况取决于是哪一种失败：每种失败在记录里留下什么，见[注 2](#note-2-refused-streams)。

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

**读取 gzip 头部：`inflateGetHeader`，以及之后的 `inflate`**

- 调用 `inflateGetHeader` 时：`head` 不是 `NULL`。它的 `extra`、`name` 和 `comment` 各自是 `NULL`，或者分别有 `extra_max`、`name_max`、`comm_max` 个可写字节。这个记录和这些缓冲区都在流自身的内存之外（`HeaderMemory`）。
- 记录一直挂接在这个流上，直到一次成功的 `inflateReset` 或 `inflateReset2`、一次找到同步点的 `inflateSync`（它会重置这个流）、一次换掉它的 `inflateGetHeader` 调用，或者 `inflateEnd`。挂接期间，每次 `inflate` 调用时记录及其缓冲区都同样有效，头部读完之后也是如此（`ActiveHeader` 中的 `HeaderMemory`）。
- `inflate` 还在读头部期间，`extra` 缓冲区不与尚未读取的输入重叠，你也不调低记录中的 `extra_len`（`InflateHeaderProgress`）。
- `inflateCopy` 得到的副本挂接着同一个记录。这几行对副本上的每次 `inflate` 调用同样成立，直到副本以上述方式之一解除挂接。

**写出 gzip 头部：`deflateSetHeader`、`deflatePrime`，以及之后的 `deflate`、`deflateParams`、`deflateBound`、`deflateBound_z`**

- `deflateSetHeader` 和 `deflatePrime` 在初始化或重置之后的第一次 `deflate` 调用之前调用，这是 `zlib.h` 的规定（`DeflateNotStarted`）。
- 调用 `deflateSetHeader` 时：`head` 是 `NULL`，或者是流自身内存之外的一个记录。它的 `extra` 是 `NULL`，或者有 `extra_len` 个可读字节，并且在流自身的内存之外。它的 `name` 和 `comment` 各自是 `NULL` 或以 NUL 结尾的字符串（`HeaderMemory`）。
- 记录一直挂接在这个流上，直到 `deflateReset`、一次换掉它的 `deflateSetHeader` 调用，或者 `deflateEnd`。
- 从 `deflateSetHeader` 起，到 `deflate` 把头部写完为止，每次 `deflate`、`deflateParams`、`deflateBound` 和 `deflateBound_z` 调用时：
  - 记录及其缓冲区仍像 `deflateSetHeader` 那一行说的那样有效（`ActiveHeader` 中的 `HeaderMemory`）；
  - `z_stream` 的输入范围和输出范围、extra 字段、name 和 comment 两两不重叠，三个头部缓冲区在流自身的内存之外（`DeflateHeaderApart`）；
  - 如果某次 `deflate` 调用在 extra 字段、name 或 comment 写到一半时返回，你不缩短那个字段，也不把它改成 `NULL`（`DeflateHeaderProgress`）。
- 头部写完之后，`deflate` 和 `deflateParams` 对这个记录不再有任何要求。zlib 不会告诉你头部是在哪一刻写完的。
- `deflateBound` 和 `deflateBound_z` 不论何时调用都会读取挂接着的记录，头部写完之后也一样。每次这样的调用时，记录及其缓冲区都像 `deflateSetHeader` 那一行说的那样有效（`DeflateHeaderLive`）。
- `deflateCopy` 得到的副本挂接着同一个记录。这几行对副本上的调用同样成立。

**`inflateCopy`、`deflateCopy`**

- `source` 是下一条所说的那种流，`dest` 指向一个不是 `source` 的 `z_stream`（`source ≠ dest`）。
- 副本与 `source` 指向同一个 `gz_header` 记录。于是“gzip 头部”各行对两个流上的调用都成立。

**其余流调用**（`inflateEnd`、`deflateEnd`、`inflateReset`、`inflateReset2`、`inflatePrime`、`inflateMark`、`deflateReset`、`deflateTune`、`deflatePending`、`deflateUsed`）

- 对参数没有前提。流须是某次初始化或复制返回 `Z_OK` 得到的，并且一直按这份清单使用。
- 不在 deflate 流上直接调用 `deflateResetKeep`。`zlib.h` 把它列在未文档化的函数里，含有直接调用的历史在各个 deflate 目标之外。`deflateReset` 先调用它、再清空哈希表，是被覆盖的（`StreamOperation`）。
- `deflatePending` 和 `deflateUsed`：每个结果指针（`pending`、`bits`）是 `NULL`，或者指向你自己的一个变量，它与 `z_stream` 和流自身的内存都不重叠。这一行没有 Lean 谓词陈述：翻译把结果作为值返回（见[“结果单元”](#stream-calls-inflate-and-deflate)一行）。

**`NULL` 流或不一致的流**

- 以下情况会被拒绝：流指针是 `NULL`；`z_stream` 的 `state` 是 `Z_NULL`，例如 `End` 之后；对仍然存活的 `z_stream` 作的结构体复制。除四个初始化函数之外，每个有文档的流函数的安全目标都有拒绝这一子句。
- 被拒绝的调用返回一个错误值，并让内存保持原样；例外是源被拒绝的 `inflateCopy` 和 `deflateCopy` 会把 `dest->state` 置为 `Z_NULL`。返回值和精确的命题见[注 2](#note-2-refused-streams)。
- 不被覆盖：设置了分配器、而 `state` 里是过期指针或垃圾指针的 `z_stream`。这包括原件已被结束之后还在使用的结构体复制。

**`compress`、`compress2`、`compress_z`、`compress2_z`**

- `source` 有 `sourceLen` 个可读字节，`dest` 有 `*destLen` 个可写字节，两者不重叠（`CompressArguments`）。`sourceLen == 0` 时 `source` 可以是 `NULL`，`*destLen == 0` 时 `dest` 可以是 `NULL`。
- C 以 `Z_STREAM_ERROR` 拒绝的调用，不论其他参数如何都被覆盖：`source` 为 `NULL` 而 `sourceLen` 不为零，`dest` 为 `NULL` 而 `*destLen` 不为零，以及 `_z` 形式的 `destLen` 为 `NULL`（`compressRejected`）。
- `compress` 和 `compress2` 的 `destLen` 不能是 `NULL`（`CompressorSafety`）。
- `destLen` 指向你自己的一个变量，它与 `source` 和 `dest` 都不重叠。这一行没有 Lean 谓词陈述：翻译把 `*destLen` 当作值传入（见[“整缓冲区压缩”](#whole-buffer-utilities-and-checksums)一行）。

**`uncompress`、`uncompress2`、`uncompress_z`、`uncompress2_z`**

- `source` 是 `NULL`，或在源长度范围内可读；`dest` 是 `NULL`，或有 `*destLen` 个可写字节。`destLen`，以及带 `2` 的两个函数的 `sourceLen`，各自是 `NULL`，或指向八个可读可写的字节（`LengthCell`）。
- `source`、`dest` 和各个长度变量两两不重叠（`UtilitySeparation`）。
- `uncompress` 和 `uncompress2` 的长度指针不能是 `NULL`。

**校验和与查询**

- `adler32`、`adler32_z`：只有 `len == 0` 时 `buf` 才可以是 `NULL`；否则它有 `len` 个可读字节（`AdlerBufferBytes`）。
- `crc32`、`crc32_z`：`buf` 是 `NULL`，或有 `len` 个可读字节。
- `crc32_combine_op`：`op` 是 `crc32_combine_gen` 或 `crc32_combine_gen64` 返回的值，这是 `zlib.h` 的规定。
- 各个组合函数、`compressBound`、`compressBound_z`、`zlibVersion` 和 `zlibCompileFlags` 没有前提。

**回调解码器：`inflateBackInit`、`inflateBack`、`inflateBackEnd`**

- 调用 `inflateBackInit` 时：`zalloc` 和 `zfree` 是 `Z_NULL`；`windowBits` 在 8 到 15 之间；`window` 不是 `NULL`，有 `2^windowBits` 个可写字节，并且是一个字节数组或其中一段，而不是结构体里的字节字段（`BackInitArguments`、`BackSafeReachable.init`）。`z_stream` 的 `state` 字段可以取任意值。
- 每次调用 `inflateBack` 时，`strm->next_in` 是 `NULL`，或者指向 `avail_in` 个可读字节；这些字节不与窗口重叠，并且是一个字节数组或其中一段（`BackFirstChunk`）。
- 你的 `in` 和 `out` 函数会返回，只写你自己的内存，不写窗口、`z_stream` 和 zlib 的状态。`in` 交出的每个片段都可读，是一个字节数组或其中一段，不与窗口重叠，并且在下一次 `in` 调用之前保持可读（`CallbackProtocol`、`BackPlatform`）。
- 一次 `inflateBack` 调用总共得到的输入少于 2^48 字节，第一个片段也算在内（`inputBound`）。
- 两次 `inflateBack` 调用之间，你不写窗口，并且只改 `z_stream` 的四个缓冲区字段（`BackSafeReachable.caller`）。如果 `window` 指向某个数组的第一个字节，这条规则管的是整个数组，包括 `2^windowBits` 字节之后的部分：两次调用之间，这个数组的任何字节你都不写。

**gzip 文件：各个 `gz*` 函数**

- `path` 和 `mode` 是 `NULL` 或以 NUL 结尾的字符串（`GzOpenSafe`、`GzDopenSafe`）。
- 传给 `gzread`、`gzfread` 或 `gzgets` 的缓冲区，在调用指明的长度内可写；传给 `gzwrite` 或 `gzfwrite` 的缓冲区，在调用指明的长度内可读。`gzerror` 的 `errnum` 指针是 `NULL`，或者指向你自己的一个 `int`（`GzRange`）。
- 这些缓冲区、`gzerror` 的那个 `int`、`gzputs` 的参数，以及 `gzprintf` 和 `gzvprintf` 的格式串和每个指针参数，都是你自己的内存，不是 zlib 为这个文件分配的内存。尤其不要把 `gzerror` 返回的字符串再传回同一个文件上的调用（`GzRange`、`GzArguments`）。
- `gzputs` 的参数是以 NUL 结尾的字符串，不能是 `NULL`（`CString`）。
- `gzprintf` 或 `gzvprintf` 的调用是一次对其格式串和参数在 C 中有定义的 `vsnprintf` 调用，格式串中没有 `%n`。库不检查这一点，也没有前提陈述它。文件以写方式打开且不处于错误状态时，格式串是以 NUL 结尾的字符串，每个指针参数都指向未被释放的内存（`GzArguments`）。
- 两次调用之间，你不写 zlib 为这个文件分配的内存（`GzCallerFrame`）。
- 关闭文件的那次调用之后，你不再使用这个文件：`gzclose`，或者在相应模式的文件上调用的 `gzclose_r` 或 `gzclose_w`。文件已被释放，C 中也是如此。
- `gzread`、`gzfread`、`gzgetc`、`gzgetc_`、`gzgets` 和 `gzungetc` 的终止，是在文件描述符还能交付的字节少于 2^61 时证明的（`ReadsFinite`）。没有这个条件，证明仍然说明这些调用不会引起未定义行为。
- `NULL` 文件会被每个函数拒绝，什么也不改变（`Goal.gz_refusal`）。对 `NULL` 使用 `gzgetc()` 宏在 C 中是未定义行为，不被覆盖。

## 构建与平台

下面每张表的各列依次是：前提及陈述它的 Lean 谓词；它要求什么；陈述它的目标；它的理由，以及什么不被覆盖。

| 前提 | 要求什么 | 目标 | 理由，以及什么不被覆盖 |
| --- | --- | --- | --- |
| 初始配置 | 默认 x86_64 Linux、LP64、静态构建和默认分配器：`zalloc` 与 `zfree` 各自是 `NULL` 或默认函数（`DefaultOrNull`、`DefAlloc`） | 每个目标 | 证明针对的就是这个构建和这个分配器。不被覆盖：自定义分配器，以及任何其他构建配置（[进度](progress.md)）。默认分配器失败是被覆盖的：各目标对每一种分配结果都成立。 |
| 平台字节对象范围（`ByteObjectsFit`） | 每个字节对象小于 `2^63` 字节，包括调用者的、静态的和内嵌的存储 | 见下面的列表 | LP64 下单个对象大小的上限 `PTRDIFF_MAX`（[平台](spec/platform.md)）。它既不限制内存总量，也不限制流的长度。 |

各目标在以下位置陈述 `ByteObjectsFit`：

- 每次流调用所在的堆（`StreamCallDomain`，以及 `StreamSequenceSafety` 的第 2 个子句）；
- 对 inflate 流，还包括历史中此前的每个堆，即每次调用之前和每次调用者修改之后（`StreamReachable.step`、`.rebuffer`）；deflate 的历史只在目标所陈述的那次调用上带有它；
- `compress*` 与 `uncompress*` 的目标（`CompressorSafety`、`UncompressCountedSafe`、`UncompressSingleSafe`）；
- 每次 gz 打开所在的堆，以及 gz 历史中每次调用者修改之后的堆（`GzHistory`、`GzOpenSafe`、`GzDopenSafe`），这就覆盖了调用者的路径串和模式串（[回归](../../tests/verification/regressions/gzopen-path-ptrdiff.lean)）；
- 对回调解码器，是每次 `inflateBack` 调用所在的堆和每个回调步骤之后的堆（`BackSafeReachable.step`、`BackPlatform`）。

初始化、校验和与拒绝目标不陈述它。End 目标不对调用时的堆陈述它；inflate 的历史按上面第二条带有它。有一个具体的堆满足它（`inflate_default_witness_platform`）。

目标对模型中的堆提出的条件（`Fresh`、`Uniq`、`LibraryGlobals`、`CrcGlobals`）、循环燃料、CRC 地址模型和 NULL 指针算术，都不是调用者的义务。它们在[模型的限制](model-limits.md#conditions-on-the-model-that-goals-state)中。

## 流调用：inflate 与 deflate

流函数的安全目标在每个可达的流（`StreamReachable`）上成立，只要参数满足 `StreamArguments`。

| 前提 | 要求什么 | 目标 | 理由，以及什么不被覆盖 |
| --- | --- | --- | --- |
| 流的初始化（`InitArguments`） | `strm` 是 `NULL`，或者是一个可读的记录，其 `zalloc` 与 `zfree` 各自是 `NULL` 或默认函数（`DefaultOrNull`）。`version` 是 `NULL`，或其第一个字节可读。堆是良构的（[模型的限制](model-limits.md#conditions-on-the-model-that-goals-state)）。记录的其他字段（包括 `state`）、`version` 的第一个字节和 `stream_size` 都是任意的。`Goal.inflateBackInit__safety` 多一条要求，`zlib.h` 同样有这条要求：窗口非 `NULL` 且 `windowBits` 为 8 到 15 时，窗口有 `2^windowBits` 个可写字节。 | `Goal.inflateInit2__safety`、`Goal.inflateInit__safety`、`Goal.deflateInit2__safety`、`Goal.deflateInit__safety`、`Goal.inflateBackInit__safety` | 只有 `DefaultOrNull` 比 `zlib.h` 更窄。版本不对、`stream_size` 不对和 `NULL` 流都被覆盖：调用返回错误码，并且不留下任何块（`InitResultSafe`）。见[注 1](#note-1-init-and-unset-fields)。 |
| 历史的第一次调用（`StreamReachable.inflateInit`、`.deflateInit`） | 一段历史从一次返回 `Z_OK` 的初始化调用开始：记录可读并满足 `DefaultOrNull`，`version` 的第一个字节是 `'1'`，`stream_size = 112`。 | 两个序列目标，以及通过 `StreamReachable` 涉及的每个单函数流目标 | 除 `DefaultOrNull` 外，这些就是 C 返回 `Z_OK` 的条件。对 `state` 没有任何子句。 |
| 流缓冲区（`StreamBuffers`） | 输入范围（`next_in`、`avail_in`）与输出范围（`next_out`、`avail_out`）互相分离，且都不在流拥有的存储内。每个范围是 `NULL` 或可读，输出范围还须可写。 | `Goal.inflate_safety`、`Goal.deflate_safety`、`Goal.deflateParams_safety`，以及两个序列目标中的这些调用（`StreamArguments`）。功能目标 `Goal.inflate` 与 `Goal.deflate` 也假设它。 | `zlib.h` 描述的是调用者让各缓冲区互不重叠时的调用。不被覆盖：输入与输出重叠，以及缓冲区位于流自身的状态之内。 |
| 调用之间调用者的修改（`Rebuffer`） | 在一段历史的两次调用之间，调用者只改变流记录的 `next_in`、`avail_in`、`next_out` 和 `avail_out`，以及流不拥有的内存。 | 两个序列目标；通过 `StreamReachable` 涉及的每个单函数流目标 | 这是 `zlib.h` 的规则：应用程序更新缓冲区字段，其他字段都 `must not be updated by the application`（应用程序不得更新）。不被覆盖：调用者写了记录的其他字段，或写了流拥有的块的历史。 |
| 其他流参数（`StreamArguments`） | `inflateSync`：输入范围是 `NULL` 且 `avail_in = 0`，或者可读且在流的存储之外。`deflatePrime`：还没有任何 `deflate` 调用启动过这个流（`DeflateNotStarted`）；`deflateSetHeader` 有同样的顺序规则（“头部参数”一行）。头部调用和字典调用各有自己的行。其余流调用没有参数前提。 | 该函数的安全目标，以及序列目标中的同一种调用 | 次序规则是 `zlib.h` 的（"before the first deflate() call"，即在第一次 `deflate()` 调用之前）。在一次 `deflate` 调用之后调用 `deflatePrime`，是真实 C 的未定义行为（[复现](../../tests/regression/deflate-history-domain/README.md)）。 |
| 字典缓冲区（`CallerRange`） | 字典参数是 `NULL`，或是一个可读范围（两个 `Get` 调用还要求可写），其中没有字节落在流拥有的块内。`inflateGetDictionary` 的范围有 `whave` 字节；`deflateGetDictionary` 的范围有 `min(w_size, strstart + lookahead)` 字节。 | `Goal.inflateGetDictionary_safety`、`Goal.deflateGetDictionary_safety`、`Goal.inflateSetDictionary_safety`、`Goal.deflateSetDictionary_safety`，以及序列目标中的这些调用 | 调用者的字典没有理由位于流的存储之内。不被覆盖：位于流的窗口或其他存储之内的字典缓冲区。 |
| 结果单元（`dictLength`、`pending`、`bits`） | 没有前提，也无法陈述前提。翻译把这些标量输出参数当作值传递，而不是内存。`inflateGetDictionary` 接收 `*dictLength` 的值，指针为 `NULL` 时是 `none`（`Option UInt32`）。`deflateGetDictionary`、`deflatePending` 和 `deflateUsed` 只接收每个指针是否为 `NULL`（`Bool`）。每个函数都把 C 写入的值作为另一个结果返回。 | `Goal.inflateGetDictionary_safety`、`Goal.deflateGetDictionary_safety`、`Goal.deflatePending_safety`、`Goal.deflateUsed_safety`，以及序列目标中的这些调用 | 这些目标对结果单元的内存什么都没说；C 是用普通赋值经由指针写入它的（`*dictLength = ...`）。被覆盖：结果单元是调用者的一个普通变量，并且与字典缓冲区、流记录和流拥有的存储都分开的调用。不被覆盖：其他任何调用。 |
| 头部参数（`HeaderMemory`、`DeflateNotStarted`、`DeflateHeaderLive`） | `inflateGetHeader`：头记录不是 `NULL`，不归流拥有，其 `extra`、`name` 和 `comment` 缓冲区各自是 `NULL`，或分别有 `extra_max`、`name_max`、`comm_max` 个可写字节。`deflateSetHeader`：头是 `NULL`，或是一个流不拥有的记录，其非 `NULL` 的 `extra` 有 `extra_len` 个可读字节，且没有字节落在流拥有的块内，非 `NULL` 的 `name` 和 `comment` 是短于 `2^64` 字节、以 NUL 结尾的字符串；并且还没有任何 `deflate` 调用启动过这个流。这次调用对 `name` 和 `comment` 没有关于归属的子句；那一子句在“deflate 的 gzip 头区域”一行。`deflateBound`、`deflateBound_z`：`ActiveHeader`（下面四行），并且已设置的 gzip 头在任何时候都存活，而不只是在写出期间。 | `Goal.inflateGetHeader_safety`、`Goal.deflateSetHeader_safety`、`Goal.deflateBound_safety`、`Goal.deflateBound_z_safety`，以及序列目标中的这些调用 | `inflateGetHeader` 经由这个指针写入（`head->done = 0`），所以 `NULL` 头部不被覆盖。`deflateSetHeader` 的次序规则是 `zlib.h` 的；在头部正被写出时设置的 `NULL` 头部，会被真实的 C 解引用（[复现](../../tests/regression/deflate-history-domain/README.md)）。 |
| 挂接的 gzip 头保持存活（`ActiveHeader` 中的 `HeaderMemory`） | 每次 `inflate` 调用时，在每种模式下，包括头已读完（`done` 已置位）之后：交给 `inflateGetHeader` 的记录仍是一个流不拥有的存活记录，其非 `NULL` 的 `extra`、`name` 和 `comment` 仍分别有 `extra_max`、`name_max`、`comm_max` 个可写字节，并位于流的存储之外。对 deflate 流，状态为 `GZIP_STATE` .. `HCRC_STATE`（`DeflateHeaderWriting`）期间的每次 `deflate`、`deflateParams`、`deflateBound` 和 `deflateBound_z` 调用时：交给 `deflateSetHeader` 的记录存活且不归流拥有，其非 `NULL` 的 `extra` 有 `extra_len` 个可读字节，并位于流的存储之外，非 `NULL` 的 `name` 和 `comment` 是以 NUL 结尾的字符串。`GZIP_STATE` 是 gzip 流从初始化或重置起、在任何 `deflate` 调用之前就有的状态，所以这个时段从 `deflateSetHeader` 开始。头写完之后调用者可以释放它，但 `deflateBound` 和 `deflateBound_z` 除外（见上一行）。`inflateCopy` 或 `deflateCopy` 得到的流与它的源有同一个头指针，所以这一行对副本上的调用同样成立。 | `Goal.inflate_safety`、`Goal.deflate_safety`、`Goal.deflateParams_safety`、`Goal.deflateBound_safety`、`Goal.deflateBound_z_safety`，以及两个序列目标中的这些调用 | 库保存调用者的指针，并在之后的调用中使用它。对 `inflate`，这条前提要求的比 C 用到的多：`inflate.c` 只在头部模式（`HEAD` .. `HCRC`）中读写 `state->head`。不被覆盖：调用者释放了记录或其缓冲区之后的 `inflate` 调用，`done` 置位之后也一样。对 `deflate`，这条前提要求 `extra_len` 个可读字节；C 读取的是 `extra_len mod 2^16` 个。 |
| inflate 的 gzip extra 字段（`InflateHeaderProgress`） | `inflate` 把 gzip 头（`HEAD` .. `HCRC`）读入挂接的 `gz_header` 时，其 `extra` 缓冲区（`extra_max` 字节）与尚未读取的输入分离；在 `EXTRA` 模式中，记录的 `extra_len` 不小于 `state->length`。 | `Goal.inflate_safety`，以及 `Goal.inflate_sequence_safety` 中的每次 `inflate` 调用；功能目标 `Goal.inflate` 与 `Goal.inflate_sequence` 也是如此 | 被排除的每种情形都是真实 C 在 `EXTRA` 的 `zmemcpy` 中的未定义行为（[复现](../../tests/regression/inflate-gzip-extra/README.md)）：重叠的复制，或者调用者在 extra 字段中途调低 `extra_len` 之后越过 `extra_max` 的写入。`zlib.h` 对这两种情形都没有说明。 |
| deflate 的 gzip 头区域（`DeflateHeaderApart`） | 状态为 `GZIP_STATE` .. `HCRC_STATE` 且挂接着 `gz_header` 期间，每次 `deflate`、`deflateParams`、`deflateBound` 和 `deflateBound_z` 调用时：输入范围、输出范围、extra 字段（`extra_len mod 2^16` 字节）、name 与 comment（各含其 NUL）是两两分离的字节范围，可以位于同一个块中；extra 字段、name 与 comment 位于流拥有的存储之外。输入范围和输出范围就是那次调用时 `z_stream` 各字段所指的范围；对并不使用它们的 `deflateBound` 和 `deflateBound_z` 也是如此。 | `Goal.deflate_safety`、`Goal.deflateParams_safety`、`Goal.deflateBound_safety`、`Goal.deflateBound_z_safety`，以及 `Goal.deflate_sequence_safety` 中的每次这类调用；功能目标 `Goal.deflate` 与 `Goal.deflate_sequence` 也是如此 | 这些区域没有理由重叠。name 位于输出范围或 `pending_buf` 之内，是真实 C 的未定义行为：一次刷新或一个头部字节会覆盖它的 NUL，name 循环随后读到缓冲区之外（[复现](../../tests/regression/deflate-gzip-name-output/README.md)）。`zlib.h` 对这些布局没有说明。 |
| deflate 的 gzip 头进度（`DeflateHeaderProgress`） | 在上一行所说的每次调用时，如果此前某次 `deflate` 调用在挂接的 `gz_header` 的某个字段写到一半时返回，调用者保留了已经写出的部分：字段仍覆盖已写出的部分（`gzindex`），并且在 `EXTRA_STATE`、`NAME_STATE` 或 `COMMENT_STATE` 中，该字段没有中途被置为 `NULL`（它为 `NULL` 时 `gzindex = 0`）。 | 与上一行相同的目标 | 被排除的修改是真实 C 的未定义行为（[复现](../../tests/regression/deflate-history-domain/README.md)）：被缩短的字段会被读到末尾之外；中途被改成 `NULL` 的字段会被跳过而不重置 `gzindex`，下一个字符串就从 `gzindex` 处读起，越过它的末尾。`zlib.h` 要求在第一次 `deflate` 调用之前提供头部，对头部写出期间的改动没有说明。 |
| 被拒绝的流（`RefusedInflate`、`RefusedDeflate`） | 被拒绝的流是 `NULL`，或者是一个可读的记录：其状态为 `NULL`，或其 `zalloc` 或 `zfree` 为 `NULL`，或其状态是一个被检查拒绝的存活状态记录（回指指针、`mode` 或 `status` 字段有误）。 | 除四个初始化函数之外每个有文档的流函数的安全目标的拒绝子句，以及 `Goal.inflateCopy_safety` 和 `Goal.deflateCopy_safety` 的拒绝子句；`Goal.inflate_refusal`、`Goal.deflate_refusal` | 其中包括：`End` 之后的记录、失败的复制的目的记录、对存活记录的结构体复制，以及[注 2](#note-2-refused-streams)所说的初始化失败之后的记录。同一条注列出不被覆盖的三类记录。 |
| 复制的目的流 | 在“从可达的源复制”这个子句里：目的流是一个可读的流记录，并且不是源记录（`source ≠ dest`），源使用默认分配器（`DefAlloc`）。拒绝子句只要求目的记录可读，`dest` 为 `NULL` 时则没有要求；它们没有 `source ≠ dest` 这条前提。 | `Goal.inflateCopy_safety`、`Goal.deflateCopy_safety`，以及功能目标 `Goal.inflateCopy`、`Goal.deflateCopy` | `dest == source` 且源可达时，C 的 `zmemcpy(dest, source, sizeof(z_stream))` 把一个对象复制到它自身上，这是未定义行为。源被拒绝时，C 在复制之前就返回，所以那里 `dest == source` 是被覆盖的。因模型无法表达而不被覆盖：与源记录、某个缓冲区或某个状态记录部分重叠的目的记录（[模型的限制](model-limits.md#how-the-runtime-represents-c)，地址与布局模型）。 |
| 直接调用 `deflateResetKeep` | deflate 的调用历史（`StreamOperation .deflate`）中没有对 `deflateResetKeep` 的直接调用；`deflateReset` 和 `deflateInit2_` 仍在其中。 | `Goal.deflate_sequence_safety`，以及通过 `StreamReachable` 涉及的各个单函数 deflate 目标 | `zlib.h` 把 `deflateResetKeep` 声明在 `undocumented functions (not part of the zlib API)`（未文档化函数，不属于 zlib API）之下。不被覆盖：含有直接调用的历史。 |

### 注 1：初始化与未设置的字段

在 C 中，`inflateInit` 的调用者没有设置的字段，其值是不确定的。模型里没有这样的值。未设置的整数字段取一个任意的值；未设置的指针字段取模型能够表达的某个值：`NULL`，或对某个模型对象的引用。四个初始化目标和 `Goal.inflateBackInit__safety` 对每一个这样的值都成立，因为 `InitArguments` 只约束 `zalloc` 和 `zfree`。C 的初始化函数给 `strm->state` 赋值，而不读取它。模型里没有“未初始化指针”这种值，这是模型的一处限制（[可信基础](trusted-base.md)第 2 项）。

初始化的三个非空性目标（`Goal.inflate_initialisation_domain`、`Goal.deflate_initialisation_domain`、`Goal.inflate_back_initialisation_domain`）是针对调用之前 `state` 为 `NULL` 的记录陈述的（`InitDomain`）。它们说：在每个这样的堆上，只要没有分配失败，初始化就返回 `Z_OK`。它们不是任何安全目标的前提。

### 注 2：被拒绝的流

**拒绝在哪里陈述。** 除四个初始化函数之外，每个有文档的 inflate 和 deflate 流函数的安全目标都有两个子句：对被拒绝的流（`RefusedInflate` 或 `RefusedDeflate`）的拒绝，以及对可达流的调用。`Goal.inflateCopy_safety` 和 `Goal.deflateCopy_safety` 在针对 `NULL` 参数的子句之外，还有一个针对被拒绝的源的子句。`Goal.inflate_refusal` 和 `Goal.deflate_refusal` 各用一个目标再次陈述以下函数的拒绝：`inflate`、`inflateEnd`、`inflateReset`、`inflateReset2`、`inflateGetDictionary`、`inflateSetDictionary` 和 `inflateCopy`，以及 `deflate`、`deflateSetDictionary`、`deflateParams`、`deflateGetDictionary` 和 `deflateCopy`。

**被拒绝的调用返回什么。** 返回 `Z_STREAM_ERROR`，有两个例外，都与 C 一致。`inflateMark` 返回 `-65536`。`deflateBound` 和 `deflateBound_z` 返回它们在 `sourceLen` 相同时对 `NULL` 流给出的上界，这不是错误值。

**被拒绝的调用改变了什么。** 除 `inflate`、`inflateSync` 和两个复制函数外，调用之后的堆就是调用之前的堆。源被拒绝的复制把 `NULL` 写入目的记录的 `state` 字段，与 C 相同（`dest->state = Z_NULL`），此外什么也不改；这个子句要求目的记录可读、源指针不是 `NULL`。对 `inflate` 和 `inflateSync`，目标在满足 `Fresh` 的堆上陈述：调用不写原先存活的任何块，每个存活的块都保持原样，没有块被创建或释放。这不是堆相等：这两个翻译各自会分配并释放一个四字节的局部数组，所以模型的块计数器可能增大。

**初始化失败之后的记录。** 它在 `state` 为 `NULL` 时，或者在 `zalloc` 或 `zfree` 为 `NULL` 时被拒绝。下表说明每种失败在记录里留下什么。

| 失败 | 调用之后的 `state` | 调用之后的 `zalloc`、`zfree` |
| --- | --- | --- |
| `Z_VERSION_ERROR`；`inflateBackInit_` 因窗口为 `NULL` 或 `windowBits` 不合法而返回的 `Z_STREAM_ERROR` | 与调用之前相同 | 与调用之前相同。它们原先按检查清单的要求是 `NULL` 时，不论 `state` 里是什么，记录都被拒绝 |
| 状态记录分配不出来时的 `Z_MEM_ERROR` | 与调用之前相同 | 已置为默认函数 |
| `deflateInit2_` 因参数有误返回的 `Z_STREAM_ERROR` | 与调用之前相同 | 已置为默认函数 |
| `inflateInit2_` 因 `windowBits` 有误返回的 `Z_STREAM_ERROR` | `NULL` | 已置为默认函数 |
| `deflateInit2_` 的四个缓冲区之一分配不出来时的 `Z_MEM_ERROR` | `NULL` | 已置为默认函数 |

在第 1 至 3 行中，`state` 里是调用者留下的值。`zalloc` 和 `zfree` 已设置时，这个值是 `NULL` 则记录被拒绝；它是过时指针或垃圾指针时，记录属于下面三类之一。

**不被覆盖。** 在 `zalloc` 和 `zfree` 已设置的情况下，有三类记录在拒绝的定义域之外。在 C 中，状态检查对其中每一类都会经由这个指针读取，这是未定义行为。

1. **状态字段里是垃圾地址**，例如从未初始化的自动变量 `z_stream`。模型无法表达它：这个字段是 `NULL`、一个 inflate 状态编号或一个 deflate 状态编号，而新分配内存中的指针是 `NULL`（[模型的限制](model-limits.md#how-the-runtime-represents-c)，“未初始化指针变成 NULL”一行）。
2. **悬空的状态**：字段指向一个已不存活的状态，例如原件已被结束之后还在使用的结构体复制。谓词排除它。
3. **类型不对的状态**：把 deflate 状态交给 inflate 函数，或者反过来。谓词排除它。

## 整缓冲区实用函数与校验和

| 前提 | 要求什么 | 目标 | 理由，以及什么不被覆盖 |
| --- | --- | --- | --- |
| 整缓冲区压缩（`CompressArguments`） | 源与目的缓冲区不重叠：`Separate source n dest c`。源可读，目的缓冲区在其容量范围内可写，除非这次调用是 C 会拒绝的调用（`compressRejected`）。`compress` 与 `compress2` 的长度单元不能是 `NULL`；只有 `_z` 形式允许 `NULL` 单元。 | `Goal.compress_safety`、`Goal.compress2_safety` 及其 `_z` 形式 | 源与目的没有理由重叠。长度单元 `*destLen` 在翻译中是一个标量值（`Option UInt64`），不是内存，所以这些目标对它的内存什么都没说。不被覆盖：源与目的重叠，以及长度单元不是一个与两者都分开的可写变量。 |
| 计数解压（`UtilitySeparation`、`UncompressCountedSafe`、`UncompressSingleSafe`） | 源、目的缓冲区、目的长度单元和源长度单元两两分离。`uncompress` 与 `uncompress_z` 需要源与目的缓冲区分离、长度单元与数据分离。长度单元是八个可读可写的字节（`LengthCell`）；`uncompress` 与 `uncompress2` 的单元不能是 `NULL`。 | `Goal.uncompress_safe`、`Goal.uncompress2_safe` 及其 `_z` 形式 | 这些区域没有理由重叠。这里的单元 `*destLen` 和 `*sourceLen` 在翻译中是内存，所以分离是一条写明的前提。不被覆盖：长度单元与数据缓冲区或另一个单元别名。 |
| Adler 初始化查询（`AdlerBufferBytes`） | 只有长度为零时 `buf` 才可以是 `NULL`；非 `NULL` 的可读缓冲区保留完整的长度范围。 | `Goal.adler32_safety`、`Goal.adler32_z_safety`，以及功能目标 `Goal.adler32`、`Goal.adler32_z` | 比 zlib 1.4 的 `zlib.h` 更窄：后者允许 `buf` 为 `NULL`，对 `len` 不加条件。`NULL` 且 `len = 1` 时，C 会读 `buf[0]`。CRC 的目标仍用 `BufferBytes`，它容许 `NULL` 配任意长度。 |
| CRC 组合算子 | 算子是 `crc32_combine_gen` 或 `crc32_combine_gen64` 返回的值。 | `Goal.crc32_combine_op_safety` | 这是 `zlib.h` 为 `crc32_combine_op` 规定的定义域。不被覆盖：任意的 `op` 值。 |

## 回调解码器

`Goal.inflate_back_sequence_safety` 在 `BackSafeReachable` 的历史上成立。`Goal.inflateBack_safety` 和 `Goal.inflateBackEnd_safety` 中关于历史的子句也是如此，它们重复了序列目标的子句：下面每一行只要写了序列目标，对这两个目标同样成立。`Goal.inflateBackInit__safety` 没有这些前提；它的前提在“流的初始化”一行。

| 前提 | 要求什么 | 目标 | 理由，以及什么不被覆盖 |
| --- | --- | --- | --- |
| 回调解码器的初始化（`BackSafeReachable.init` 中的 `BackInitArguments`） | 流记录可读；`zalloc` 与 `zfree` 各自是 `NULL` 或默认函数；`version` 指向一个可读的字节 `'1'`；`stream_size = 112`；调用返回了 `Z_OK`。记录的其他字段（包括 `state`）可以取任意值。 | `Goal.inflate_back_sequence_safety` | 除默认分配器外，这些就是 C 返回 `Z_OK` 的条件。失败的初始化调用不开始任何历史；它的安全性是 `Goal.inflateBackInit__safety`。 |
| 回调（`CallbackProtocol`） | 调用者为它的 `in` 和 `out` 函数提供一个协议；各子句见下面的列表。 | `Goal.inflate_back_sequence_safety` | 回调是调用者的代码，所以它们做什么是一条前提。描述符对象可以与窗口共用同一次分配，只要在切片之外。 |
| 调用之间调用者的修改（`BackSafeReachable.caller`） | 两次调用之间，调用者的修改是一次 `Rebuffer`（“调用之间调用者的修改”一行），并且保持窗口切片，以及每个仍存活的块的只读标志。 | `Goal.inflate_back_sequence_safety` | 窗口就是解码器的历史。这比 `zlib.h` 更窄：`zlib.h` 没有禁止在两次调用之间写窗口。窗口指针位于其所在块的偏移 0 时，在模型中流拥有这个块（`InflateOwned`），`Rebuffer` 于是在两次调用之间保持整个块，而不只是切片。C 不读取此前的窗口字节（`inflateBack` 在每次调用开始时置 `state->whave = 0`），这一点**尚未由证明确认**。C 代码无法改变只读标志，所以那个子句不排除任何调用者。 |
| 回调输入总量 | `protocol.inputBound < 2^48`：一次 `inflateBack` 调用总共得到的输入少于 `2^48` 字节。这个总量包括第一个片段（调用时的 `next_in`、`avail_in`）和各次 `in` 调用交出的每个片段。 | `Goal.inflate_back_sequence_safety` | 运行时把每个循环限制在 `2^64` 次迭代以内（[模型的限制](model-limits.md#conditions-on-the-model-that-goals-state)），而解码循环的每一轮至少读一位，所以得到更多输入的调用可能在 C 还会继续的地方耗尽燃料。`zlib.h` 没有这样的限制。 |
| 回调解码器窗口 | `8 ≤ windowBits ≤ 15`，窗口不是 `NULL` 并且有 `2^windowBits` 个可写字节，这是 `zlib.h` 的要求；另外还要求：窗口是某个堆字节块的切片。 | `Goal.inflate_back_sequence_safety`，通过 `BackSafeReachable.init` | 模型中另外唯一可写的字节视图是 deflate 状态内的 depth 数组，它是库的存储，调用者无法指名。不被覆盖：位于那里的窗口。 |
| 回调解码器输入片段 | 每个输入片段都位于某个堆字节块中：调用者给出的第一个片段（`BackFirstChunk`），以及 `in` 交出的每个片段（`BackPlatform`）。 | `Goal.inflate_back_sequence_safety` | `inflate_fast` 在这个片段上运行，而它的证明针对堆上的字节块（[模型的限制](model-limits.md#functional-and-model-statements)，“快速解码器辅助函数”）。不被覆盖：位于模型其他存储中的片段，例如结构体的字段或静态数据；C 能处理任何可读存储中的片段。 |

`CallbackProtocol` 的各个子句：

- `in` 和 `out` 各自都会返回而不出故障，并且只改变调用者自己的块；这些块不包括状态和流记录。
- 关于一次 `in` 或 `out` 调用的子句只在这样的堆上才被要求：流是这个窗口上的一个有效回调解码器（`CallbackEntry`）。库交给回调的只有这样的堆。没有这个限制，就不可能存在任何协议（[回调](proof/callbacks.md)；[反例](../../tests/verification/regressions/inflateback-protocol-vacuous.lean)）。
- 两者都保持窗口切片中的字节。
- `in` 交出的片段可读，并且与窗口、状态和流记录分离。`out` 保持当前的输入片段可读。
- 总输入有一个有限的上界（`inputBound`）。
- 每个回调都让堆保持良构（`Fresh`、`Uniq`），它新建的每个块都属于调用者自己（`ExternalFrame`）。
- 协议带有一个不变量，说的是堆以及“已供给和已交付字节”的日志。每个回调都保持它。这个不变量只能依赖调用者自己的块和堆的分配器字段，不能依赖窗口切片中的字节（`CallbackProtocol.local_`）。

关于同一次调用还有两条前提，它们是目标第三个子句的前提，不是 `CallbackProtocol` 的子句：第一个片段（`next_in`、`avail_in`）可读，并且与窗口分离；在调用 `inflateBack` 时的堆上，不变量成立。`Goal.inflateBack_call_domain` 表明这些前提和一个协议在一次具体的调用上同时成立。

## Gzip 文件接口

`Goal.gz_sequence_safety` 在一个句柄的每段历史（`GzHistory`）上、对每个文件系统世界成立。每个 gz 函数的安全目标（`Goal.<function>_safety`）把它的一个子句限制到这个函数上，前提相同：下面写了 `Goal.gz_sequence_safety` 的行，对该行所说的那些函数的目标同样成立。这些目标说的是打过补丁的源码（[补丁](../../patches/README.md) 0002 至 0005）。gz 世界是堆之外的可信语义：[外部 I/O 模型](design/external-io.md)描述它，[可信基础](trusted-base.md)说明对它作了哪些假设。

| 前提 | 要求什么 | 目标 | 理由，以及什么不被覆盖 |
| --- | --- | --- | --- |
| Gz 打开参数（`GzOpenSafe`、`GzDopenSafe`、`GzHistory.open`） | `path` 与 `mode` 各自是 `NULL`，或是短于 `2^64` 字节、以 NUL 结尾的字符串；堆是良构的，其字节对象都不超限；世界是一个良构的文件系统（`FileSystem`）。 | `Goal.gz_sequence_safety` | C 把每个字符串一直读到它的 NUL。被覆盖：每个描述符、每种模式文本和每个世界，包括每一种失败。不被覆盖：在自身对象之内没有以 NUL 结尾的路径或模式。 |
| Gz 调用者缓冲区（`GzArguments` 中的 `GzRange`） | `gzread`、`gzfread`、`gzwrite`、`gzfwrite`、`gzputs`、`gzgets` 与 `gzerror` 的调用者缓冲区可读（读取调用的缓冲区和 `gzerror` 的 `errnum` 还须可写），并且与句柄拥有的块分开（`GzOwned`）。`gzputs` 的参数是以 NUL 结尾的字符串（`CString`），范围包含它的 NUL：没有 NUL 的可读字节，以及 `NULL`，都在范围之外。 | `Goal.gz_sequence_safety` | 库在调用期间会释放并改写它自己的块（[见下](#why-the-handles-own-strings-are-excluded)）。不被覆盖：位于句柄的块之内的缓冲区。 |
| Gz printf 字符串（`GzArguments`） | `gzprintf` 与 `gzvprintf` 的格式串以及每个指针参数都与句柄拥有的块分开（`GzOwned`）。 | `Goal.gz_sequence_safety` | 理由与上一行相同。 |
| Gz printf 调用（调用者的义务；`GzArguments`） | `vsnprintf` 的调用对格式串和参数在 C 中有定义，且格式串中没有 `%n`：没有前提陈述这一点，由调用者保证，和每次 printf 调用一样（[可信基础](trusted-base.md)）。文件以写方式打开且不处于错误状态时，`GzArguments` 要求格式串是以 NUL 结尾的字符串，每个指针参数都指向未被释放的块。随后 `gz_init`、`gz_zero` 或 `gz_vacate` 失败时它也这样要求，尽管 C 在调用 `vsnprintf` 之前就返回了。 | `Goal.gz_sequence_safety` | `vsnprintf` 是按契约建模的外部调用，所以每种有效格式都被覆盖，包括浮点和 `%p`。不被覆盖：通过参数写入的 `%n`，以及在 `vsnprintf` 之前返回、格式串又不是字符串的调用。 |
| Gz 调用者步骤与世界步骤（`GzCallerFrame`、`GzWorldStep`） | 两次调用之间，调用者可以改变句柄不拥有的任何块，也可以释放自己的缓冲区；堆保持良构，其字节对象都不超限。世界可以变成任何良构的文件系统：别的参与者可以关闭或重用句柄的描述符。 | `Goal.gz_sequence_safety` | 句柄的块属于库。不被覆盖：调用者写了句柄拥有的块的历史。世界步骤容许的比真实系统更多。 |
| Gz 读取调用的终止（`ReadsFinite`） | 对 `gzread`、`gzfread`、`gzgetc`、`gzgetc_`、`gzgets` 和 `gzungetc`：句柄的描述符有一个小于 `2^61` 字节的有限读取预算（`fs.readBudget fd = some b` 且 `b < 2^61`），即该描述符还能交付的总字节数。这条前提还说描述符编号不为负（`HasBudget`）。 | `Goal.gz_sequence_safety` 中关于终止的那一半，且只针对这六个调用 | 在无穷无尽的来源上，C 有两个循环不会结束（[见下](#why-a-read-budget)）。这条前提不排除任何故障：无故障的那一半和后置条件对每个世界都成立，不需要预算。`gzdirect`、写入一侧和 `gzseek` 不需要它。 |
| Gz 操作系统事实 | 非空的 `write` 从不返回 0；`close` 即使失败也会释放描述符。 | `Goal.gz_sequence_safety`，通过世界模型 | 这是 Linux 的行为，被信任，没有检查。第一条为 `gz_comp` 的写循环定界。**尚未由证明确认**：按对 C 的解读，一个永远返回 0 的 `write` 会让 `gz_comp` 永远循环。模型中没有带这种 `write` 的世界，所以没有定理陈述这一点。 |

`strerror` 的模型是模型的限制，不是调用者的义务：见[模型的限制](model-limits.md#conditions-on-the-model-that-goals-state)，“外部错误字符串”一行。

### 为什么排除句柄自己的字符串

`gzerror` 返回的字符串就是 `state->msg`。库每次清除或替换错误时，都在 `gz_error` 里释放它，而许多入口函数在读取自己的参数之前就会这样做。所以把这个字符串再传回同一个句柄上的调用，在 C 中可能是释放后使用。在上一次写入停滞的写入端上，`gzprintf(f, "%s", gzerror(f, &e))` 先释放这条消息，再在 `vsnprintf` 中读它：AddressSanitizer 报告堆释放后使用（[复现](../../tests/regression/gzprintf-error-string/README.md)）。`zlib.h` 只提醒说，之后的 `gzerror` 调用可能使这个字符串失效。这条前提对每个接受调用者内存的调用都排除句柄自己的块，不论那个调用是否释放这条消息。

### 为什么需要读取预算

C 里有两个循环在无穷无尽的来源上不会结束：来源永远交付只解码出空内容的数据（空的 gzip 成员）时，`gz_fetch` 会一直循环；待跳过的量极大时，`gz_skip` 会永远读下去。任何有限的循环燃料都覆盖不了这种情况。有读取预算时，每个循环都有界。

`2^61` 这个数是模型的限制，不是 zlib 的。模型的每个循环有 `2^64` 次迭代的燃料。读取循环由一些度量限定，这些度量由剩余的输入、读取预算和尚待交付的字节数构成（`fetchRank`，以及 `gz_read` 与 `gz_skip` 的度量）。一次取数会把缓冲区填满，除非它失败、输入结束、到达 `GZ_OFF_MAX`，或者降低了 `fetchRank`；所以小于 `2^61` 的预算使这些度量以及迭代次数都低于 `2^64`。某个上界是必需的：`2^70` 字节、每个 20 字节的空 gzip 成员所需要的轮数超过循环燃料（[经过检查的计算](../../tests/verification/regressions/gz-read-budget-fuel.lean)）。

预算按描述符编号记：`close` 之后被重用的编号继承剩余的预算。`gzdopen` 会拒绝负的描述符，所以没有句柄来自负描述符。

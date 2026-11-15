<!-- source-sha256: a01d5fb3060b456e56e44269b9303ad3e2fd758eac61ced72ff01b34417629f4 -->
# 偏离记录：定理假设了什么

本页列出已登记安全目标中比 `zlib.h` 更窄、或读者容易忽略的前提，以及与之相关的每一条模型限制。完整的清单是 Lean 命题本身。前提之外的调用不在覆盖范围内：既没有证明它安全，也不声称它不安全。每条前提都显式写在 Lean 命题中；表中每一行写出陈述它的谓词。凡是 Lean 谓词允许 `NULL` 的地方都允许 `NULL`。

- **在这些前提下已证明：** 必需的安全目标，位于 `ZlibF/Spec/Safety/` 和 `ZlibF/Spec/Public/`（状态见[进度](progress.md#scope)）。
- **所作假设：** 下面各行，以及模型本身（[可信基础](trusted-base.md)）。
- **不覆盖：** 违反某条前提的调用。已知真实 C 在那里会出错时，该行给出复现的链接；[Sanitizer 报告](sanitizer-reports.md)列出全部复现。

比 `zlib.h` 更窄的前提也写在陈述它的定义的文档注释中。任何限制都不能成为丢掉失败的公开用例的理由：目标写错了，就连同反例一起修正；翻译或运行时错了，就在那一层修正（[验证策略](anti-cheating.md)）。API 手册所用的词汇见[契约约定](spec/api/contracts.md)。

## 构建、平台与模型中的堆

| 领域 | 当前限制 | 后果 |
| --- | --- | --- |
| 初始配置 | 默认 x86_64 Linux、LP64、静态构建和默认分配器 | 其他构建配置不在计划内（[范围](progress.md#scope)）。`zalloc` 或 `zfree` 为自定义函数的流在所有目标之外（`DefaultOrNull`、`DefAlloc`）。默认分配器的失败在范围内：安全目标对每一种分配结果都成立。 |
| 平台字节对象范围（`ByteObjectsFit`） | 每个表示出的字节对象小于 `2^63` 字节，包括调用者、静态和内嵌存储 | 这是接受的[系统环境前提](spec/platform.md)：LP64 的 `PTRDIFF_MAX` 对象大小上限。它按对象计，不限制总内存或流的总长度。安全目标在以下位置陈述它：每次流调用所在的堆（`StreamCallDomain`，以及 `StreamSequenceSafety` 的第 2 条）；对 inflate 流，还包括历史中此前的每个堆，即每次调用之前和每次调用者修改之后（`StreamReachable.step`、`.rebuffer`），而 deflate 历史只在目标所陈述的那次调用上带有它；`compress*` 与 `uncompress*` 的目标（`CompressorSafety`、`UncompressCountedSafe`、`UncompressSingleSafe`）；每次 gz 打开所在的堆以及 gz 历史中每次调用者修改之后的堆（`GzHistory`、`GzOpenSafe`、`GzDopenSafe`），这覆盖调用者的路径串和模式串（[回归](../tests/verification/regressions/gzopen-path-ptrdiff.lean)）；对回调解码器，则是每次 `inflateBack` 调用所在的堆和每个回调步骤之后的堆（`BackSafeReachable.step`、`BackPlatform`）。初始化、End、校验和与拒绝目标不需要它。该前提可满足：公开的调用者见证具有它（`inflate_default_witness_platform`）。功能目标（`Goal.inflate`、`Goal.inflate_sequence`、各实用函数契约、`Goal.gzopen`、`Goal.gzopen64`、`Goal.gz_initialisation_domain`）以同样方式陈述它。证明操作系统的限制不属于 zlib 证明。 |
| 堆的良构性（`Fresh`、`Uniq`、`LibraryGlobals`、`CrcGlobals`） | 初始化、打开、`compress*` 或 `uncompress*` 调用开始时的堆，在 `nextBlk` 及以上没有存活块（`Fresh`），每个块号至多有一个对象（`Uniq`），并带有选定构建的常量表（`LibraryGlobals`）。CRC 目标只要求两张 CRC 表（`CrcGlobals`），`inflate` 的拒绝只要求 `Fresh`。两次调用之间调用者的修改保持这三者（`Rebuffer`、`GzCallerFrame`）。 | 这些是对模型中堆的条件，不是 `zlib.h` 加给调用者的义务，但它们仍然是前提。`Fresh` 并不表示 `nextBlk` 以下的块号在各表之间唯一；`Uniq` 表示这一点（[可信基础](trusted-base.md)）。 |
| 循环额度 | 每个翻译出的循环至多运行 `2^64` 次迭代；耗尽上界即 `Fault.outOfFuel` | 结论为 `.ok` 的安全目标证明了这个上界永远不会达到。在 C 可能无界循环、而证明又推不出上界的地方，目标带有一个给出上界的前提：下文的回调输入总量和 gz 读取预算。 |
| CRC 地址和字访问 | `addrOf` 只观察地址低位。堆字节块保留对齐起点；静态和内嵌字节对象有任意稳定余数。字加载按字节组装 | 通用 ABI 布局、任意原始块起点和 C 转换的别名语义仍不在该抽象内。公开校验和定义域不变。[静态地址回归](../tests/verification/regressions/crc-static-address.lean)保留了此前模型反例的输入，作为正向检查。 |
| 空指针算术 | `Ptr.add` 允许空指针加零；`Ptr.diff` 对空指针故障，而压缩器辅助函数允许空指针减空指针 | 模型允许不等于 C 有定义。[安全性规范](spec/safety.md#null-pointers-and-pointer-differences)区分操作和语言规则。[分配回归](../tests/regression/compress-allocation/README.md)为零容量空目标保留这一区别。 |

## 流调用：inflate 与 deflate

流函数的安全目标在每个可达的流（`StreamReachable`）上成立，只要参数满足 `StreamArguments`。`zlib.h` 针对调用者互相分开的缓冲区来描述这些调用；目标把分离写成假设。

| 领域 | 当前限制 | 后果 |
| --- | --- | --- |
| 流的初始化（`InitDomain`） | 流记录可读；`zalloc` 与 `zfree` 各自为 `NULL` 或默认函数（`DefaultOrNull`）；记录的 `state` 字段为 `NULL`；`version` 指向一个可读字节 `'1'`；调用传入 `stream_size = 112`。堆是良构的（见上一行）。 | 这是 `Goal.inflateInit2__safety`、`Goal.inflateInit__safety`、`Goal.deflateInit2__safety`、`Goal.deflateInit__safety` 以及 `BackSafeReachable.init` 的前提。流历史的第一次调用（`StreamReachable.inflateInit`、`.deflateInit`）有同样的前提，但没有关于 `state` 的那一条。`zlib.h` 要求调用者设置 `zalloc`、`zfree` 和 `opaque`；它不要求 `state` 为 `NULL`，C 的初始化函数也不读取 `state` 就覆盖它。初始化之前 `state` 不为 `NULL` 的记录不在初始化安全目标之内。错误的版本、错误的 `stream_size` 和 `NULL` 流不在这些目标中：它们是功能目标 `Goal.inflateInit2_`、`Goal.inflateInit_`、`Goal.deflateInit2_` 和 `Goal.deflateInit_` 的拒绝分支，这些功能目标已登记。 |
| 流缓冲区（`StreamBuffers`） | 输入范围（`next_in`、`avail_in`）与输出范围（`next_out`、`avail_out`）互相分离，且都不在流自己拥有的存储内。每个范围或为 NULL，或可读，输出范围还须可写。 | 它是每次 `inflate`、`deflate` 和 `deflateParams` 调用的前提（`StreamArguments`），因而是 `Goal.inflate_safety`、`Goal.deflate_safety`、`Goal.deflateParams_safety` 和两个序列安全目标的前提；功能目标 `Goal.inflate` 与 `Goal.deflate` 也以它为前提。输入与输出重叠，或缓冲区落在流自身状态内的调用不在覆盖范围内。 |
| 调用之间调用者的修改（`Rebuffer`） | 在一段历史的两次调用之间，调用者只改变流记录的 `next_in`、`avail_in`、`next_out` 和 `avail_out`，以及流不拥有的内存。 | 这是 `zlib.h` 的规则：应用程序更新缓冲区字段，其余字段“不得由应用程序更新”。调用者写入记录的其他字段或流拥有的块的历史，不在序列目标之内。 |
| 其他流参数（`StreamArguments`） | `inflateSync`：输入范围为 `NULL` 且 `avail_in = 0`，或者可读且在流的存储之外。`inflateGetHeader`：头记录不为 `NULL`，不被流拥有，其 `extra`、`name` 和 `comment` 缓冲区各自为 `NULL` 或在 `extra_max`、`name_max`、`comm_max` 字节内可写（`HeaderMemory`）。`deflateSetHeader`：头为 `NULL`，或是一个流不拥有的记录，其非 `NULL` 的 `extra` 在 `extra_len` 字节内可读，非 `NULL` 的 `name` 和 `comment` 是短于 `2^64` 字节、以 NUL 结尾的字符串；并且还没有任何 `deflate` 调用启动过这个流（`DeflateNotStarted`）。`deflatePrime`：还没有任何 `deflate` 调用启动过这个流。`deflateBound`、`deflateBound_z`：`ActiveHeader`（下面提到它的四行），并且已设置的 gzip 头在任何时候都仍然存活，而不只是在写入期间（`DeflateHeaderLive`）；它们是 `Goal.deflateBound_safety` 和 `Goal.deflateBound_z_safety` 的前提。其余流调用没有参数前提。 | 每一条都是该函数安全目标的前提，也是序列目标中同一调用的前提。顺序规则来自 `zlib.h`（“在第一次 deflate() 调用之前”）；被排除的顺序是真实 C 的未定义行为（[复现](../tests/regression/deflate-history-domain/README.md)）。头为 `NULL` 的 `inflateGetHeader` 在目标之外：C 会通过该指针写入（`head->done = 0`）。 |
| 挂接的 gzip 头保持存活（`ActiveHeader` 中的 `HeaderMemory`） | 每次 `inflate` 调用时，在每种模式下，包括头已读完（`done` 已置位）之后：交给 `inflateGetHeader` 的记录仍是一个流不拥有的存活记录，其非 `NULL` 的 `extra`、`name` 和 `comment` 仍在 `extra_max`、`name_max`、`comm_max` 字节内可写，并位于流的存储之外。`deflate` 写头期间（`GZIP_STATE` .. `HCRC_STATE`）：交给 `deflateSetHeader` 的记录存活且不被流拥有，其非 `NULL` 的 `extra` 在 `extra_len` 字节内可读，非 `NULL` 的 `name` 和 `comment` 是以 NUL 结尾的字符串。头写完之后调用者可以释放它，但 `deflateBound` 和 `deflateBound_z` 除外（见上一行）。 | `ActiveHeader` 的一个合取项，因此是 `Goal.inflate_safety`、`Goal.deflate_safety`、`Goal.deflateParams_safety`、`Goal.deflateBound_safety`、`Goal.deflateBound_z_safety` 的前提，也是 `Goal.inflate_sequence_safety` 和 `Goal.deflate_sequence_safety` 中每次这类调用的前提。对 `inflate`，它要求的比 C 用到的多：`inflate.c` 只在头部模式（`HEAD` .. `HCRC`）中读写 `state->head`，`done` 置位之后不再访问。调用者在 `done` 之后释放该记录或其缓冲区、然后再次调用 `inflate` 的情形不在覆盖范围内。`inflateReset` 会解除该记录的挂接。对 `deflate`，前提要求 `extra_len` 个可读字节；C 只读 `extra_len mod 2^16` 个。 |
| 字典缓冲区（`CallerRange`） | 字典参数为 `NULL`，或是一个可读范围（两个 `Get` 调用还要求可写），其中没有字节落在流拥有的块内。`inflateGetDictionary` 的范围有 `whave` 字节；`deflateGetDictionary` 的范围有 `min(w_size, strstart + lookahead)` 字节。 | 适用于 `inflateGetDictionary`、`deflateGetDictionary`、`inflateSetDictionary` 与 `deflateSetDictionary`。位于流的窗口或其他存储内的字典缓冲区不在覆盖范围内。 |
| inflate gzip extra 字段（`InflateHeaderProgress`） | `inflate` 把 gzip 头（`HEAD` .. `HCRC`）读入挂接的 `gz_header` 时，其 `extra` 缓冲区（`extra_max` 字节）与未读输入分离；在 `EXTRA` 中，头记录的 `extra_len` 不小于 `state->length`。 | `ActiveHeader` 的一个合取项，因此是 `Goal.inflate_safety` 以及 `Goal.inflate_sequence_safety` 中每次 `inflate` 调用的前提，功能目标 `Goal.inflate` 与 `Goal.inflate_sequence` 同样如此。每个被排除的情形都是真实 C 在 EXTRA 的 `zmemcpy` 中的未定义行为（[复现](../tests/regression/inflate-gzip-extra/README.md)）：重叠复制，或调用者在 extra 字段内调低 `extra_len` 后越过 `extra_max` 写入。zlib.h 没有说明这两种布局是否允许。 |
| deflate gzip 头区域（`DeflateHeaderApart`） | `deflate` 写入挂接的 `gz_header`（`GZIP_STATE` .. `HCRC_STATE`）期间，输入范围、输出范围、extra 字段（`extra_len mod 2^16` 字节）、name 与 comment（各含其 NUL）两两为分离的字节范围，可以位于同一块中；extra、name 与 comment 位于流所拥有的存储之外。 | `ActiveHeader` 的一个合取项，因此是 `Goal.deflate_safety`、`Goal.deflateParams_safety`、`Goal.deflateBound_safety`、`Goal.deflateBound_z_safety` 以及 `Goal.deflate_sequence_safety` 中每次这类调用的前提，功能目标 `Goal.deflate` 与 `Goal.deflate_sequence` 同样如此。这些区域没有重叠的理由。其中两种被排除的情形是真实 C 的未定义行为（[复现](../tests/regression/deflate-gzip-name-output/README.md)）：位于输出范围或 `pending_buf` 中的 name，其 NUL 被刷新或头字节覆盖，name 循环越过缓冲区读取。zlib.h 没有说明这些布局是否允许。 |
| deflate gzip 头进度（`DeflateHeaderProgress`） | 每次写入挂接 `gz_header` 的 `deflate` 调用中，调用方保持已写部分：字段仍覆盖已写部分（`gzindex`），且在 `EXTRA_STATE`、`NAME_STATE` 或 `COMMENT_STATE` 中该字段不会中途被置为 `NULL`（为 `NULL` 时 `gzindex = 0`）。 | `ActiveHeader` 的一个合取项，因此是 `Goal.deflate_safety`、`Goal.deflateParams_safety`、`Goal.deflateBound_safety`、`Goal.deflateBound_z_safety` 以及 `Goal.deflate_sequence_safety` 中每次这类调用的前提，功能目标 `Goal.deflate` 与 `Goal.deflate_sequence` 同样如此。被排除的修改是真实 C 的未定义行为（[复现](../tests/regression/deflate-history-domain/README.md)）：被缩短的字段会越界读取；中途置为 `NULL` 的字段被跳过而 `gzindex` 不被重置，下一个字符串从 `gzindex` 起读取，越过其末尾。zlib.h 要求调用方在第一次 `deflate` 调用之前提供头部；它没有说明写入期间记录能否改变。 |
| 被拒绝的流（`RefusedInflate`、`RefusedDeflate`；`Goal.inflate_refusal`、`Goal.deflate_refusal`） | 被拒绝的流是 `NULL`，或者是一个可读记录，其状态为 `NULL`、其 `zalloc` 或 `zfree` 为 `NULL`，或其状态是一个被检查拒绝的存活状态记录（反向指针、模式或状态错误）。 | 这包括 `End` 之后、初始化失败之后、复制失败的目标，以及存活记录的结构体副本。状态字段为垃圾指针的记录在定义域之外，例如从未初始化的自动 `z_stream`。检查会经由该指针读取，在 C 中这是未定义行为。模型同样无法表达它：在模型中，新内存里的指针为 `NULL`（`docs/trusted-base.md`，“Uninitialised pointers become NULL”一行）。 |
| 复制目标（`Goal.inflateCopy_safety`、`Goal.deflateCopy_safety`，以及功能目标 `Goal.inflateCopy`、`Goal.deflateCopy`） | 目标是一个可读的流记录，且不是源记录（`source ≠ dest`）。源带有默认分配器（`DefAlloc`）。模型把 `z_stream` 记录放在自己的表中，与字节和字缓冲区以及状态记录分开。因此无法表达部分重叠源记录、缓冲区或源所拥有的状态记录的目标。 | 当 `dest == source` 时，C 的 `zmemcpy(dest, source, sizeof(z_stream))` 把对象复制到自身上，这是未定义行为；该情况不在覆盖范围内。部分重叠的目标同样在定理之外：独立的记录表把它假设掉了（`docs/trusted-base.md`，地址与布局模型）。zlib.h 没有说明是否允许这种布局。 |
| 直接调用 `deflateResetKeep` | deflate 调用历史（`StreamOperation .deflate`）中没有对 `deflateResetKeep` 的直接调用；`deflateReset` 和 `deflateInit2_` 仍在其中 | 这不是比 zlib.h 更窄的限制：zlib.h 把 `deflateResetKeep` 声明在 `/* undocumented functions (not part of the zlib API) */` 之下，直接调用它的历史在已文档化的 API 之外，它的目标也不是必需的公开目标（[进度](progress.md#scope)）。真实 C 在那里不安全：在 `deflateResetKeep`、`deflate(Z_BLOCK)`、`deflateCopy` 以及副本上的一次 `Z_RLE` 或 `Z_HUFFMAN_ONLY` 刷新之后，之后的 `deflate` 会沿一个未初始化的 `prev` 槽前进并读到窗口之外（`docs/findings/deflate-copy-pending-prev`）；不做复制时，之后的匹配可能出错（`docs/findings/deflate-resetkeep-stale-hash`）。单次调用的安全性（无故障、终止）仍被证明；`deflateReset` 经过它。 |

## 整缓冲区实用函数与校验和

| 领域 | 当前限制 | 后果 |
| --- | --- | --- |
| 整缓冲区压缩（`CompressArguments`） | 源与目标不重叠：`Separate source n dest c`。 | 它是 `Goal.compress_safety`、`Goal.compress2_safety` 及其 `_z` 形式的前提。源可读，目标在其容量内可写，除非该调用是 C 会拒绝的调用（`compressRejected`）。`compress` 与 `compress2` 的长度单元不为 `NULL`；只有 `_z` 形式允许 `NULL` 单元。源与目标重叠的调用不在覆盖范围内。长度单元 `*destLen` 在翻译中是一个标量值（`Option UInt64`，`ZlibF/Zlib/compress.c.lean`），不是内存：与源或目标重叠的单元无法表达，也不在覆盖范围内。这限制了 `Goal.compress_safety`、`Goal.compress2_safety` 及其 `_z` 形式。 |
| 计数解压（`UtilitySeparation`、`UncompressCountedSafe`、`UncompressSingleSafe`） | 源、目标、目标长度单元和源长度单元两两分离。`uncompress` 与 `uncompress_z` 需要源与目标、长度单元与数据的分离。 | 它是 `Goal.uncompress_safe`、`Goal.uncompress2_safe` 及其 `_z` 形式的前提。长度单元是八个可读可写的字节（`LengthCell`）；`uncompress` 与 `uncompress2` 的单元不为 `NULL`。长度单元与数据缓冲区或另一个单元重叠的调用不在覆盖范围内。与 `compress*` 不同，单元 `*destLen` 和 `*sourceLen` 在翻译中是内存（`ZlibF/Zlib/uncompr.c.lean`），所以这里的分离是写明的前提，而不是模型的限制。 |
| Adler 初始化查询 | `AdlerBufferBytes` 只允许零长度时为 NULL；非空可读对象保留原定义域 | 该显式限制窄于固定头文件对 NULL 不加限定的表述。它适用于 `Goal.adler32_safety` 和 `Goal.adler32_z_safety`，也适用于功能目标 `Goal.adler32` 和 `Goal.adler32_z`。CRC 目标保留 `BufferBytes`，它允许任意长度下的 `NULL`。上游 [PR #1364](https://github.com/madler/zlib/pull/1364) 报告了对 NULL `buf` 的单字节读取；维护者于 2026 年 11 月 6 日关闭该请求，保留代码，并宣布将在 zlib.h 中加入对 `len` 的限制。`develop` 头 `99623ef7097352da7993ba614161fd6a311e046e` 尚未包含该文字；文字合入后需按其复核本行。 |
| CRC 组合算子 | `Goal.crc32_combine_op_safety` 取的算子是 `crc32_combine_gen` 或 `crc32_combine_gen64` 返回的值 | 这是 `zlib.h` 为 `crc32_combine_op` 规定的定义域，不是收窄。任意的 `op` 值不在覆盖范围内。 |

## 回调解码器

`Goal.inflate_back_sequence_safety` 在 `BackSafeReachable` 的历史上成立。

| 领域 | 当前限制 | 后果 |
| --- | --- | --- |
| 回调（`CallbackProtocol`） | 调用者为它的 `in` 和 `out` 函数提供一个协议：每个函数都不出故障地返回，只改变调用者自己的块（其中不含状态和流记录），保持窗口切片，交出的输入块可读，并与窗口、状态和流记录分离；`out` 保持当前输入块可读；总输入有一个有限上界（`inputBound`）。第一个输入块（`next_in`、`avail_in`）可读并与窗口分离。每个回调还保持堆的良构性（`Fresh`、`Uniq`），它新建的每个块都属于调用者自己的块（`ExternalFrame`）。协议带有一个关于堆和已供给、已交付字节日志的不变量：调用 `inflateBack` 时它成立，每个回调都保持它。该不变量只能依赖调用者自己的块和堆的分配器字段，不能依赖窗口切片中的字节（`CallbackProtocol.local_`）：它忽略窗口字节和不属于调用者的块，保留其余一切效果。两次调用之间，调用者的修改是一次 `Rebuffer`（“调用之间调用者的修改”一行），并保持窗口切片以及每个仍存活的块的只读标志（`BackSafeReachable.caller`）。 | 这些是调用者代码的契约，不是假设的库契约，并保持显式。描述符对象可以共享窗口所在分配中切片以外的部分。C 代码无法改变只读标志，所以最后一条不排除任何 C 调用者。 |
| 回调输入总量 | `Goal.inflate_back_sequence_safety` 假设 `protocol.inputBound < 2^48`：一次 `inflateBack` 调用的所有 `in` 调用共提供少于 `2^48` 字节 | zlib.h 对一次调用的总输入没有限制。运行时把每个循环限制在 `2^64` 次迭代（`docs/trusted-base.md`），解码循环每轮至少读一位，因此提供更多输入的调用可能在 C 仍会继续时耗尽额度。`2^48` 字节远超一次调用实际能处理的输入。`Goal.inflateBack`（功能性，不在计划内，未证明）没有这个前提。 |
| 回调解码器窗口 | `Goal.inflate_back_sequence_safety`（通过 `BackSafeReachable.init`）假设 `8 ≤ windowBits ≤ 15`、窗口不为 `NULL` 且在 `2^windowBits` 字节内可写（这是 `zlib.h` 的要求），并且还假设窗口是一个堆字节块的切片 | zlib.h 只要求 `2^windowBits` 字节的可写窗口。模型中另一种可写字节视图只有 deflate 状态内部的 depth 数组，那是调用者无法指名的库存储；窗口位于那里不在已证明的定义域内。 |
| 回调解码器输入块 | `Goal.inflate_back_sequence_safety` 假设每个输入块位于一个堆字节块中：调用者的第一个输入块（`BackFirstChunk`）以及 `in` 交出的每个输入块（`BackPlatform`） | C 能处理位于任何可读存储中的输入块。位于其他存储中的输入块，例如调用者结构体的字段或静态数据，不在已证明的定义域内。这与 `inflate` 快速入口的限制相同（"快速解码辅助函数"）：`inflate_fast` 在该输入块上运行。把两个解码器推广到任意字节引用是 `docs/progress.md` 中的候选工作。 |

## Gzip 文件接口

`Goal.gz_sequence_safety` 在一个句柄的每段历史（`GzHistory`）上、对每个文件系统世界成立。它针对打过补丁的源码陈述（[补丁](../patches/README.md) 0002 至 0005）。gz 世界是堆之外的可信语义：[外部 I/O 模型](design/external-io.md)描述它，[可信基础](trusted-base.md)说明对它作了哪些假设。

| 领域 | 当前限制 | 后果 |
| --- | --- | --- |
| Gz 打开参数（`GzOpenSafe`、`GzDopenSafe`、`GzHistory.open`） | `path` 与 `mode` 各自为 `NULL`，或是短于 `2^64` 字节、以 NUL 结尾的字符串；堆是良构的，其字节对象不超限；世界是良构的文件系统（`FileSystem`）。 | 任何描述符、任何模式文本和任何世界下的打开都在覆盖范围内，包括每一种失败。在其对象内没有 NUL 结尾的路径或模式在范围之外，与 C 中一样。 |
| Gz 调用者缓冲区（`GzArguments` 中的 `GzRange`） | `gzread`、`gzfread`、`gzwrite`、`gzfwrite`、`gzputs`、`gzgets` 与 `gzerror` 的调用者缓冲区可读（读取调用的缓冲区和 `gzerror` 的 `errnum` 还须可写），并与句柄拥有的块分开：它们的字节根都不被句柄拥有（`GzOwned`）。`gzputs` 的参数是以 NUL 结尾的字符串（`CString`），范围含其 NUL：没有 NUL 的可读字节以及 `NULL` 都在定义域之外。 | 每个入口都先调用 `gz_error(state, Z_OK, NULL)`，它在触及缓冲区之前释放 `state->msg`。`gzerror` 返回的字符串就是 `state->msg`，所以把它传回去在 C 中是释放后使用：在停滞的写入者上执行 `gzputs(f, gzerror(f, &e))`，AddressSanitizer 报告 `strlen` 中的堆释放后使用（[复现](../tests/regression/gzprintf-error-string/README.md)，也覆盖 `gzwrite` 与 `gzread`）。zlib.h 只提醒之后的 `gzerror` 调用。调用者缓冲区和字面量都在覆盖范围内。 |
| Gz printf 字符串（`GzArguments`） | `gzprintf` 与 `gzvprintf` 的格式串以及每个字符串参数（`%s`）都与句柄拥有的块分开：它们的字节根都不被句柄拥有（`GzOwned`），正如 `GzRange` 对 `gzwrite`、`gzputs` 与 `gzread` 的缓冲区所要求的。 | `gzvprintf` 在 `vsnprintf` 读取格式串和参数之前调用 `gz_error(state, Z_OK, NULL)`，它会释放 `state->msg`。`gzerror` 返回的字符串就是 `state->msg`，所以把它传回去在 C 中是释放后使用（[复现](../tests/regression/gzprintf-error-string/README.md)）；zlib.h 只提醒之后的 `gzerror` 调用。字面量和调用者字符串都在覆盖范围内。 |
| 格式化 | 表示出的整数、字符和字符串参数，以及支持的标志、宽度、精度和长度修饰符 | 浮点、指针、写计数和其他未表示转换需要扩展模型。`GzArguments` 在 `Goal.gz_sequence_safety` 的每个 `gzprintf` 与 `gzvprintf` 步骤上都要求可表示的格式（`Formatted`），读取者或处于错误中的句柄也不例外，而 C 在那里根本不读格式串。定义域之外：`%f` 及其他浮点转换、`%p`、`%n`、长度修饰符 `h` 与 `hh`（`%hd`、`%hhu`）、`*` 宽度与精度（`%*d`）、没有 NUL 的数组上的 `%.3s`，以及给定 `unsigned` 参数的 `%c` 或 `%d`（值可表示时 `va_arg` 允许）。 |
| Gz 调用者步骤与世界步骤（`GzCallerFrame`、`GzWorldStep`） | 两次调用之间，调用者可以改变句柄不拥有的任何块，也可以释放自己的缓冲区；堆保持良构，其字节对象不超限。世界可以变成任何良构的文件系统：另一方可以关闭或重用句柄的描述符。 | 这比真实系统更宽，是有意为之。调用者写入句柄拥有的块，则不在历史之内。`gzbuffer`、`gzclose` 等不涉及调用者内存的调用没有参数前提。 |
| gz 读取终止（M7） | gz 序列安全目标终止的那一半，对 `gzread`、`gzfread`、`gzgetc`、`gzgetc_`、`gzgets` 和 `gzungetc` 假设句柄的描述符编号具有小于 `2^61` 字节的有限读取额度（`fs.readBudget fd = some b` 且 `b < 2^61`，前提 `ReadsFinite`）：即该描述符还能交付的总字节数。描述符编号不为负（`0 ≤ fd`，见 `HasBudget`）。关闭后重用的编号继承剩余额度 | zlib.h 不限制输入。永远交付只解码为空内容的数据（空 gzip 成员）的来源会让 `gz_fetch` 一直循环；对无穷来源进行巨大待跳过量的 `gz_skip` 会永远读取：这是 C 真实的不终止，任何有限额度都覆盖不了。有额度时每个循环都有界。`2^61` 这个数是模型的限制，不是 zlib 的：模型的每个循环有 `2^64` 次燃料。读取循环由输入剩余量、读取额度与尚待交付的字节数构成的度量限定（`fetchRank`，以及 `gz_read` 与 `gz_skip` 的度量）。一次取数填满缓冲区，除非失败、输入结束、到达 `GZ_OFF_MAX` 或降低 `fetchRank`，因此额度小于 `2^61` 使这些度量以及循环次数都小于 `2^64`。该上界的依据：`tests/verification/regressions/gz-read-budget-fuel.lean` 表明旧前提（任意大小的额度）允许一个额度，其中空 gzip 成员所需的轮数超过循环燃料。它只是算术核心，不是对 `gz_fetch` 返回 `outOfFuel` 的一次已检查运行。该前提不排除任何故障：无故障的那一半和后置条件对每个世界成立，不需要额度。`gzdirect`、写入一侧和 `gzseek` 不需要它。`gzdopen` 用 -1 以外的负描述符建立的句柄在模型中没有额度，所以不声称其读取调用终止，尽管真实的 `read` 在这种描述符上会立即以 `EBADF` 失败。终止依赖两条世界规则：读取调用的 `ReadsFinite`，以及 OS 事实“非空 `write` 从不返回 0”（“gz 操作系统事实”一行），它约束写入一侧。 |
| gz 操作系统事实 | 非空 `write` 从不返回 0；`close` 失败时也释放描述符 | Linux 行为，可信，未检查。`write` 永远返回 0 会让 C 中的 `gz_comp` 无限循环（`docs/progress.md` 中的观察记录）。 |
| 外部错误字符串 | `strerror` 返回带有调用代次的只读外部视图，不消耗分配尝试，也不增加库拥有的存活块；下一次调用使旧借用视图失效 | 模型选取顺序调用和固定区域设置下的文本，不表示并发调用、区域设置更改或旧指针身份的再次复用。文本复制与借用保持是独立证明义务。这不是完整的 libc 对应结论。 |

## 功能性命题与模型命题

下面各行限制的是功能目标、API 模型和内部引理。没有任何必需的安全目标依赖它们。它们仍然列在这里，是因为受它们限制的定理仍然登记在册。功能目标不在计划内（[范围](progress.md#scope)）。

| 领域 | 当前限制 | 后果 |
| --- | --- | --- |
| 聚焦函数手册 | 条目可能要求有效句柄、分离缓冲区、实际字符串的校验和、生成的操作符或特定调用顺序 | 这些是明确的文字范围，不缩小更广泛 Lean 公开目标。 |
| API 模型中的压缩器长度单元 | 功能性模型 `Concrete.compress2_z` 和 `Concrete.compress2` 使用可选标量输入及返回的存储值 | 本行只涉及功能性模型。其中不表示该单元与输入或输出的别名。`_z` 与兼容包装的空单元效果仍不同。翻译中的长度单元同样是标量，而这一点确实限制了必需的安全目标：见上文“整缓冲区压缩”一行。 |
| 计数解压单元 | 草案适配器保持输入长度、输出长度和数据范围分离 | 单元与数据或彼此的别名在适配器之外。早期和后期内存失败保留不同标量效果。 |
| 压缩器数据关系 | `Compress2` 用粗粒度拒绝标志描述数据 | `Compress2Z` 和 `Compress2Wrapper` 表达指针形状、错误顺序和长度存储。数据模型定理本身不是入口细化。 |
| 上界算术 | LP64 上两个长度都是 64 位 | `Goal.compress_bound_value` 覆盖每个 `UInt64`，没有更小数值前提。其他 ABI 需要大小转换命题。只有数值公式不能建立输出容量充足性。 |
| Deflate 字典顺序 | `DeflSetDict` 的 zlib 分支在 `started` 后拒绝字典 | C 可在流结束后接受字典。细化只能在文档顺序内使用该拒绝。`deflate_valid` 是模型定理，不是关于全部此类 C 执行的定理。 |
| 普通字节格式阶段 | 一个初始预置字典解释普通流 | 解码开始后的 raw 字典替换有构造器导出的标记。精确窗口效果和无条件序列安全仍须满足。一个初始字典不能描述完整高级历史。 |
| 高级操作组合 | Priming、头部和恢复保留具体逐入口目标 | 目标集合不是每种组合的完整操作细化。证明不能选择或清除历史资格标记来逃避义务。 |
| 快速解码辅助函数 | 局部执行和位来源引理假设输入与输出为原始字节块（互异，或同一块中不相交的范围）、窗口块不同于输出块、六个输入字节、258 个输出字节、入口位数小于八及 sane 模式 | 这些是构造和 init 不变量必须建立的内部前提，既不限制也不证明公开 inflate 目标。 |
| 已接受窗口参数下的 inflate 初始化 | `inflate_init2_valid_public` 假设 `Api.inflWbits wb.toInt = some (wrap, bits)` | 它对允许的 raw、zlib、gzip 和自动窗口参数保留现有初始化契约，包括所有分配结果、ABI／版本拒绝和空流拒绝。无效窗口参数明确排除；固定的 `Goal.inflateInit2_` 及已记录的清理契约问题均未改变。 |
| gz 文件数据 | 功能性的 gz 契约（`FileData`、`CloseContract`、`GzWriterFormat`、读写结果值）以及已登记目标 `Goal.gzoffset64`、`Goal.gzoffset` 和 `Goal.gzrewind`（自 `caad9db4` 起带前提 `RegularOs fs`）针对系统调用预言的普通文件实例（`RegularOs`）陈述 | 它们描述普通文件。预言的 `lseek` 可以返回而不移动描述符，某些 Linux 设备即如此；此时偏移与回绕的结果值不成立（[回归](../tests/verification/regressions/gz-offset-regular-world.lean)）。安全目标不使用这些契约。`gzoffset64`、`gzoffset` 和 `gzrewind` 在每个世界上的安全属于 `Goal.gz_sequence_safety`，该目标已登记，没有 `RegularOs` 前提。文件系统权限、父目录、链接、所有权和锁未被表示；预言的失败覆盖它们对每次调用的影响。 |

deflate 各中间定理的前提，以及局部的 open、close 和 priming 里程碑，在 2026-11-15 之前列在本页。它们收窄的是引理，从不收窄公开目标。它们原样保存在 [deflate 内部证明范围](history/deviations-internal-scopes.md)中。

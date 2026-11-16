<!-- source-sha256: 10ced7e45ecc2dbe2272d1d8872def3eccd41fd4760815d8910947c1c3fb9318 -->
# 按函数查覆盖情况

本页回答一个问题：`zlib.h` 的函数 X 的安全性是由哪条定理证明的，定义域是什么？每个有文档的函数占一行。每行写明安全目标、类型恰好就是该目标的定理，以及证明所在的文件。安全一列提到的每条定理都列在 `tests/audit/theorems.txt` 中。另有一列写明功能定理（如果有）；功能定理保留着，但并非必需。

- **已证明。** 目标构建中每个有文档的函数，都在其所在行写明的定义域上有一条安全定理。表中的名字已与 `tests/audit/public-api.json`、`tests/audit/theorems.txt` 和证明文件核对。
- **所作假设。** [可信基础](trusted-base.md)的六项，以及[偏离记录](deviations.md)中的前提；“定义域”一列指向的就是这些前提。
- **比 `zlib.h` 更窄。** 某一行的定义域比 `zlib.h` 要求得更多时，该行或[比 `zlib.h` 更窄的定义域](#domains-narrower-than-zlibh)一节会写明，相应的前提见[偏离记录](deviations.md)。

本页是一张地图，不是状态页。它不写一项结论处于哪个层级。每项结论的层级（已检查、已登记还是已验收）和每次验收运行所在的提交，见[进度页的“范围”一节](progress.md#scope)；针对上面这些事项计划做的工作，见[进度页的“zlib.h 函数的无故障覆盖”一节](progress.md#no-fault-coverage-of-zlibh-functions)。

## 怎样读一行

- **安全目标与定理。** 所有目标都在命名空间 `ZlibF.Spec.Public` 中，这里写作 `Goal.…`。定理名不带命名空间；每张表前面的说明给出命名空间和 `ZlibF/Proof/` 下的文件。
- **定义域。** 目标在“流可达”之外还要求什么。“无”表示对参数没有前提。有三条前提是每个流函数行和实用函数行共有的，不再重复：默认分配器、良构的模型堆，以及字节对象小于 `2^63` 字节（[偏离记录](deviations.md#build-and-platform)）。
- **`NULL` 流或不一致的流。** 对 `NULL` 流，或对 `zlib.h` 称为不一致的记录的调用，是一次拒绝。除四个初始化函数之外，每个流函数的安全目标在针对可达流的子句之外，都有一个针对它的子句。这一列写的是该子句陈述的内容：返回的值，以及堆的变化。该子句的定义域是 `RefusedInflate` 或 `RefusedDeflate`（[偏离记录，注 2](deviations.md#note-2-refused-streams)）：在 `zalloc` 和 `zfree` 已设置时，它不包括悬空的、属于另一种流的或垃圾的状态指针。这一列写有“`Goal.inflate_refusal` 也陈述”或“`Goal.deflate_refusal` 也陈述”的地方，是说那个目标把同一个拒绝又陈述了一遍；它的定理是 `public-stream-refusal.lean` 中的 `ZlibF.Spec.Public.RefusalProof.inflate_refusal` 或 `ZlibF.Spec.Public.RefusalProof.Deflate.deflate_refusal`。
- **序列目标。** 除初始化、End 和 Copy 之外，每个流调用除了自己的目标，还是所属那一类流的序列目标中的一种调用，所以它在任何历史的任何位置上也被覆盖：
  - `Goal.inflate_sequence_safety`：定理 `Zlib.Inflate.Proofs.inflate_sequence_safety_public`，`public-inflate-sequence-safety.lean`；
  - `Goal.deflate_sequence_safety`：定理 `Zlib.Deflate.Universal.deflate_sequence_safety`，`public-deflate-goals.lean`。

  End 调用是序列目标的第 3 个子句。一次成功的初始化或复制开启一段历史。

## Inflate 流

“安全目标”一列的定理：`public-stream-call-safety.lean` 中的 `ZlibF.Spec.Public.StreamCallSafetyProof.<名字>`，除非该行写了别的文件。两条初始化定理是 `public-init-safety.lean` 中的 `ZlibF.Spec.Public.InitSafetyProof.<名字>`。

| 函数 | 安全目标（定理同名） | 定义域 | `NULL` 流或不一致的流 | 功能定理（保留，并非必需） |
| --- | --- | --- | --- | --- |
| `inflateInit_`（宏 `inflateInit`） | `Goal.inflateInit__safety` | `zlib.h` 允许的每次调用（`InitArguments`）：`strm` 为 `NULL` 或使用默认分配器的记录；任意的 `state`、版本字节和 `stream_size`；每一种分配结果 | 在目标之内 | `Goal.inflateInit_`：`init15_public`，`public-inflate-init.lean` |
| `inflateInit2_`（宏 `inflateInit2`） | `Goal.inflateInit2__safety` | 同上，并对每个 `windowBits` | 在目标之内 | `Goal.inflateInit2_`：`inflate_init2_public`，`public-inflate-init2.lean` |
| `inflate` | `Goal.inflate_safety` | `StreamBuffers` 与 `ActiveHeader` | 在目标之内：`Z_STREAM_ERROR`；在满足 `Fresh` 的堆上，不写原先存活的任何块，存活的块保持原样；`Goal.inflate_refusal` 也陈述 | `Goal.inflate`：`Zlib.Inflate.Proofs.inflate_public`，`public-inflate.lean` |
| `inflateEnd` | `Goal.inflateEnd_safety` | 无 | 在目标之内：`Z_STREAM_ERROR`，堆不变；`Goal.inflate_refusal` 也陈述 | `Goal.inflateEnd`：`inflate_end_public`，`public-inflate-end.lean` |
| `inflateSetDictionary` | `Goal.inflateSetDictionary_safety` | 字典缓冲区（`CallerRange`） | 在目标之内：`Z_STREAM_ERROR`，堆不变；`Goal.inflate_refusal` 也陈述 | `Goal.inflateSetDictionary`：`inflateSetDictionary_public`，`public-inflate-setdict.lean` |
| `inflateGetDictionary` | `Goal.inflateGetDictionary_safety` | 目的缓冲区（`CallerRange`）。结果单元 `*dictLength` 在模型中是一个值（见[说明](#result-cells)） | 在目标之内：`Z_STREAM_ERROR`，长度值按传入时的值原样返回，堆不变；`Goal.inflate_refusal` 也陈述 | `Goal.inflateGetDictionary`：`inflate_getdict_public`，`public-inflate-getdict.lean` |
| `inflateSync` | `Goal.inflateSync_safety` | 输入范围 | 在目标之内：`Z_STREAM_ERROR`；在满足 `Fresh` 的堆上，不写原先存活的任何块，存活的块保持原样 | 没有：`Goal.inflateSync` 不在计划内 |
| `inflateCopy` | `Goal.inflateCopy_safety`：`ZlibF.Spec.Public.InflateCopySafetyProof.inflateCopy_safety`，`public-inflate-copy-safety.lean` | `source ≠ dest`；目的流是一个可读的记录 | 在目标之内。`dest` 为 `NULL`：`Z_STREAM_ERROR`，堆不变。`source` 为 `NULL`，或源记录属于 `RefusedInflate`，而 `dest` 记录可读：`Z_STREAM_ERROR`，且只把 `dest->state` 置为 `NULL`。对被拒绝的源，`Goal.inflate_refusal` 也陈述 | `Goal.inflateCopy`：`inflate_copy_public`，`public-inflate-copy.lean` |
| `inflateReset` | `Goal.inflateReset_safety` | 无 | 在目标之内：`Z_STREAM_ERROR`，堆不变；`Goal.inflate_refusal` 也陈述 | `Goal.inflateReset`：`reset_public`，`public-inflate-reset.lean` |
| `inflateReset2` | `Goal.inflateReset2_safety` | 无；每个 `windowBits` | 在目标之内：`Z_STREAM_ERROR`，堆不变；`Goal.inflate_refusal` 也陈述 | `Goal.inflateReset2`：`reset2_public`，`public-inflate-reset2.lean` |
| `inflatePrime` | `Goal.inflatePrime_safety` | 无 | 在目标之内：`Z_STREAM_ERROR`，堆不变 | `Goal.inflatePrime`：`prime_public`，`public-inflate-prime.lean` |
| `inflateMark` | `Goal.inflateMark_safety` | 无 | 在目标之内：`-65536`，堆不变 | `Goal.inflateMark`：`mark_public`，`public-inflate-mark.lean` |
| `inflateGetHeader` | `Goal.inflateGetHeader_safety` | `head` 不是 `NULL`；头部缓冲区（`HeaderMemory`） | 在目标之内：`Z_STREAM_ERROR`，堆不变 | `Goal.inflateGetHeader`：`getheader_public`，`public-inflate-header.lean` |

## Deflate 流

“安全目标”一列的定理：`public-stream-call-safety.lean` 中的 `ZlibF.Spec.Public.StreamCallSafetyProof.<名字>`；两个初始化函数则是 `public-init-safety.lean` 中的 `ZlibF.Spec.Public.InitSafetyProof.<名字>`；该行写了别的文件时以该行为准。

| 函数 | 安全目标（定理同名） | 定义域 | `NULL` 流或不一致的流 | 功能定理（保留，并非必需） |
| --- | --- | --- | --- | --- |
| `deflateInit_`（宏 `deflateInit`） | `Goal.deflateInit__safety` | `zlib.h` 允许的每次调用（`InitArguments`），每个压缩级别 | 在目标之内 | `Goal.deflateInit_`：`deflateInit_proof`，`public-deflate-init.lean` |
| `deflateInit2_`（宏 `deflateInit2`） | `Goal.deflateInit2__safety` | 同上，并对每个方法、`windowBits`、`memLevel` 和策略 | 在目标之内 | `Goal.deflateInit2_`：`deflateInit2_proof`，`public-deflate-init2.lean` |
| `deflate` | `Goal.deflate_safety` | `StreamBuffers` 与 `ActiveHeader` | 在目标之内：`Z_STREAM_ERROR`，堆不变；`Goal.deflate_refusal` 也陈述 | `Goal.deflate`：`Zlib.Deflate.Universal.deflate_safety`，`public-deflate-goals.lean` |
| `deflateEnd` | `Goal.deflateEnd_safety` | 无 | 在目标之内：`Z_STREAM_ERROR`，堆不变 | `Goal.deflateEnd`：`deflate_end_public`，`public-deflate-end.lean` |
| `deflateSetDictionary` | `Goal.deflateSetDictionary_safety` | 字典缓冲区（`CallerRange`） | 在目标之内：`Z_STREAM_ERROR`，堆不变；`Goal.deflate_refusal` 也陈述 | 没有：`Goal.deflateSetDictionary` 不在计划内 |
| `deflateGetDictionary` | `Goal.deflateGetDictionary_safety` | 目的缓冲区（`CallerRange`）。结果单元 `*dictLength` 在模型中是一个值（见[说明](#result-cells)） | 在目标之内：`Z_STREAM_ERROR`，不存入长度，堆不变；`Goal.deflate_refusal` 也陈述 | `Goal.deflateGetDictionary`：`deflate_getdict_public`，`public-deflate-getdict.lean` |
| `deflateCopy` | `Goal.deflateCopy_safety`：`Zlib.Deflate.Universal.deflate_copy_safety`，`public-deflate-copy.lean` | `source ≠ dest`；目的流是一个可读的记录 | 在目标之内。`dest` 为 `NULL`：`Z_STREAM_ERROR`，堆不变。`source` 为 `NULL`，或源记录属于 `RefusedDeflate`，而 `dest` 记录可读：`Z_STREAM_ERROR`，且只把 `dest->state` 置为 `NULL`。对被拒绝的源，`Goal.deflate_refusal` 也陈述 | `Goal.deflateCopy`：`deflate_copy_public`，`public-deflate-copy.lean` |
| `deflateReset` | `Goal.deflateReset_safety` | 无 | 在目标之内：`Z_STREAM_ERROR`，堆不变 | `Goal.deflateReset`：`deflate_reset_public`，`public-deflate-reset.lean` |
| `deflateParams` | `Goal.deflateParams_safety` | `StreamBuffers` 与 `ActiveHeader` | 在目标之内：`Z_STREAM_ERROR`，堆不变；`Goal.deflate_refusal` 也陈述 | 没有：`Goal.deflateParams` 不在计划内 |
| `deflateTune` | `Goal.deflateTune_safety` | 无 | 在目标之内：`Z_STREAM_ERROR`，堆不变 | `Goal.deflateTune`：`tune_public`，`public-deflate-small-queries.lean` |
| `deflateBound` | `Goal.deflateBound_safety` | `ActiveHeader` 与 `DeflateHeaderLive` | 在目标之内：返回对 `NULL` 流调用时返回的值（是上界，不是错误值），堆不变 | 没有：`Goal.deflateBound` 不在计划内 |
| `deflateBound_z` | `Goal.deflateBound_z_safety` | `ActiveHeader` 与 `DeflateHeaderLive` | 在目标之内：返回对 `NULL` 流调用时返回的值（是上界，不是错误值），堆不变 | 没有：`Goal.deflateBound_z` 不在计划内 |
| `deflatePending` | `Goal.deflatePending_safety` | 无。结果单元 `*pending` 和 `*bits` 在模型中是值（见[说明](#result-cells)） | 在目标之内：`Z_STREAM_ERROR`，两个计数都不存入，堆不变 | `Goal.deflatePending`：`pending_public`，`public-deflate-small-queries.lean` |
| `deflateUsed` | `Goal.deflateUsed_safety` | 无。结果单元 `*bits` 在模型中是一个值（见[说明](#result-cells)） | 在目标之内：`Z_STREAM_ERROR`，不存入计数，堆不变 | `Goal.deflateUsed`：`used_public`，`public-deflate-small-queries.lean` |
| `deflatePrime` | `Goal.deflatePrime_safety` | 在第一次 `deflate` 调用之前（`DeflateNotStarted`），这是 `zlib.h` 的规则 | 在目标之内：`Z_STREAM_ERROR`，堆不变 | 没有：`Goal.deflatePrime` 不在计划内 |
| `deflateSetHeader` | `Goal.deflateSetHeader_safety` | 在第一次 `deflate` 调用之前；头部缓冲区（`HeaderMemory`） | 在目标之内：`Z_STREAM_ERROR`，堆不变 | `Goal.deflateSetHeader`：`header_public`，`public-deflate-small-queries.lean` |

<a id="result-cells"></a>**结果单元。** `inflateGetDictionary`、`deflateGetDictionary`、`deflatePending` 和 `deflateUsed` 通过指针写出结果。翻译把这样的指针当作值，而不是内存，所以这四个函数的安全目标对结果单元的内存什么都没说：既没说它可写，也没说它与其他区域分开。模型表示的是哪些调用，见[偏离记录](deviations.md#stream-calls-inflate-and-deflate)的“结果单元”一行。`compress*` 的长度单元也是如此（[整缓冲区实用函数](#whole-buffer-utilities)）。

## 回调解码器

安全一列的定理：`public-back-safety.lean` 中的 `ZlibF.Spec.Public.BackSafetyProof.<name>`。目标在 `ZlibF/Spec/Safety/Back.lean` 中。

| 函数 | 安全目标 = 定理名 | 定义域 | `NULL` 流或不一致的流 | 功能定理（保留，并非必需） |
| --- | --- | --- | --- | --- |
| `inflateBackInit_`（宏 `inflateBackInit`） | `Goal.inflateBackInit__safety` | `zlib.h` 允许的每次调用（`InitArguments`），对每个 `windowBits`、`stream_size` 和 `state`；窗口非 `NULL` 且 `windowBits` 为 8 到 15 时，窗口有 `2^windowBits` 个可写字节；每一种分配结果 | `NULL` 流在目标之内 | `Goal.inflateBackInit_`：`ZlibF.Spec.Public.InflateBackInitProof.back_init_public`，`public-infback-init.lean`。它对每个 `state` 值说明错误的版本或大小、`NULL` 流、`NULL` 窗口、错误的 `windowBits` 和分配失败各返回哪个值。 |
| `inflateBack` | `Goal.inflateBack_safety` | `BackSafeReachable` 的一段历史；`inputBound < 2^48`；窗口和每个输入片段都在堆字节块中；回调协议 | 在目标之内：`NULL` 流，以及状态为 `NULL` 的流记录 | 没有：`Goal.inflateBack` 不在计划内 |
| `inflateBackEnd` | `Goal.inflateBackEnd_safety` | `BackSafeReachable` 的一段历史；没有别的要求 | 在目标之内：`NULL` 流，以及状态或 `zfree` 为 `NULL` 的流记录 | `Goal.inflateBackEnd`：`ZlibF.Spec.Public.InflateBackEndProof.back_end_public`，`public-infback-end.lean` |

- **序列目标。** `Goal.inflate_back_sequence_safety`（`ZlibF/Spec/Public/Sequences.lean`）：定理 `Zlib.Infback.Safety.inflate_back_sequence_safety`，`infback.c.safety-fast.lean`。它多说一点：每段历史之后，调用者的窗口上都有一个有效的解码器状态。它的子句 1 和子句 3 是 `Goal.inflateBack_safety` 的第一个和第三个子句，它的子句 4 是 `Goal.inflateBackEnd_safety` 的第三个子句。历史从一次返回 `Z_OK` 的 `inflateBackInit_` 调用开始，调用之前 `state` 字段可以取任意值（`BackInitArguments`）。
- **非空性。** `Goal.inflate_back_initialisation_domain`（`ZlibF/Spec/Public/Domains.lean`）。
- **证明变异体。** 序列定理有十一个证明变异体，针对 `inflateBack`、`inflateBackInit_` 和 `inflateBackEnd`（`tests/proof-mutants/infback-sequence.tsv`）。三个单函数目标在 `tests/audit/public-mutants.json` 中各有自己的键（[变异体指南](checking/proof-mutants.md)）。

## 校验和与查询

“安全目标”一列的定理：`public-stateless-safety.lean` 中的 `ZlibF.Spec.Public.StatelessSafetyProof.<名字>`。这些目标说的是：调用返回，并且堆保持不变。每个 CRC 目标，包括各组合目标，都有一条前提：模型中的两张 CRC 表就是该构建的表（`CrcGlobals`）。这是对模型的条件，不是对参数的条件（[模型的限制](model-limits.md#conditions-on-the-model-that-goals-state)），所以对参数没有前提的 CRC 行，“定义域”一列写“无”。

| 函数 | 安全目标（定理同名） | 定义域 | 功能定理（保留，并非必需） |
| --- | --- | --- | --- |
| `adler32` | `Goal.adler32_safety` | **比 `zlib.h` 更窄**：只有 `len = 0` 时 `buf` 才可以是 `NULL`（`AdlerBufferBytes`）。`len = 1` 时 C 会读 `buf[0]`。`buf` 为 `NULL` 且 `len ≥ 2` 在 C 中是安全的，但没有证明。 | `Goal.adler32`：`adler_public`，`public-adler-update.lean` |
| `adler32_z` | `Goal.adler32_z_safety` | 与 `adler32` 相同 | `Goal.adler32_z`：`adler_z_public`，`public-adler-update.lean` |
| `adler32_combine`、`adler32_combine64` | `Goal.adler32_combine_safety`、`Goal.adler32_combine64_safety` | 无 | `Goal.adler32_combine`、`Goal.adler32_combine64`：`combine_public`、`combine64_public`，`public-adler-combine.lean` |
| `crc32`、`crc32_z` | `Goal.crc32_safety`、`Goal.crc32_z_safety` | `buf` 可读，或为 `NULL`（长度任意）（`BufferBytes`） | `Goal.crc32`、`Goal.crc32_z`：`crc32`、`crc32_z`，`public-crc-updates.lean` |
| `crc32_combine`、`crc32_combine64` | `Goal.crc32_combine_safety`、`Goal.crc32_combine64_safety` | 无 | `Goal.crc32_combine`、`Goal.crc32_combine64`：`combine`、`combine64`，`public-crc-combine.lean` |
| `crc32_combine_gen`、`crc32_combine_gen64` | `Goal.crc32_combine_gen_safety`、`Goal.crc32_combine_gen64_safety` | 无 | `Goal.crc32_combine_gen`、`Goal.crc32_combine_gen64`：`gen`、`gen64`，`public-crc-combine.lean` |
| `crc32_combine_op` | `Goal.crc32_combine_op_safety` | `op` 来自 `crc32_combine_gen` 或 `crc32_combine_gen64`，这是 `zlib.h` 的规定 | `Goal.crc32_combine_op`：`op`，`public-crc-combine.lean` |
| `zlibVersion` | `Goal.zlibVersion_safety` | 无 | `Goal.zlibVersion`：`zlibVersion`，`public-zlib-version.lean` |
| `zlibCompileFlags` | `Goal.zlibCompileFlags_safety` | 无 | `Goal.zlibCompileFlags`：`zlibCompileFlags`，`public-zlib-compile-flags.lean` |
| `compressBound`、`compressBound_z` | `Goal.compressBound`、`Goal.compressBound_z`：`ZlibF.Spec.Public.Proofs.compressBound`、`compressBound_z`，`public-compress-bound.lean` | 无 | 同样的两个目标。它们的翻译是纯函数，不涉及堆，也不会出故障，所以完整的契约同时充当两种目标。 |

## 整缓冲区实用函数

| 函数 | 安全目标与定理 | 定义域 | 功能定理（保留，并非必需） |
| --- | --- | --- | --- |
| `compress`、`compress_z`、`compress2`、`compress2_z` | `Goal.compress_safety`、`Goal.compress_z_safety`、`Goal.compress2_safety`、`Goal.compress2_z_safety`：`ZlibF.Spec.Public.Proofs.Compress.<名字>`，`public-compress-safe-mid.lean` | 源与目的缓冲区分离；长度单元在模型中是标量，所以与数据重叠的单元不被覆盖（[偏离记录](deviations.md#whole-buffer-utilities-and-checksums)）。每个压缩级别。 | 没有：`Goal.compress*` 不在计划内 |
| `uncompress`、`uncompress_z`、`uncompress2`、`uncompress2_z` | `Goal.uncompress_safe`、`Goal.uncompress_z_safe`、`Goal.uncompress2_safe`、`Goal.uncompress2_z_safe`：`ZlibF.Spec.Public.Proofs.Uncompress.<名字>`，`public-uncompress-safe.lean` | 数据与各长度单元两两分离（`UtilitySeparation`） | 没有：`Goal.uncompress*` 不在计划内 |

## Gzip 文件接口

31 个有文档的 gz 函数以及 `gzvprintf`，各有自己的安全目标 `Goal.<function>_safety`，在 `ZlibF/Spec/Safety/GzCalls.lean` 中。定理与目标同名：`public-gz-call-safety.lean` 中的 `ZlibF.Spec.Public.GzCallSafetyProof.<function>_safety`。每个目标是序列目标的一个子句，限制到一个函数的调用上。接受句柄的函数，其目标还带有对 `NULL` 句柄的拒绝。

- **序列目标。** `Goal.gz_sequence_safety`（`ZlibF/Spec/Public/GzSafety.lean`）：定理 `ZlibF.Spec.Public.Proofs.gz_sequence_safety_public`，`public-gz-sequence-safety.lean`。它的定义域是一个句柄在每个文件系统世界中的每段历史（`GzHistory`）。
- **非空性。** `Goal.gz_sequence_nonvacuity`：定理 `ZlibF.Spec.Public.Proofs.GzNonvacuity.gz_sequence_nonvacuity_public`，`public-gz-sequence-nonvacuity.lean`。
- **`NULL` 句柄。** `Goal.gz_refusal`：定理 `ZlibF.Spec.Public.GzRefusalProof.gz_refusal`，`public-gz-refusal.lean`。接受句柄的 29 个 gz 函数（包括 `gzvprintf`）各自返回文档规定的值，堆和世界都不变。三个打开函数不接受句柄。这 29 个函数各自的目标都重复了属于它的那个子句。
- **证明变异体。** 每一组 gz 函数，以及补丁 0002 至 0005 的每一处改动，都有变异体（`gz-sequence.tsv`、`gz-read.tsv`、`gz-refusal.tsv`）。32 个单函数目标在 `tests/audit/public-mutants.json` 中各有自己的键；随这些键新增的行在 `public-gz-safety.tsv` 中（[变异体指南](checking/proof-mutants.md)）。

下表说明每个函数的目标限制的是序列目标的哪个子句。前提是[偏离记录中 gz 的各行](deviations.md#gzip-file-interface)。

| 函数（各有自己的 `Goal.<function>_safety`） | 目标所限制的 `Goal.gz_sequence_safety` 的部分 | 说明 |
| --- | --- | --- |
| `gzopen`、`gzopen64` | 打开子句（`GzOpenSafe`） | 每个路径、模式和世界，包括每一种失败 |
| `gzdopen` | 打开子句（`GzDopenSafe`） | 每个 `fd`。功能目标 `Goal.gzdopen` 也已证明（`Zlib.Gzlib.Proofs.gzdopen_complete`）。 |
| `gzbuffer`、`gzeof`、`gzerror`、`gzclearerr`、`gztell`、`gztell64`、`gzoffset`、`gzoffset64`、`gzrewind`、`gzseek`、`gzseek64` | 调用子句；`gzerror` 还有关于它所返回字符串的子句 | `gzbuffer`、`gzeof`、`gzerror`、`gzclearerr`、`gzoffset`、`gzoffset64` 和 `gzrewind` 的功能目标也已证明。 |
| `gzwrite`、`gzfwrite`、`gzputc`、`gzputs`、`gzprintf`、`gzvprintf`、`gzflush`、`gzsetparams` | 调用子句 | `gzprintf` 和 `gzvprintf` 的每次调用都需要可表示的格式串，读句柄上也一样。`zlib.h` 把 `gzvprintf` 列为未文档化；它的目标仍然是必需的。 |
| `gzread`、`gzfread`、`gzgetc`、`gzgetc_`、`gzungetc`、`gzgets` | 调用子句；终止需要 `ReadsFinite`。`gzgetc` 还有宏子句 | 在每个世界中都不出故障；读取预算小于 `2^61` 时正常返回 |
| `gzdirect` | 调用子句 | 在每个世界中都终止 |
| `gzclose`、`gzclose_r`、`gzclose_w` | 关闭子句 | 模式不对的关闭被拒绝，什么也不改变；否则释放拥有的每个块，并释放描述符 |
| `zlib.h` 的 `gzgetc()` 宏（在 `Goal.gzgetc_safety` 中） | 宏子句，以及历史步骤 `GzHistory.getcMacro` | 有已缓冲的输出时走内联路径；`x.have = 0` 时调用函数，在 `ReadsFinite` 之下被覆盖。对 `NULL` 句柄使用这个宏在 C 中是未定义行为，不被覆盖。 |
| 同一描述符上的第二个句柄 | 世界步骤 `GzHistory.world` | 一次调用之后可以换成任何良构的世界，所以别的参与者可以关闭或重用这个描述符（[回归](../tests/verification/regressions/gz-world-closes-fd.lean)）。 |

## 比 `zlib.h` 更窄的定义域

每一条在[偏离记录](deviations.md)中都有对应的行。

- `inflateBack`：`inputBound < 2^48`；窗口和每个输入片段都在堆字节块中；两次调用之间调用者不写窗口。
- `inflateCopy` 与 `deflateCopy`：`source ≠ dest`。
- `adler32` 与 `adler32_z`：只有 `len = 0` 时 `buf` 才可以是 `NULL`。
- `inflate`、`deflate`、`deflateParams`、`compress*`、`uncompress*`：调用者的各区域互不重叠。
- `compress*`、`inflateGetDictionary`、`deflateGetDictionary`、`deflatePending`、`deflateUsed`：结果单元在模型中是一个值，所以目标对它的内存什么都没说。
- gz 的读取调用：终止需要读取预算。
- 每个流：默认分配器。

gz 覆盖情况当初是怎样审查和改正的，记在[覆盖情况：审查记录](history/coverage-review-record.md)中；更早的未完成事项列表在[覆盖情况：早先的未完成事项](history/coverage-open-items.md)中。

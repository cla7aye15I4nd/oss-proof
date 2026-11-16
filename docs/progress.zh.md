<!-- source-sha256: 2c4fd7d4d5f43673967e6da4014a3dba25782f97e79cf10a3cc38ea6b6723841 -->
# 结论的状态

本页说明每项结论、zlib 的每个公开函数是否已经完成。只有本页说明状态。要点是：三项安全结论都已完成，组成它们的 99 个目标全部完成。

一项结论、一个目标或一个函数只有两种状态。

- **完成**：存在一条 Lean 定理，它的命题恰好就是这个目标，并且通过了本项目的每一项检查。这意味着什么，见[完成的结论依靠什么](checking/README.md)。
- **未完成**：没有这样的定理。如果也不打算给出定理，会另外写明“不在计划内”。

这些结论是什么意思，请读[总览](overview.md)。每个函数对应哪条定理、定理覆盖哪些调用，请读[按函数查覆盖情况](coverage.md)和[偏离记录](deviations.md)。

## 结论 {#scope}

安全指没有未定义行为、没有内存错误、没有泄漏，并且终止。这些结论针对默认的 x86_64 Linux 构建。

| # | 结论 | 目标 | 状态 |
| ---: | --- | --- | --- |
| 1 | `inflate` 对每个输入、缓冲区的每种切分都安全，对它的调用序列也是如此。 | `Goal.inflate_safety`、`Goal.inflate_sequence_safety` | 完成 |
| 2 | `deflate` 对每个输入、缓冲区的每种切分都安全，对它的调用序列也是如此。 | `Goal.deflate_safety`、`Goal.deflate_sequence_safety` | 完成 |
| 3 | 其余每个有文档的公开函数都安全：`compress*` 与 `uncompress*`、其他流函数、校验和函数、gzip 文件接口和回调解码器 `inflateBack`。 | [下文](#functions)各表中的其余全部目标 | 完成 |
| 4 | 默认 zlib 流的往返：用默认级别的 `deflateInit` 压缩，再用 `inflateInit` 解压，得到原输入。 | 还没有写出目标 | 未完成 |

关于第 4 项：有一条定理 `deflate_inflate_roundtrip`，它对翻译后的 C 证明了一个条件形式。当一个 `deflate` 调用序列和一个 `inflate` 调用序列都到达 `Z_STREAM_END` 时，`inflate` 写出的字节就是 `deflate` 读入的字节。没有定理说明在输出空间足够、分配成功时两边都会到达 `Z_STREAM_END`，也没有定理陈述不带这个条件的往返，或者 `uncompress(compress(x)) = x`。

## 每个公开函数 {#functions}

默认构建中每个有文档的函数都有自己的安全目标。[API 参考](spec/api/README.md)中每个函数的页面给出它的目标的命题。

### 解压流 {#inflate-streams}

| 函数 | 目标 | 状态 |
| --- | --- | --- |
| `inflate` | `Goal.inflate_safety` | 完成 |
| `inflateCopy` | `Goal.inflateCopy_safety` | 完成 |
| `inflateEnd` | `Goal.inflateEnd_safety` | 完成 |
| `inflateGetDictionary` | `Goal.inflateGetDictionary_safety` | 完成 |
| `inflateGetHeader` | `Goal.inflateGetHeader_safety` | 完成 |
| `inflateInit2_` | `Goal.inflateInit2__safety` | 完成 |
| `inflateInit_` | `Goal.inflateInit__safety` | 完成 |
| `inflateMark` | `Goal.inflateMark_safety` | 完成 |
| `inflatePrime` | `Goal.inflatePrime_safety` | 完成 |
| `inflateReset` | `Goal.inflateReset_safety` | 完成 |
| `inflateReset2` | `Goal.inflateReset2_safety` | 完成 |
| `inflateSetDictionary` | `Goal.inflateSetDictionary_safety` | 完成 |
| `inflateSync` | `Goal.inflateSync_safety` | 完成 |

### 压缩流 {#deflate-streams}

| 函数 | 目标 | 状态 |
| --- | --- | --- |
| `deflate` | `Goal.deflate_safety` | 完成 |
| `deflateBound` | `Goal.deflateBound_safety` | 完成 |
| `deflateBound_z` | `Goal.deflateBound_z_safety` | 完成 |
| `deflateCopy` | `Goal.deflateCopy_safety` | 完成 |
| `deflateEnd` | `Goal.deflateEnd_safety` | 完成 |
| `deflateGetDictionary` | `Goal.deflateGetDictionary_safety` | 完成 |
| `deflateInit2_` | `Goal.deflateInit2__safety` | 完成 |
| `deflateInit_` | `Goal.deflateInit__safety` | 完成 |
| `deflateParams` | `Goal.deflateParams_safety` | 完成 |
| `deflatePending` | `Goal.deflatePending_safety` | 完成 |
| `deflatePrime` | `Goal.deflatePrime_safety` | 完成 |
| `deflateReset` | `Goal.deflateReset_safety` | 完成 |
| `deflateSetDictionary` | `Goal.deflateSetDictionary_safety` | 完成 |
| `deflateSetHeader` | `Goal.deflateSetHeader_safety` | 完成 |
| `deflateTune` | `Goal.deflateTune_safety` | 完成 |
| `deflateUsed` | `Goal.deflateUsed_safety` | 完成 |

### 完整缓冲区与库信息 {#buffers-and-library}

| 函数 | 目标 | 状态 |
| --- | --- | --- |
| `compress` | `Goal.compress_safety` | 完成 |
| `compress2` | `Goal.compress2_safety` | 完成 |
| `compress2_z` | `Goal.compress2_z_safety` | 完成 |
| `compressBound` | `Goal.compressBound` | 完成 |
| `compressBound_z` | `Goal.compressBound_z` | 完成 |
| `compress_z` | `Goal.compress_z_safety` | 完成 |
| `uncompress` | `Goal.uncompress_safe` | 完成 |
| `uncompress2` | `Goal.uncompress2_safe` | 完成 |
| `uncompress2_z` | `Goal.uncompress2_z_safe` | 完成 |
| `uncompress_z` | `Goal.uncompress_z_safe` | 完成 |
| `zlibCompileFlags` | `Goal.zlibCompileFlags_safety` | 完成 |
| `zlibVersion` | `Goal.zlibVersion_safety` | 完成 |

### 校验和 {#checksums}

| 函数 | 目标 | 状态 |
| --- | --- | --- |
| `adler32` | `Goal.adler32_safety` | 完成 |
| `adler32_combine` | `Goal.adler32_combine_safety` | 完成 |
| `adler32_combine64` | `Goal.adler32_combine64_safety` | 完成 |
| `adler32_z` | `Goal.adler32_z_safety` | 完成 |
| `crc32` | `Goal.crc32_safety` | 完成 |
| `crc32_combine` | `Goal.crc32_combine_safety` | 完成 |
| `crc32_combine64` | `Goal.crc32_combine64_safety` | 完成 |
| `crc32_combine_gen` | `Goal.crc32_combine_gen_safety` | 完成 |
| `crc32_combine_gen64` | `Goal.crc32_combine_gen64_safety` | 完成 |
| `crc32_combine_op` | `Goal.crc32_combine_op_safety` | 完成 |
| `crc32_z` | `Goal.crc32_z_safety` | 完成 |

### 回调解码 {#callback-decoding}

| 函数 | 目标 | 状态 |
| --- | --- | --- |
| `inflateBack` | `Goal.inflateBack_safety` | 完成 |
| `inflateBackEnd` | `Goal.inflateBackEnd_safety` | 完成 |
| `inflateBackInit_` | `Goal.inflateBackInit__safety` | 完成 |

### gzip 文件 {#gzip-files}

| 函数 | 目标 | 状态 |
| --- | --- | --- |
| `gzbuffer` | `Goal.gzbuffer_safety` | 完成 |
| `gzclearerr` | `Goal.gzclearerr_safety` | 完成 |
| `gzclose` | `Goal.gzclose_safety` | 完成 |
| `gzclose_r` | `Goal.gzclose_r_safety` | 完成 |
| `gzclose_w` | `Goal.gzclose_w_safety` | 完成 |
| `gzdirect` | `Goal.gzdirect_safety` | 完成 |
| `gzdopen` | `Goal.gzdopen_safety` | 完成 |
| `gzeof` | `Goal.gzeof_safety` | 完成 |
| `gzerror` | `Goal.gzerror_safety` | 完成 |
| `gzflush` | `Goal.gzflush_safety` | 完成 |
| `gzfread` | `Goal.gzfread_safety` | 完成 |
| `gzfwrite` | `Goal.gzfwrite_safety` | 完成 |
| `gzgetc` | `Goal.gzgetc_safety` | 完成 |
| `gzgetc_` | `Goal.gzgetc__safety` | 完成 |
| `gzgets` | `Goal.gzgets_safety` | 完成 |
| `gzoffset` | `Goal.gzoffset_safety` | 完成 |
| `gzoffset64` | `Goal.gzoffset64_safety` | 完成 |
| `gzopen` | `Goal.gzopen_safety` | 完成 |
| `gzopen64` | `Goal.gzopen64_safety` | 完成 |
| `gzprintf` | `Goal.gzprintf_safety` | 完成 |
| `gzputc` | `Goal.gzputc_safety` | 完成 |
| `gzputs` | `Goal.gzputs_safety` | 完成 |
| `gzread` | `Goal.gzread_safety` | 完成 |
| `gzrewind` | `Goal.gzrewind_safety` | 完成 |
| `gzseek` | `Goal.gzseek_safety` | 完成 |
| `gzseek64` | `Goal.gzseek64_safety` | 完成 |
| `gzsetparams` | `Goal.gzsetparams_safety` | 完成 |
| `gztell` | `Goal.gztell_safety` | 完成 |
| `gztell64` | `Goal.gztell64_safety` | 完成 |
| `gzungetc` | `Goal.gzungetc_safety` | 完成 |
| `gzvprintf` | `Goal.gzvprintf_safety` | 完成 |
| `gzwrite` | `Goal.gzwrite_safety` | 完成 |

`gzvprintf` 在 `zlib.h` 中是未文档化函数。它有安全目标，因为 `gzprintf` 要经过它。`Goal.compressBound` 和 `Goal.compressBound_z` 是两个纯函数的完整契约，这两个函数不涉及堆，也不会出故障；这两个契约代替它们的安全目标。

### 涉及多个函数的目标 {#other-goals}

| 命题 | 目标 | 状态 |
| --- | --- | --- |
| inflate 流的每个调用序列都安全。 | `Goal.inflate_sequence_safety` | 完成 |
| deflate 流的每个调用序列都安全。 | `Goal.deflate_sequence_safety` | 完成 |
| 回调解码器的每个调用序列都安全，对每种调用者协议都成立。 | `Goal.inflate_back_sequence_safety` | 完成 |
| gzip 文件句柄的每段历史都安全，对每个文件系统世界都成立。 | `Goal.gz_sequence_safety` | 完成 |
| inflate 的各个函数拒绝 `NULL` 流或不一致的流，不出故障。 | `Goal.inflate_refusal` | 完成 |
| deflate 的各个函数拒绝 `NULL` 流或不一致的流，不出故障。 | `Goal.deflate_refusal` | 完成 |
| gzip 文件函数拒绝 `NULL` 句柄，不出故障，也不改变任何东西。 | `Goal.gz_refusal` | 完成 |
| inflate 各目标的前提可以满足：在一个具体的堆上初始化成功。 | `Goal.inflate_initialisation_domain` | 完成 |
| deflate 各目标的前提可以满足：在一个具体的堆上初始化成功。 | `Goal.deflate_initialisation_domain` | 完成 |
| 回调解码器各目标的前提可以满足：在一个具体的堆上初始化成功。 | `Goal.inflate_back_initialisation_domain` | 完成 |
| 一次 `inflateBack` 调用的各项前提可以同时满足，用的是具体的回调和具体的调用者协议。 | `Goal.inflateBack_call_domain` | 完成 |
| gzip 文件各目标的前提可以满足：存在一个句柄的两段具体历史，一段读、一段写。 | `Goal.gz_sequence_nonvacuity` | 完成 |

## 不在计划内 {#not-planned}

这些不打算给出定理。已经为它们证明的定理保留。

| 组 | 包含什么 | 理由 |
| --- | --- | --- |
| 功能正确性（第 4 项除外） | 函数在安全之外算出了什么：`inflate` 的输出等于格式规定的内容；其他压缩级别、策略、窗口大小和封装的往返，带预设字典的往返，经由 gzip 文件接口或 `inflateBack` 的往返；gzip 文件函数读出或写入的字节；`inflateBack` 交付的内容；只谈抽象模型的命题。 | 安全结论不需要它们。关于 gzip 文件接口的命题还要依靠一个手工建立的模型，包括文件系统、描述符和 `printf` 格式化。安全证明所依赖的功能性事实，在那个证明里一并证明。 |
| 其他构建配置 | 默认 x86_64 Linux 构建之外的每一种配置。 | 每一种配置都要针对不同的平台模型把整个证明重做一遍。 |
| 未文档化函数 | `zError`、`inflateSyncPoint`、`get_crc_table`、`inflateUndermine`、`inflateValidate`、`inflateCodesUsed`、`inflateResetKeep`、`deflateResetKeep`、`gzopen_w`：`zlib.h` 在 `undocumented functions (not part of the zlib API)`（未文档化函数，不属于 zlib API）之下声明了十个函数，这是其中九个。第十个是上文的 `gzvprintf`。 | 它们不属于 zlib API。没有为它们写出安全目标：未完成，不在计划内。 |

尽管如此，许多函数的功能契约已有定理，九个未文档化函数中的八个也在其中（只有 `gzopen_w` 例外，它不在默认构建中）。[API 参考](spec/api/README.md)中每个函数的页面说明它的功能契约是否完成。

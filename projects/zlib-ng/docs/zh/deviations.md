<!-- source-sha256: f58a721bbb156f4e0c01148c6bce28f49d198fda3c41c5bfa7ff08b8b6345f0a -->
# 偏差：调用必须满足的条件

本页列出比 `zlib.h` 更窄、或读者可能忽略的每一个目标前提。超出这些范围的调用不在覆盖之内：既未证明安全，
也不声称不安全。

## 所有调用

- 库为 zlib-ng `develop` 分支提交 `5f1f4899` 加十个补丁，以
  `-DZLIB_COMPAT=ON -DWITH_OPTIM=OFF -DWITH_CRC32_CHORBA=OFF -DWITH_RUNTIME_CPU_DETECTION=OFF` 构建为 x86_64
  Linux LP64 库，使 `adler32` 与 `adler32_z` 执行 `adler32_c`，`crc32` 与 `crc32_z` 执行 `crc32_braid`。分派到
  SIMD 内核或 Chorba CRC-32 内核（默认）的构建不在覆盖之内。
- 静态 CRC 表 `crc_table` 与 `x2n_table` 持有 `crc32_braid_tbl.h` 的常量（`CrcGlobals`）。在 C 中它们是常量
  数据；在模型中它们属于堆，因此 CRC 目标显式陈述这一点。
- 缓冲区参数要么是 `NULL`（`len` 任意），要么指向某个存活对象内 `len` 个可读字节（`BufferBytes`）。这正是
  `zlib.h` 的要求。
- 定理对每个对象的每个地址（`Heap.baseAddr`）成立，因此覆盖缓冲区的所有对齐情况。
- 模型以字节读取实现按 64 位字读缓冲区（`crc32_braid`、`adler32_swar`）；到字指针的转换检查对齐，但不检查
  有效类型规则（ISO C17 §6.5p7）。

## 比 `zlib.h` 更窄

| 函数 | 前提 | Lean | 原因 |
| --- | --- | --- | --- |
| `compressBound`（仅取值） | `sourceLen ≤ 0xe38e38e38e38e377`。 | `Goal.compressBound_functional` | 超过此值时和会回绕，函数返回 `ULONG_MAX`。安全性对每个 `sourceLen` 成立。 |
| `crc32_combine_op` | `op` 的低 32 位不为 0。 | `Goal.crc32_combine_op_safety` | `zlib.h` 只允许由 `crc32_combine_gen` 从非负长度生成的 `op`，它永不为 0；低半部为 0 时 `multmodp` 不返回。 |
| `zng_alloc_aligned`（内部） | `align ≥ 8` 且 `8 + size + align < 2^32`；对齐定理要求 `align = 2^k`，`3 ≤ k ≤ 31`。 | `Goal.zng_alloc_aligned_safety`、`Goal.zng_alloc_aligned_alignment` | 唯一调用者（`gz_buffer_alloc`）传入 64 与至多 `3 * 2^30` 字节。 |

## Inflate 与 uncompress

`inflate*` 与 `uncompress*` 的目标针对 `zlib.h` 允许程序到达的流（`InflateReachable`）陈述：由成功的
`inflateInit_`、`inflateInit2_` 或 `inflateCopy` 建立，此后只被参数合法的 inflate 调用以及程序改变；程序可以改变
`next_in`、`avail_in`、`next_out`、`avail_out` 和库不拥有的内存。`Z_NULL` 流或状态为 `NULL` 的流同样被接受。

| 函数 | 前提 | Lean | 原因 |
| --- | --- | --- | --- |
| `inflateInit_`、`inflateInit2_`（及由它们建立的每个流） | `zalloc` 与 `zfree` 为 `Z_NULL`（库的默认分配器）或已是默认函数。 | `InitReady` | 未对经由调用者分配器的调用建模。 |
| `inflate`、`inflateSync` | `next_in` 与 `next_out` 为 `NULL`，或分别指向 `avail_in` 个可读字节与 `avail_out` 个可写字节；这些缓冲区与已登记 `gz_header` 的缓冲区彼此不重叠，也不与库的分配重叠。 | `StreamIO` | 没有重叠理由的调用者缓冲区。 |
| `inflateSync` | `avail_in` 不为 0 时 `next_in` 不为 `NULL`。 | `SyncInput` | `avail_in` 计数的是 `next_in` 处的字节。 |
| `inflateGetDictionary` | 缓冲区为 `NULL` 或至少有 32768 个可写字节。 | `Goal.inflateGetDictionary_safety` | `zlib.h` 指明 32768 字节总是足够；调用本身只需当前窗口大小。 |
| `inflateCopy` | `dest` 与 `source` 是不同的流；`dest` 可供初始化。 | `Goal.inflateCopy_safety` | 对 `z_stream` 的复制是 `memcpy`，对同一对象未定义。 |
| `inflateGetHeader` | `head` 不为 `Z_NULL`。 | `Goal.inflateGetHeader_safety` | `zlib.h` 要求一个 `gz_header` 结构；在 gzip 流上 C 不加检查地写入 `head->done`。 |
| `inflateInit_`、`inflateInit2_`、`inflateCopy`、`inflateBackInit_`、`uncompress*` | 堆模型中尚未分配的块里没有记录任何对象（字节、`inflate_state` 或 `inflate_allocs`）。 | `FreshBlocks` | 堆模型的良构条件，程序到达的每个堆都满足；不是对 C 输入的限制。 |
| `inflate`（流的历史中的每次调用） | 静态 CRC 表保存其常量（`CrcGlobals`）。 | `InflateStep` | 在 C 中是常量数据（见上）；`Goal.inflate_safety` 对该调用本身也要求这一点。 |
| 调用之间 | 程序不改变 `z_stream` 的其他字段与库的分配，也不释放已登记的 `gz_header` 记录。该记录的任何字段都可以改变（程序或共享该记录的另一个流都可以写它）；其缓冲区在每次 `inflate` 调用时检查。 | `CallerStep` | `zlib.h` 把 `z_stream` 字段与分配保留给库；已登记的头部会被 `inflate` 写入，因此必须保持已分配。 |
| `uncompress`、`uncompress2`、`uncompress_z`、`uncompress2_z` | `dest` 与 `source` 不重叠。 | `Disjoint` | 没有重叠理由的调用者缓冲区。 |
| `uncompress`、`uncompress2`、`uncompress_z`、`uncompress2_z` | 每个对象少于 `2^63` 字节（至多 `PTRDIFF_MAX`）。 | `ObjBound` | x86_64 Linux 上的每个对象都满足。模型中一个循环至多运行 `2^64` 次，而模型本身不限制对象大小；一次性解压的循环次数受源与目标字节总数限制。 |

## Deflate 与 compress

`deflate*` 与 `compress*` 的目标陈述在 `zlib.h` 允许程序到达的流上（`DeflateReachable`）：由成功的
`deflateInit_`、`deflateInit2_` 或 `deflateCopy` 建立，此后只被参数有效的 deflate 调用以及程序改变；程序可以改变
`next_in`、`avail_in`、`next_out`、`avail_out` 以及库不拥有的内存。`Z_NULL` 流与状态为 `NULL` 的流也被接受。

| 函数 | 前提 | Lean | 理由 |
| --- | --- | --- | --- |
| `deflateInit_`、`deflateInit2_`（及由它们建立的每个流） | `zalloc` 与 `zfree` 为 `Z_NULL`（库的默认分配器）或已是默认值。 | `DInitReady` | 未建模经由调用者分配器的调用。 |
| `deflate`、`deflateParams` | `next_in` 与 `next_out` 为 `NULL` 或指向 `avail_in` 个可读、`avail_out` 个可写字节；输出与输入及已登记的 `gz_header` 缓冲区不重叠；它们都不在库的分配块内。 | `DStreamIO` | 调用者缓冲区没有理由重叠。 |
| `deflateGetDictionary` | 缓冲区为 `NULL` 或至少有 32768 个可写字节。 | `Goal.deflateGetDictionary_safety` | `zlib.h` 指明 32768 字节总是足够。 |
| `deflateCopy` | `dest` 与 `source` 是不同的流。 | `Goal.deflateCopy_safety` | 对 `z_stream` 的复制是 `memcpy`，对同一对象未定义。 |
| `deflateSetHeader`（在流的历史中） | 在首次 `deflate` 调用之前调用，所给头的 `extra` 有 `extra_len` 个可读字节，`name` 与 `comment` 为 C 字符串。 | `DeflateStep` | 这是 `zlib.h` 对 `deflateSetHeader` 的要求；调用本身任何时候都安全（`Goal.deflateSetHeader_safety`）。 |
| `deflateBound`、`deflateBound_z` | 已登记的 `gz_header` 按 `deflateSetHeader` 的要求可读；每个对象都小于 `2^63` 字节。 | `DHeaderReadable`、`ObjBound` | `deflateBound` 读取头中的字符串直到其零字节。模型中该循环至多运行 `2^64` 次，而模型本身不限制对象的大小；x86_64 Linux 上的每个对象都远小于此。 |
| `deflateInit_`、`deflateInit2_`、`deflateCopy`、`compress*` | 堆模型在尚未分配的块中不记录任何对象（字节、inflate 或 deflate 状态）。 | `DFreshBlocks` | 堆模型的良构条件，程序到达的每个堆都满足。 |
| `deflate`、`deflateParams`（流历史中的每次调用） | 静态 CRC 表保持其常量（`CrcGlobals`）。 | `DeflateStep` | C 中的常量数据。 |
| 调用之间 | 程序不改变 `z_stream` 的其他字段或库的分配块，也不释放已登记的 `gz_header` 记录。在 `deflate` 写 gzip 头期间，程序保持头的 `extra`、`extra_len`、`name`、`comment` 字段以及两个字符串的长度不变。 | `DCallerStep` | `zlib.h` 把 `z_stream` 的这些字段与分配块留给库；`deflate` 在这些缓冲区中按保存的下标继续写头。 |
| `compress`、`compress2`、`compress_z`、`compress2_z` | `dest` 与 `source` 不重叠；每个对象少于 `2^63` 字节。 | `Disjoint`、`ObjBound` | 同 `uncompress*`。 |

## 回调解压

`inflateBack` 的目标针对 `zlib.h` 允许程序到达的流（`BackReachable`）陈述：由成功的 `inflateBackInit_` 以
`2^windowBits` 个可写字节的窗口建立，此后只被回调行为如下的 `inflateBack` 调用以及程序改变。该目标未被证明（见进度页）。

| 函数 | 前提 | Lean | 原因 |
| --- | --- | --- | --- |
| `inflateBackInit_` | `zalloc` 与 `zfree` 为 `Z_NULL` 或已是默认函数。 | `InitReady` | 与 `inflateInit_` 相同。 |
| `inflateBack` | 首个输入（`next_in`、`avail_in`）与 `in()` 交出的每块输入可读，不与窗口重叠，也不在库的分配之内。 | `BackCallbacks.chunk` | 没有重叠理由的调用者缓冲区；`zlib.h` 只要求输入在下一次 `in()` 调用前保持不变。 |
| `inflateBack` | `in()` 与 `out()` 会返回，不写也不释放 `z_stream` 与库的分配，不释放窗口也不改变其大小。 | `BackCallbacks`、`BackKeep` | `zlib.h` 把它们保留给库并禁止改变窗口；写窗口内容的回调并未被排除。 |
| `inflateBack` | 一次调用总共得到少于 `2^48` 个输入字节（含首块）。 | `BackCallPre` | 输入无穷时 `inflateBack` 不返回，C 中亦然。 |
| 调用之间 | 程序只改变 `z_stream` 的 `next_in`、`avail_in`、`next_out`、`avail_out`，不改变库的分配，并保持窗口已分配且大小不变。 | `BackCallerStep` | 与 inflate 流相同；每次调用都使用窗口。 |

## 被验证源码的行为

- `len2` 为负时，`crc32_combine`、`crc32_combine64`、`crc32_combine_gen` 与 `crc32_combine_gen64` 返回 0。
- 对任意长度的 `NULL` 缓冲区，`adler32` 与 `adler32_z` 返回 1。

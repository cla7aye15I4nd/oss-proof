# 偏差：调用必须满足的条件

本页列出比 `zlib.h` 更窄、或读者可能忽略的每一个目标前提。超出这些范围的调用不在覆盖之内：既未证明安全，
也不声称不安全。

## 所有调用

- 库为 zlib-ng `develop` 分支提交 `5f1f4899` 加七个补丁，以
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
| `inflateInit_`、`inflateInit2_`、`inflateCopy`、`uncompress*` | 堆模型中尚未分配的块里没有记录 `inflate_state` 或 `inflate_allocs` 对象。 | `FreshBlocks` | 堆模型的良构条件，程序到达的每个堆都满足；不是对 C 输入的限制。 |
| 调用之间 | 程序不改变 `z_stream` 的其他字段、库的分配或已登记的 `gz_header` 记录。 | `CallerStep` | `zlib.h` 把它们保留给库。 |
| `uncompress`、`uncompress2`、`uncompress_z`、`uncompress2_z` | `dest` 与 `source` 不重叠。 | `Disjoint` | 没有重叠理由的调用者缓冲区。 |

## 被验证源码的行为

- `len2` 为负时，`crc32_combine`、`crc32_combine64`、`crc32_combine_gen` 与 `crc32_combine_gen64` 返回 0。
- 对任意长度的 `NULL` 缓冲区，`adler32` 与 `adler32_z` 返回 1。

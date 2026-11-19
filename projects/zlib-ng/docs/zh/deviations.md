<!-- source-sha256: 1a539f7b8262d13c1832b16f2a6cae160ace18eee577875f48da214eee317f5f -->
# 前提与偏差：调用必须满足的条件

本页列出目标中比 `zlib.h` 更窄、或读者可能忽略的每个前提。不满足这些条件的调用不在覆盖范围内：既未证明其安全，
也不声称其不安全。

## 每次调用

- 库为 zlib-ng 2.3.3 加七个补丁，以
  `-DZLIB_COMPAT=ON -DWITH_OPTIM=OFF -DWITH_CRC32_CHORBA=OFF -DWITH_RUNTIME_CPU_DETECTION=OFF` 构建为 x86_64
  Linux LP64，因此 `adler32` 与 `adler32_z` 运行 `adler32_c`，`crc32` 与 `crc32_z` 运行 `crc32_braid`。分派到 SIMD
  内核或 Chorba CRC-32 内核（默认）的构建不在覆盖范围内。
- 静态 CRC 表 `crc_table` 与 `x2n_table` 持有 `crc32_braid_tbl.h` 中的常量（`CrcGlobals`）。在 C 中它们是常量数据；
  在模型中它们是堆的一部分，因此 CRC 目标显式声明这一点。
- 缓冲区参数要么是 `NULL`（`len` 任意），要么指向某个存活对象内的 `len` 个可读字节（`BufferBytes`）。这正是
  `zlib.h` 的要求。
- 定理对每个对象的每个地址（`Heap.baseAddr`）成立，因此缓冲区的每种对齐方式都被覆盖。

## 比 `zlib.h` 更窄的前提

| 函数 | 前提 | Lean | 原因 |
| --- | --- | --- | --- |
| `compressBound`（仅返回值） | `sourceLen ≤ 0xe38e38e38e38e377`。 | `Goal.compressBound_functional` | 超过该值时上界按 2^64 取模回绕。安全性对每个 `sourceLen` 都成立。 |
| `zng_alloc_aligned`（内部） | `align` 为 0 或至少为 8；对齐定理要求 `align = 2^k` 且 `3 ≤ k ≤ 31`。 | `Goal.zng_alloc_aligned_safety`、`Goal.zng_alloc_aligned_alignment` | 唯一调用者（`gz_buffer_alloc`）传入 64。 |

## 与未打补丁的 zlib-ng 行为不同之处

- 对负的 `len2`，`crc32_combine`、`crc32_combine64`、`crc32_combine_gen` 与 `crc32_combine_gen64` 返回 0；当 `op`
  的低 32 位为 0 时，`crc32_combine_op` 返回 0（补丁 0002）。未打补丁时这些调用不会返回。
- 对长度为 1 的 `NULL` 缓冲区，`adler32` 与 `adler32_z` 返回 1（补丁 0007）。未打补丁时它们经由空指针读取。

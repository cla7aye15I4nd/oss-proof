<!-- source-sha256: 99a376f10657c0511da07f1e0a55f35673bcdce5aca170dbaa62f5cd1bf23297 -->
# `uncompress*` 的安全性

`uncompress`、`uncompress_z`、`uncompress2` 和 `uncompress2_z` 在满足下列前提的每个输入上都是安全的，不论源字节是什么：调用会返回，没有未定义行为，只写目的缓冲区和长度单元，并且释放它分配的一切。本页给出这条陈述、它的前提和证明的轮廓。

源文件：`uncompr.c`。[缓冲区工具函数](buffers.md)一页解读这段 C。术语见[术语表](../glossary.md)。

## 证明了什么

| 目标（`ZlibF/Spec/Safety/Utilities.lean`） | 定理 | 模块 |
| --- | --- | --- |
| `Goal.uncompress2_z_safe` | `uncompress2_z_safe` | `ZlibF/Proof/public-uncompress-safe.lean` |
| `Goal.uncompress2_safe` | `uncompress2_safe` | 同上 |
| `Goal.uncompress_z_safe` | `uncompress_z_safe` | 同上 |
| `Goal.uncompress_safe` | `uncompress_safe` | 同上 |

这四个都是安全结果，都是必需的。每个定理证明的正是所陈述的目标，没有附加假设；下面的前提是目标陈述的一部分。这些定理[已登记](../checking/README.md)在 `tests/audit/theorems.txt` 中，并[已在提交 `bde170e9` 上验收](../checking/README.md)（[进度，Scope 一节](../progress.md#scope)）。

这些目标是 `UncompressCountedSafe` 和 `UncompressSingleSafe`（`ZlibF/Spec/Public/Utilities.lean`）的实例。对满足下列前提的每个输入：

- 调用在没有未定义行为的情况下运行并返回。用 Lean 的话说：在堆上运行翻译后的函数，得到带有返回码和新堆的 `.ok`，而不是故障；
- 参数错误返回 `Z_STREAM_ERROR`，并且什么都不改变；
- 否则，调用向输出缓冲区写入至多 `capacity` 个字节，并写长度单元，此外什么都不写；
- 每次分配在每条返回路径上都被释放；
- 返回码是 `Z_OK`、`Z_BUF_ERROR`、`Z_DATA_ERROR` 或 `Z_MEM_ERROR`，并且 `Z_MEM_ERROR` 只在某次分配失败之后出现。

关于写出的字节，这里什么都没有说。那是功能目标 `Goal.uncompress*`，不是安全结果所必需的。

## 假设了什么

| 前提 | 含义 |
| --- | --- |
| `Fresh`、`Uniq`、`LibraryGlobals` | 调用者的堆是良构的，静态表是初始的那些表。 |
| `ByteObjectsFit` | 每个字节对象少于 `2^63` 个字节。 |
| 可读的源缓冲区、可写的目的缓冲区、长度单元 | 每个非 NULL 的指针指向一个所述大小的范围或一个八字节的单元。`uncompress` 和 `uncompress2` 取非 NULL 的单元；`_z` 形式接受 `NULL` 并拒绝它。 |
| `UtilitySeparation` | 源缓冲区、目的缓冲区、目的长度单元和源长度单元两两分离。 |

这一分离在[偏离记录](../deviations.md)中有一行：“计数解压”。

## 结构

```mermaid
flowchart TD
  init["start_state：在局部流上执行 inflateInit2_"] --> loop
  loop["loop_run_safe：循环 do ... while (err == Z_OK)"] --> call
  call["call_phase_safe：一次 inflate 调用（inflate_public）"] --> loop
  loop --> epi["epilogue：存入计数、inflateEnd、释放流和保留字节"]
  epi --> z["uncompress2_z_with_safe"]
  z --> w2["counted2_of_z：uncompress2"]
  z --> w1["single_of_counted：uncompress_z, uncompress"]
```

证明只写一次，对结果上的任意关系都适用（`CountedWith`、`SingleWith`）。安全目标用 `SafeRel` 实例化它：输出不超过容量，已消耗的输入不超过源数据，返回码是文档列出的那些之一。`SafeState` 和 `SafeFinal` 是这个证明的循环状态和最终状态；除格式事实之外，它们包含了一切。功能证明不是安全结果所必需的，它用 `NoOver` 扩展这两个状态：位于源数据开头的任何完整流都没有被读到末尾。

## 证明用到了什么

- `inflate_public`，即一次 `inflate` 调用的完整契约（`Goal.inflate`），用于每次调用。`Goal.inflate` 是功能契约。安全证明使用它的进展子句、帧子句和所有权子句。
- `reach_invariant`，用于每个可达流的解码器。

没有用到 `inflate` 的任何格式事实。

## 终止

度量是未读的源数据加上未填的空间：`avail_in + len + avail_out + left`，其中 `len` 和 `left` 是 C 的局部变量：尚未交给流的源字节数和目的空间。补充只是在流的字段与剩余长度之间搬动字节，所以保持度量不变。根据 `Goal.inflate` 的进展子句 `rc = Z_OK → used ≠ 0 ∨ out ≠ []`，每次返回 `Z_OK` 的调用都消耗输入或写出输出。所以度量下降。开始时它至多是 `sourceLen + destLen`，低于循环燃料 `2^64`。所用规则是 `cdoWhile_decreasing`。

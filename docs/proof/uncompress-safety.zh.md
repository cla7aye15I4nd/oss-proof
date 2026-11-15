<!-- source-sha256: f817cf2761d4f30e396ee0526f8adb2d72d0de63223ae95b048151e58a76a151 -->
# `uncompress*` 的安全性

源文件为 `uncompr.c`。`uncompress`、`uncompress_z`、`uncompress2` 和 `uncompress2_z` 在每个输入上都是安全的。本页解释这个结果。

## 已证明什么

| 目标（`ZlibF/Spec/Safety/Utilities.lean`） | 定理 | 模块 |
| --- | --- | --- |
| `Goal.uncompress2_z_safe` | `uncompress2_z_safe` | `ZlibF/Proof/public-uncompress-safe.lean` |
| `Goal.uncompress2_safe` | `uncompress2_safe` | 同上 |
| `Goal.uncompress_z_safe` | `uncompress_z_safe` | 同上 |
| `Goal.uncompress_safe` | `uncompress_safe` | 同上 |

四者都是安全性结果，都是必需的，都没有假设。它们登记在 `tests/audit/theorems.txt` 中，并在提交 `bde170e9` 上被接受（[进度，范围](../progress.md#scope)）。

这些目标是 `UncompressCountedSafe` 和 `UncompressSingleSafe`（`ZlibF/Spec/Public/Utilities.lean`）的实例。对每个允许的输入：

- 调用在没有未定义行为的情况下运行并返回（`C.run … = .ok`）；
- 参数错误返回 `Z_STREAM_ERROR`，不改变任何东西；
- 否则，调用向输出缓冲区写入不超过 `capacity` 的字节，并写长度单元，不写其他任何地方；
- 每次分配在每条返回路径上都被释放；
- 返回码是 `Z_OK`、`Z_BUF_ERROR`、`Z_DATA_ERROR` 或 `Z_MEM_ERROR`，并且 `Z_MEM_ERROR` 只在某次分配失败之后出现。

目标对写出的字节不作任何断言。那是功能性目标 `Goal.uncompress*`，不是必需的。

## 假设了什么

| 前提 | 含义 |
| --- | --- |
| `Fresh`、`Uniq`、`LibraryGlobals` | 调用者的堆是良构的，静态表是初始的那些表。 |
| `ByteObjectsFit` | 每个字节对象小于 `2^63` 字节。 |
| 可读的源、可写的目标、长度单元 | 每个非空指针指向所述大小的范围或八字节单元。 |
| `UtilitySeparation` | 源、目标、目标长度单元和源长度单元两两分离。 |

这一分离在[偏差记录](../deviations.md)中有一行，名为“计数解压”。

## 结构

```mermaid
flowchart TD
  init["start_state：inflateInit2_ 与绑定好的流"] --> loop
  loop["loop_run_safe：循环 do ... while (err == Z_OK)"] --> call
  call["call_phase_safe：一次 inflate 调用（inflate_public）"] --> loop
  loop --> epi["epilogue：保存计数、inflateEnd、释放流和保留字节"]
  epi --> z["uncompress2_z_with_safe"]
  z --> w2["counted2_of_z：uncompress2"]
  z --> w1["single_of_counted：uncompress_z、uncompress"]
```

这次运行与功能性证明共用。`SafeState` 和 `SafeFinal` 保存除格式事实之外的一切。功能性证明在它们之上增加 `NoOver`：源开头处没有哪个完整的流被读到了末尾。包装函数对每个数据关系只证明一次（`CountedWith`、`SingleWith`）。安全目标使用关系 `SafeRel`：输出不超过容量，已消耗的输入不超过源，返回码是文档规定的。

## 证明用到什么

- `inflate_public`，即单次 `inflate` 调用的完整契约（`Goal.inflate`），用于每次调用。`Goal.inflate` 是功能性契约。安全性证明使用它的进展、帧和所有权子句。
- `reach_invariant`，用于每个可达流的解码器。

没有用到 `inflate` 的任何格式事实。

## 终止

度量是未读的源加上未填的空间：`avail_in + len + avail_out + left`。补充缓冲区的操作只是在流字段和剩余长度之间移动字节，所以保持它不变。根据 `Goal.inflate` 的进展子句 `rc = Z_OK → used ≠ 0 ∨ out ≠ []`，每次返回 `Z_OK` 的调用都消耗了输入或写出了输出，所以度量下降。它的初值至多为 `sourceLen + destLen < 2^64`，低于循环燃料。所用规则是 `cdoWhile_decreasing`。

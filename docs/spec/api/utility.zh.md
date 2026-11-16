<!-- source-sha256: e62c84514bd33bc066bb971b0b84e776e7e4cecdf81cec9f0ef57087f401ab7c -->

# 缓冲区工具与库信息

[API 手册](README.md) · [共享流规则](streams.md) · [校验和](checksums.md)

调用时若已知完整的输入和输出容量，可使用缓冲区工具。它们在内部管理临时流。
需要增量 I/O、其他封装、字典或显式刷新边界时，应使用流式接口页面。

| 任务 | 条目 |
| --- | --- |
| 压缩缓冲区 | [选择级别](#compress2_z)、[默认级别](#compress_z)、[确定目的缓冲区容量](#compressbound_z) |
| 解压缓冲区 | [报告已消费输入](#uncompress2_z)、[仅报告输出](#uncompress_z) |
| 查询库信息 | [版本](#zlibversion)、[编译标志](#zlibcompileflags)、[错误文本](#zerror) |

这些契约遵循固定版本的 `compress.c`、`uncompr.c`、`zutil.c` 和 `zlib.h`，采用默认 LP64 Linux 构建。
没有补丁改动这三个 C 文件（见[补丁说明](../../../patches/README.md)）。
`_z` 形式使用 `z_size_t`；普通形式使用 `uLong`。这里两者均为 64 位。
定义域和效果标签见[契约约定](contracts.md)。
这些是聚焦契约：前置条件描述通常的正确用法，有意比函数实际接受的范围窄。
超出前置条件的调用并不因此就是未定义行为，也不一定返回错误码。

**已证明的内容。** 只证明安全性：每次调用都返回，没有未定义行为和内存错误，只写其目标指明的内容，并且不泄漏（见[安全性](../safety.md)）。各条目在“证明目标”下给出自己的目标，所用的五项和固定用语由[阅读证明目标段落](contracts.md#reading-a-proof-goals-paragraph)定义：目标及其定理；目标适用的条件，按 Lean 命题中的顺序列出；对每一个取值都覆盖的内容；保证的内容（返回、状态、写入、分配）；以及留给其他目标的内容。证明所假设的是那里列出的条件，而不是文档中的前置条件。后置条件、返回值表和各项说明描述的是功能行为：它们读自 C 源码，凡是没有已登记定理陈述的，都**尚未由证明确认**；安全结论不需要它们。各目标的状态见[进度](../../progress.md)。

安全目标在 [Safety/Utilities.lean](../../../ZlibF/Spec/Safety/Utilities.lean) 和
[Safety/Queries.lean](../../../ZlibF/Spec/Safety/Queries.lean) 中；它们所实例化的命题
（`CompressorSafety`、`UncompressCountedSafe`、`UncompressSingleSafe`）定义在
[Public/Utilities.lean](../../../ZlibF/Spec/Public/Utilities.lean) 中。功能目标在
[Functional/Utilities.lean](../../../ZlibF/Spec/Functional/Utilities.lean) 和
[Functional/Queries.lean](../../../ZlibF/Spec/Functional/Queries.lean) 中。
[Calls.lean](../../../ZlibF/Spec/Public/Calls.lean) 固定翻译后的参数和结果。

缓冲区工具使用 zlib 封装和默认设置，创建并释放一个局部流。

先说明长度的约定：`sourceLen` 指定可读输入的字节数；`*destLen` 在调用前是目的数组的可写容量，调用后改为实际写入量。例如目的缓冲区有 1000 字节容量、最终写入 120 字节，调用前应设置 `*destLen = 1000`，成功返回后读取到 120。这个长度单元自身也是需要保持存活、可读写的调用者存储。`uncompress2_z` 的 `*sourceLen` 同样在调用前给出可用的输入字节数，返回后报告已消费的字节数。

上界函数只计算一个数，并不分配目的数组。

```mermaid
flowchart LR
    B["compressBound"] --> C["compress / compress2"]
    C --> Z["zlib 流"] --> U["uncompress / uncompress2"]
    U --> D["解码字节"]
```

### 通用约定

缓冲区调用的定义域限于有效内存：非 NULL 源覆盖指定的可读输入；
非 NULL 目的缓冲区覆盖指定的可写容量。非 NULL 长度指针指向可读写的标量单元。
输入、输出和长度单元互相分离，包括同时出现的两个长度单元。
调用期间，调用者保持这些对象存活且不修改它们。
各条目分别说明允许的 NULL 情形。其他无效指针不在此范围内。
处理解压错误不要求压缩数据有效。

**通用效果。** 范围内的每次调用都终止，且不产生故障。
缓冲区调用保持输入以及输出、长度单元以外的内存不变，写入不超过原始容量。
返回前释放所有内部分配，包括分配失败路径；调用不给调用者留下局部流，也不留下它自己做的分配。
返回指针的查询，返回的是借用的不可变存储。
“证明目标”下列出的安全目标陈述了这些效果，借用存储那一条除外；输出的内容属于功能行为。

**模型中的长度单元。** 对 `compress`、`compress2` 及它们的 `_z` 形式，翻译把 `*destLen` 作为值传递：函数接收容量（或者 `destLen` 为 NULL 这一事实），并返回要存入的长度。这个单元在模型中不是内存，所以这四个函数的安全目标无法谈论与源或目的缓冲区重叠的长度单元（见[偏离记录](../../deviations.md)中“整缓冲区压缩”一行）。对 `uncompress` 系列，长度单元是内存，每个为 8 个可读可写的字节，它们与缓冲区的分离是目标中写明的条件。

## compress2_z

```c
int ZEXPORT compress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source,
                        z_size_t sourceLen, int level);
```

按请求级别，将输入压缩为一个完整 zlib 流。

### 返回值与后续调用 {#api-compress2_z-returns}

**返回值类型。** `int` — zlib 状态码；输出长度另行写回

状态码说明整个缓冲区是否已压成完整 zlib 流。字节数在 `*destLen` 中。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**完整压缩完成** | 输出是完整的 zlib 编码；`*destLen` 是写入字节数。 | 使用恰好 `*destLen` 字节作为压缩结果。 |
| `Z_BUF_ERROR`<br>**输出容量耗尽** | 容量由编码前缀填满；非 NULL 目的缓冲区配合零容量在成功初始化后也返回此码。`*destLen` 报告已写字节数。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目的缓冲区容量。提供更大的目的缓冲区，从原始输入重新调用；这个前缀不是完整的流。 |
| `Z_MEM_ERROR`<br>**分配失败且无输出** | 通过早期参数检查且级别有效后，初始化分配失败。没有写入输出；`*destLen` 为零。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目的缓冲区容量。仅在资源允许时重新发起完整调用；本次没有压缩结果。 |
| `Z_STREAM_ERROR`<br>**早期参数拒绝** | source 为 NULL 且 sourceLen > 0，或 dest 为 NULL 且原始容量 > 0。destLen == NULL 也经检查后拒绝。现有长度值不变。 | 修正已拒绝的参数，再用有效缓冲区重新调用。 |
| `Z_STREAM_ERROR`<br>**无效压缩级别** | 通过早期参数检查后，level 不在 -1 或 0–9 中；分配前将 `*destLen` 置零。 | 选择 -1 或 0–9，并为新调用重新设置输出容量。 |
| `Z_STREAM_ERROR`<br>**零容量 NULL 目的缓冲区** | 通过早期参数检查且级别有效，dest == NULL 且容量为零，初始化成功；`*destLen` 为零。分配失败时则返回 Z_MEM_ERROR。 | 提供有效的目的缓冲区和足够容量，再重新调用。 |

**判读要点。**

- 调用前 `*destLen` 是容量；返回后除早期拒绝外是实际写入量。所有内部分配在每条返回路径上均释放。
- destLen 可以为 NULL，此时调用经检查后拒绝；非 NULL 的长度单元须可读写。
- 输入、目的缓冲区及长度单元必须互相分离并覆盖所述范围。空输入有效。-1 选择级别 6。

### 调用条件与效果 {#api-compress2_z-contract}

**定义域。** 受限定义域。

**前置条件。** 上述受限缓冲区定义域。`source` 可在零输入或经检查的拒绝情形中为 NULL。
`destLen` 可在经检查的拒绝情形中为 NULL。`dest` 可在经检查的拒绝情形中为 NULL，
包括下面的零容量情形。有效级别为 -1 和 0–9；-1 选择级别 6。

**效果。** 有状态；适用通用效果。非零输入的 NULL 源、NULL `destLen`，或非零容量的
NULL 目的缓冲区，会在任何长度写入之前返回 `Z_STREAM_ERROR`。
否则在初始化前清零 `*destLen`。无效级别在任何分配前返回 `Z_STREAM_ERROR`，长度为零。
后续返回会存储已写字节数。

**证明目标。**

- **目标。** `Goal.compress2_z_safety`（[Safety/Utilities.lean](../../../ZlibF/Spec/Safety/Utilities.lean)；其命题是 [Public/Utilities.lean](../../../ZlibF/Spec/Public/Utilities.lean) 中的 `CompressorSafety`）；必需。定理：`ZlibF.Spec.Public.Proofs.Compress.compress2_z_safety`（[public-compress-safe-mid.lean](../../../ZlibF/Proof/public-compress-safe-mid.lean)）。
- **适用条件**（`CompressorSafety`）：
    1. 堆是库堆（`Fresh`、`Uniq`、`LibraryGlobals`）；
    2. 平台大小上界成立（`ByteObjectsFit`）；
    3. 参数或者属于调用会拒绝的情况（`destLen` 为 NULL、`source` 为 NULL 而 `sourceLen` 非零，或 `dest` 为 NULL 而 `*destLen` 非零；`compressRejected`），或者满足：`source` 指向 `sourceLen` 个可读字节，`dest` 指向 `*destLen` 个可写字节，且两个范围不重叠（`CompressArguments`）。NULL 的 `source` 或 `dest` 视为零字节的范围。
- **无条件覆盖。** `destLen` 为 NULL（调用会拒绝）；每一个 `level`，无论是否有效；源字节的每一种内容；每一种分配结果。在翻译中，长度单元 `*destLen` 是一个值而不是内存（见[通用约定](#common-conventions)）：对于与缓冲区重叠的长度单元，本目标什么也没说，前置条件也排除了这种情况。
- **保证。**
    - *返回。* 调用返回。参数属于被拒绝的情况时，返回值是 `Z_STREAM_ERROR`。只有在某次分配确实失败之后才返回 `Z_MEM_ERROR`（`AllocationFailed`）。
    - *状态。* 不保留任何状态：调用结束后，它用过的流、状态和缓冲区都不存在。
    - *写入。* 只写 `dest` 处的字节，至多为进入时给出的 `*destLen` 个；参数被拒绝时不写任何内容，长度值也不变。其他对象都不变（`Store`、`SameObjectsUpToTableShape`）。
    - *分配。* 调用分配的每个块都在返回之前释放，每条路径都是如此：已分配的块与调用前相同。
- **不在本目标内。** `source` 与 `dest` 重叠：在所有目标之外（见[偏离记录](../../deviations.md)中“整缓冲区压缩”一行）。参数被接受时返回哪个状态码、写出哪些字节、存入的长度：功能目标 `Goal.compress2_z`，安全结论不需要它。

<details markdown="1" class="ar-return-exact" data-return-exact="compress2_z"><summary>完整返回条件与边界</summary>

**后置条件。** `Z_OK` 表示输出是输入的完整 zlib 编码，且 `*destLen` 是其长度。
`Z_BUF_ERROR` 表示容量已由该编码的一个前缀填满。
`Z_MEM_ERROR` 表示分配失败，且没有写入输出。

**边缘情形。** NULL 目的缓冲区配合零容量会进入初始化：若分配失败，返回 `Z_MEM_ERROR`，
否则返回 `Z_STREAM_ERROR`，长度为零。非 NULL 目的缓冲区配合零容量，在成功初始化后返回
`Z_BUF_ERROR`。空输入有效。

</details>

## compress2

```c
int ZEXPORT compress2(Bytef *dest, uLongf *destLen, const Bytef *source,
                      uLong sourceLen, int level);
```

[compress2_z](#compress2_z) 的 `uLong` 形式。

### 返回值与后续调用 {#api-compress2-returns}

**返回值类型。** `int` — zlib 状态码；输出长度另行写回

状态码说明整个缓冲区是否已压成完整 zlib 流。字节数在 `*destLen` 中。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**完整压缩完成** | 输出是完整的 zlib 编码；`*destLen` 是写入字节数。 | 使用恰好 `*destLen` 字节作为压缩结果。 |
| `Z_BUF_ERROR`<br>**输出容量耗尽** | 容量由编码前缀填满；非 NULL 目的缓冲区配合零容量在成功初始化后也返回此码。`*destLen` 报告已写字节数。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目的缓冲区容量。提供更大的目的缓冲区，从原始输入重新调用；这个前缀不是完整的流。 |
| `Z_MEM_ERROR`<br>**分配失败且无输出** | 通过早期参数检查且级别有效后，初始化分配失败。没有写入输出；`*destLen` 为零。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目的缓冲区容量。仅在资源允许时重新发起完整调用；本次没有压缩结果。 |
| `Z_STREAM_ERROR`<br>**早期参数拒绝** | source 为 NULL 且 sourceLen > 0，或 dest 为 NULL 且原始容量 > 0。现有长度值不变。 | 修正已拒绝的参数，再用有效缓冲区重新调用。 |
| `Z_STREAM_ERROR`<br>**无效压缩级别** | 通过早期参数检查后，level 不在 -1 或 0–9 中；分配前将 `*destLen` 置零。 | 选择 -1 或 0–9，并为新调用重新设置输出容量。 |
| `Z_STREAM_ERROR`<br>**零容量 NULL 目的缓冲区** | 通过早期参数检查且级别有效，dest == NULL 且容量为零，初始化成功；`*destLen` 为零。分配失败时则返回 Z_MEM_ERROR。 | 提供有效的目的缓冲区和足够容量，再重新调用。 |

**判读要点。**

- 调用前 `*destLen` 是容量；返回后除早期拒绝外是实际写入量。所有内部分配在每条返回路径上均释放。
- 普通适配器先读取非 NULL 的 destLen 单元，且每次返回都写回长度；NULL destLen 不在这个前置条件内。
- 输入、目的缓冲区及长度单元必须互相分离并覆盖所述范围。空输入有效。-1 选择级别 6。

### 调用条件与效果 {#api-compress2-contract}

**定义域。** 受限定义域。

**前置条件。** `compress2_z` 的受限定义域，且 `destLen` 单元非 NULL。
包装函数会先读取该单元，再调用带检查的 `_z` 条目。

**效果。** 有状态；缓冲区效果和清理效果与 `compress2_z` 相同。
包装函数在每次返回时写回长度，包括错误返回。
早期参数拒绝保持其原值；无效级别或分配失败使其为零。

**证明目标。**

- **目标。** `Goal.compress2_safety`（[Safety/Utilities.lean](../../../ZlibF/Spec/Safety/Utilities.lean)；其命题是 [Public/Utilities.lean](../../../ZlibF/Spec/Public/Utilities.lean) 中的 `CompressorSafety`）；必需。定理：`ZlibF.Spec.Public.Proofs.Compress.compress2_safety`（[public-compress-safe-mid.lean](../../../ZlibF/Proof/public-compress-safe-mid.lean)）。
- **适用条件**（`CompressorSafety`）：
    1. 堆是库堆（`Fresh`、`Uniq`、`LibraryGlobals`）；
    2. 平台大小上界成立（`ByteObjectsFit`）；
    3. `destLen` 不为 NULL；
    4. 参数或者属于调用会拒绝的情况（`source` 为 NULL 而 `sourceLen` 非零，或 `dest` 为 NULL 而 `*destLen` 非零；`compressRejected`），或者满足：`source` 指向 `sourceLen` 个可读字节，`dest` 指向 `*destLen` 个可写字节，且两个范围不重叠（`CompressArguments`）。NULL 的 `source` 或 `dest` 视为零字节的范围。
- **无条件覆盖。** 每一个 `level`，无论是否有效；源字节的每一种内容；每一种分配结果。在翻译中，长度单元 `*destLen` 是一个值而不是内存（见[通用约定](#common-conventions)）：对于与缓冲区重叠的长度单元，本目标什么也没说，前置条件也排除了这种情况。
- **保证。**
    - *返回。* 调用返回。参数属于被拒绝的情况时，返回值是 `Z_STREAM_ERROR`。只有在某次分配确实失败之后才返回 `Z_MEM_ERROR`（`AllocationFailed`）。
    - *状态。* 不保留任何状态：调用结束后，它用过的流、状态和缓冲区都不存在。
    - *写入。* 只写 `dest` 处的字节，至多为进入时给出的 `*destLen` 个；参数被拒绝时不写任何内容，长度值也不变。其他对象都不变（`Store`、`SameObjectsUpToTableShape`）。
    - *分配。* 调用分配的每个块都在返回之前释放，每条路径都是如此：已分配的块与调用前相同。
- **不在本目标内。** `source` 与 `dest` 重叠：在所有目标之外（见[偏离记录](../../deviations.md)中“整缓冲区压缩”一行）。参数被接受时返回哪个状态码、写出哪些字节、存入的长度：功能目标 `Goal.compress2`，安全结论不需要它。

<details markdown="1" class="ar-return-exact" data-return-exact="compress2"><summary>完整返回条件与边界</summary>

**后置条件。** 编码和返回码契约与 `compress2_z` 相同。

</details>

## compress_z

```c
int ZEXPORT compress_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t sourceLen);
```

按默认级别压缩（-1，选择级别 6）。

### 返回值与后续调用 {#api-compress_z-returns}

**返回值类型。** `int` — zlib 状态码；输出长度另行写回

状态码说明整个缓冲区是否已压成完整 zlib 流。字节数在 `*destLen` 中。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**完整压缩完成** | 输出是完整的 zlib 编码；`*destLen` 是写入字节数。 | 使用恰好 `*destLen` 字节作为压缩结果。 |
| `Z_BUF_ERROR`<br>**输出容量耗尽** | 容量由编码前缀填满；非 NULL 目的缓冲区配合零容量在成功初始化后也返回此码。`*destLen` 报告已写字节数。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目的缓冲区容量。提供更大的目的缓冲区，从原始输入重新调用；这个前缀不是完整的流。 |
| `Z_MEM_ERROR`<br>**分配失败且无输出** | 通过早期参数检查后，初始化分配失败。没有写入输出；`*destLen` 为零。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目的缓冲区容量。仅在资源允许时重新发起完整调用；本次没有压缩结果。 |
| `Z_STREAM_ERROR`<br>**早期参数拒绝** | source 为 NULL 且 sourceLen > 0，或 dest 为 NULL 且原始容量 > 0。destLen == NULL 也经检查后拒绝。现有长度值不变。 | 修正已拒绝的参数，再用有效缓冲区重新调用。 |
| `Z_STREAM_ERROR`<br>**零容量 NULL 目的缓冲区** | 通过早期参数检查，dest == NULL 且容量为零，初始化成功；`*destLen` 为零。分配失败时则返回 Z_MEM_ERROR。 | 提供有效的目的缓冲区和足够容量，再重新调用。 |

**判读要点。**

- 调用前 `*destLen` 是容量；返回后除早期拒绝外是实际写入量。所有内部分配在每条返回路径上均释放。
- destLen 可以为 NULL，此时调用经检查后拒绝；非 NULL 的长度单元须可读写。
- 输入、目的缓冲区及长度单元必须互相分离并覆盖所述范围。空输入有效。使用默认级别 -1，即级别 6。

### 调用条件与效果 {#api-compress_z-contract}

**定义域。** 受限定义域。

**前置条件。** [compress2_z](#compress2_z) 的受限定义域，不包含级别参数。

**效果。** 有状态；长度写入、经检查的 NULL 情形和完整清理均与 `compress2_z` 相同。

**证明目标。**

- **目标。** `Goal.compress_z_safety`（[Safety/Utilities.lean](../../../ZlibF/Spec/Safety/Utilities.lean)；其命题是 [Public/Utilities.lean](../../../ZlibF/Spec/Public/Utilities.lean) 中的 `CompressorSafety`）；必需。定理：`ZlibF.Spec.Public.Proofs.Compress.compress_z_safety`（[public-compress-safe-mid.lean](../../../ZlibF/Proof/public-compress-safe-mid.lean)）。
- **适用条件**（`CompressorSafety`）：
    1. 堆是库堆（`Fresh`、`Uniq`、`LibraryGlobals`）；
    2. 平台大小上界成立（`ByteObjectsFit`）；
    3. 参数或者属于调用会拒绝的情况（`destLen` 为 NULL、`source` 为 NULL 而 `sourceLen` 非零，或 `dest` 为 NULL 而 `*destLen` 非零；`compressRejected`），或者满足：`source` 指向 `sourceLen` 个可读字节，`dest` 指向 `*destLen` 个可写字节，且两个范围不重叠（`CompressArguments`）。NULL 的 `source` 或 `dest` 视为零字节的范围。
- **无条件覆盖。** `destLen` 为 NULL（调用会拒绝）；源字节的每一种内容；每一种分配结果。在翻译中，长度单元 `*destLen` 是一个值而不是内存（见[通用约定](#common-conventions)）：对于与缓冲区重叠的长度单元，本目标什么也没说，前置条件也排除了这种情况。
- **保证。**
    - *返回。* 调用返回。参数属于被拒绝的情况时，返回值是 `Z_STREAM_ERROR`。只有在某次分配确实失败之后才返回 `Z_MEM_ERROR`（`AllocationFailed`）。
    - *状态。* 不保留任何状态：调用结束后，它用过的流、状态和缓冲区都不存在。
    - *写入。* 只写 `dest` 处的字节，至多为进入时给出的 `*destLen` 个；参数被拒绝时不写任何内容，长度值也不变。其他对象都不变（`Store`、`SameObjectsUpToTableShape`）。
    - *分配。* 调用分配的每个块都在返回之前释放，每条路径都是如此：已分配的块与调用前相同。
- **不在本目标内。** `source` 与 `dest` 重叠：在所有目标之外（见[偏离记录](../../deviations.md)中“整缓冲区压缩”一行）。参数被接受时返回哪个状态码、写出哪些字节、存入的长度：功能目标 `Goal.compress_z`，安全结论不需要它。

<details markdown="1" class="ar-return-exact" data-return-exact="compress_z"><summary>完整返回条件与边界</summary>

**后置条件。** 与默认级别的 `compress2_z` 相同。

</details>

## compress

```c
int ZEXPORT compress(Bytef *dest, uLongf *destLen, const Bytef *source, uLong sourceLen);
```

默认级别的 `uLong` 压缩条目。

### 返回值与后续调用 {#api-compress-returns}

**返回值类型。** `int` — zlib 状态码；输出长度另行写回

状态码说明整个缓冲区是否已压成完整 zlib 流。字节数在 `*destLen` 中。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**完整压缩完成** | 输出是完整的 zlib 编码；`*destLen` 是写入字节数。 | 使用恰好 `*destLen` 字节作为压缩结果。 |
| `Z_BUF_ERROR`<br>**输出容量耗尽** | 容量由编码前缀填满；非 NULL 目的缓冲区配合零容量在成功初始化后也返回此码。`*destLen` 报告已写字节数。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目的缓冲区容量。提供更大的目的缓冲区，从原始输入重新调用；这个前缀不是完整的流。 |
| `Z_MEM_ERROR`<br>**分配失败且无输出** | 通过早期参数检查后，初始化分配失败。没有写入输出；`*destLen` 为零。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目的缓冲区容量。仅在资源允许时重新发起完整调用；本次没有压缩结果。 |
| `Z_STREAM_ERROR`<br>**早期参数拒绝** | source 为 NULL 且 sourceLen > 0，或 dest 为 NULL 且原始容量 > 0。现有长度值不变。 | 修正已拒绝的参数，再用有效缓冲区重新调用。 |
| `Z_STREAM_ERROR`<br>**零容量 NULL 目的缓冲区** | 通过早期参数检查，dest == NULL 且容量为零，初始化成功；`*destLen` 为零。分配失败时则返回 Z_MEM_ERROR。 | 提供有效的目的缓冲区和足够容量，再重新调用。 |

**判读要点。**

- 调用前 `*destLen` 是容量；返回后除早期拒绝外是实际写入量。所有内部分配在每条返回路径上均释放。
- 普通适配器先读取非 NULL 的 destLen 单元，且每次返回都写回长度；NULL destLen 不在这个前置条件内。
- 输入、目的缓冲区及长度单元必须互相分离并覆盖所述范围。空输入有效。使用默认级别 -1，即级别 6。

### 调用条件与效果 {#api-compress-contract}

**定义域。** 受限定义域。

**前置条件。** [compress2](#compress2) 的受限定义域；`destLen` 必须非 NULL。

**效果。** 有状态；长度写入和完整清理与 `compress2` 相同。

**证明目标。**

- **目标。** `Goal.compress_safety`（[Safety/Utilities.lean](../../../ZlibF/Spec/Safety/Utilities.lean)；其命题是 [Public/Utilities.lean](../../../ZlibF/Spec/Public/Utilities.lean) 中的 `CompressorSafety`）；必需。定理：`ZlibF.Spec.Public.Proofs.Compress.compress_safety`（[public-compress-safe-mid.lean](../../../ZlibF/Proof/public-compress-safe-mid.lean)）。
- **适用条件**（`CompressorSafety`）：
    1. 堆是库堆（`Fresh`、`Uniq`、`LibraryGlobals`）；
    2. 平台大小上界成立（`ByteObjectsFit`）；
    3. `destLen` 不为 NULL；
    4. 参数或者属于调用会拒绝的情况（`source` 为 NULL 而 `sourceLen` 非零，或 `dest` 为 NULL 而 `*destLen` 非零；`compressRejected`），或者满足：`source` 指向 `sourceLen` 个可读字节，`dest` 指向 `*destLen` 个可写字节，且两个范围不重叠（`CompressArguments`）。NULL 的 `source` 或 `dest` 视为零字节的范围。
- **无条件覆盖。** 源字节的每一种内容；每一种分配结果。在翻译中，长度单元 `*destLen` 是一个值而不是内存（见[通用约定](#common-conventions)）：对于与缓冲区重叠的长度单元，本目标什么也没说，前置条件也排除了这种情况。
- **保证。**
    - *返回。* 调用返回。参数属于被拒绝的情况时，返回值是 `Z_STREAM_ERROR`。只有在某次分配确实失败之后才返回 `Z_MEM_ERROR`（`AllocationFailed`）。
    - *状态。* 不保留任何状态：调用结束后，它用过的流、状态和缓冲区都不存在。
    - *写入。* 只写 `dest` 处的字节，至多为进入时给出的 `*destLen` 个；参数被拒绝时不写任何内容，长度值也不变。其他对象都不变（`Store`、`SameObjectsUpToTableShape`）。
    - *分配。* 调用分配的每个块都在返回之前释放，每条路径都是如此：已分配的块与调用前相同。
- **不在本目标内。** `source` 与 `dest` 重叠：在所有目标之外（见[偏离记录](../../deviations.md)中“整缓冲区压缩”一行）。参数被接受时返回哪个状态码、写出哪些字节、存入的长度：功能目标 `Goal.compress`，安全结论不需要它。

<details markdown="1" class="ar-return-exact" data-return-exact="compress"><summary>完整返回条件与边界</summary>

**后置条件。** 与级别 -1 的 `compress2` 相同。

</details>

## compressBound_z

```c
z_size_t ZEXPORT compressBound_z(z_size_t sourceLen);
```

计算为默认 zlib 压缩缓冲区确定容量所用的数值上界。

### 返回值与后续调用 {#api-compressbound_z-returns}

**返回值类型。** `z_size_t` — 饱和的压缩容量数值

计算默认压缩设置使用的容量数值，不分配缓冲区。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `min(2^64 - 1, n + (n >> 12) + (n >> 14) + (n >> 25) + 13)`<br>**容量数值** | n = sourceLen，可取任意 64 位无符号值；按数学整数求和，再饱和至最大值。n == 0 时返回 13。 | 将数值用于规划有效目的缓冲区容量。 |

**判读要点。**

- 这是数值契约，无错误返回。输出容量充分性是另一个性质，只限于默认的 zlib 封装、窗口和内存设置；它不涵盖任意的裸流或 gzip 设置。

### 调用条件与效果 {#api-compressbound_z-contract}

**定义域。** 完整类型定义域。

**前置条件。** 完整类型定义域：每个 64 位 `sourceLen`，包括零和最大值。

**效果。** 纯计算。没有指针访问、分配、状态变化或错误返回。

**范围。** 本契约规定数值。输出容量充分性是另一个性质，针对使用默认封装、
窗口和内存设置的有效压缩调用。它不为任意裸流或 gzip 流的设置给出上界。

**证明目标。**

- **目标。** `Goal.compressBound_z`（[Functional/Queries.lean](../../../ZlibF/Spec/Functional/Queries.lean)）；必需。它是这个函数的完整契约，同时充当它的安全目标；安全目标没有另行陈述。定理：`ZlibF.Spec.Public.Proofs.compressBound_z`（[public-compress-bound.lean](../../../ZlibF/Proof/public-compress-bound.lean)）。
- **适用条件。** 始终适用：命题没有前提。
- **无条件覆盖。** 每一个 `sourceLen`。
- **保证。**
    - *返回。* 翻译是一个从参数到结果的全函数。它不接受堆，也没有故障分支，所以调用对每个参数都返回；本目标另外说明结果是后置条件中给出的饱和公式。
    - *状态、写入、分配。* 都没有：这个函数不访问内存。
- **不在本目标内。** 这么大的目的缓冲区对 `compress` 是否足够：没有必需目标陈述这一点。

<details markdown="1" class="ar-return-exact" data-return-exact="compressBound_z"><summary>完整返回条件与边界</summary>

**后置条件。** 对 `n = sourceLen`，返回
`min(2^64 - 1, n + (n >> 12) + (n >> 14) + (n >> 25) + 13)`，其中和按数学整数解释。
零得到 13；和溢出时得到最大值。

</details>

## compressBound

```c
uLong ZEXPORT compressBound(uLong sourceLen);
```

数值上界的 `uLong` 形式。

### 返回值与后续调用 {#api-compressbound-returns}

**返回值类型。** `uLong` — 饱和的压缩容量数值

计算默认压缩设置使用的容量数值，不分配缓冲区。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `min(2^64 - 1, n + (n >> 12) + (n >> 14) + (n >> 25) + 13)`<br>**容量数值** | n = sourceLen，可取任意 64 位无符号值；按数学整数求和，再饱和至最大值。n == 0 时返回 13。 | 将数值用于规划有效目的缓冲区容量。 |

**判读要点。**

- 这是数值契约，无错误返回。输出容量充分性是另一个性质，只限于默认的 zlib 封装、窗口和内存设置；它不涵盖任意的裸流或 gzip 设置。

### 调用条件与效果 {#api-compressbound-contract}

**定义域。** 完整类型定义域。

**前置条件。** 完整类型定义域：每个 64 位 `sourceLen`。

**效果。** 纯计算。没有内存访问或错误返回。输出容量充分性的范围也相同。

**证明目标。**

- **目标。** `Goal.compressBound`（[Functional/Queries.lean](../../../ZlibF/Spec/Functional/Queries.lean)）；必需。它是这个函数的完整契约，同时充当它的安全目标；安全目标没有另行陈述。定理：`ZlibF.Spec.Public.Proofs.compressBound`（[public-compress-bound.lean](../../../ZlibF/Proof/public-compress-bound.lean)）。
- **适用条件。** 始终适用：命题没有前提。
- **无条件覆盖。** 每一个 `sourceLen`。
- **保证。**
    - *返回。* 翻译是一个从参数到结果的全函数。它不接受堆，也没有故障分支，所以调用对每个参数都返回；本目标另外说明结果是后置条件中给出的饱和公式。
    - *状态、写入、分配。* 都没有：这个函数不访问内存。
- **不在本目标内。** 这么大的目的缓冲区对 `compress` 是否足够：没有必需目标陈述这一点。

<details markdown="1" class="ar-return-exact" data-return-exact="compressBound"><summary>完整返回条件与边界</summary>

**后置条件。** 此构建下，公式与饱和规则和 [compressBound_z](#compressbound_z) 相同。

</details>

## uncompress2_z

```c
int ZEXPORT uncompress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t *sourceLen);
```

解码第一个 zlib 流，并报告输出大小和输入消费量。

### 返回值与后续调用 {#api-uncompress2_z-returns}

**返回值类型。** `int` — zlib 状态码；计数由长度参数报告

状态码说明第一个 zlib 流是否完整解码。长度值报告输出及输入消费量。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**完整解码完成** | 第一个 zlib 流已完整解码且校验通过；`*destLen` 报告已写字节数，`*sourceLen` 报告已消费字节数。尾随输入未使用。 | 使用恰好 `*destLen` 字节的输出。可根据 `*sourceLen` 定位未使用的输入。 |
| `Z_BUF_ERROR`<br>**输出已满且仍有输入** | 输出填满容量且仍有输入；`*destLen` 报告已写字节数，`*sourceLen` 报告已消费字节数。已写输出保持可用。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目的缓冲区容量，并把 `*sourceLen` 重新设为原始输入的完整长度。若需完整结果，扩大目的缓冲区容量并从原始输入重新调用；该工具不返回可续用的流。 |
| `Z_DATA_ERROR`<br>**数据、输入完整性或字典错误** | 输入畸形或不完整，或需要预置字典；裸流、gzip 输入也在错误范围内。成功初始化后的空输入亦为数据错误。解码器在无剩余输入时返回的 Z_BUF_ERROR 也映射为此码。 | 不要把部分输出视为已校验的完整结果；检查格式、输入完整性及字典需求，改用合适的调用。 |
| `Z_MEM_ERROR`<br>**初始化分配失败** | 初始化失败；现有长度值均不变，未写入输出。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目的缓冲区容量，并把 `*sourceLen` 重新设为原始输入的完整长度。资源允许时可从原输入重新发起完整调用，并重新提供容量。 |
| `Z_MEM_ERROR`<br>**解码期间分配失败** | 成功初始化后分配失败，可能已有部分输出；`*destLen` 报告已写字节数，`*sourceLen` 报告已消费字节数。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目的缓冲区容量，并把 `*sourceLen` 重新设为原始输入的完整长度。保留需要的已写字节；它们不是已完整校验的结果。新调用须从原输入开始并重新设置容量。 |
| `Z_STREAM_ERROR`<br>**初始化前参数拒绝** | 非空输入的 NULL source，或正容量的 NULL dest，或 NULL destLen 或 NULL sourceLen，会在初始化前被拒绝；现有长度值均不变。 | 修正已拒绝的参数，再重新调用。 |

**判读要点。**

- 成功初始化后，每次返回都写入实际计数，包括后续内存失败；已写输出仍可读取。每条返回路径均释放所有内部分配。
- 长度指针可以为 NULL，此时调用经检查后拒绝；非 NULL 的单元须可读写。
- 输入、目的缓冲区及长度单元互相分离。NULL 目的缓冲区配合零容量可使用私有输出指针接受完整空流。内部 Z_STREAM_END 映射为 Z_OK，Z_NEED_DICT 映射为 Z_DATA_ERROR，其他解码器返回码保留。

### 调用条件与效果 {#api-uncompress2_z-contract}

**定义域。** 受限定义域。

**前置条件。** 上述受限缓冲区定义域。`*sourceLen` 是可用输入量，`*destLen` 是输出容量。
任一长度指针都可在经检查的拒绝情形中为 NULL。
数据指针仅可在对应长度为零，或经检查的拒绝情形中为 NULL。
畸形、截断、裸流、gzip 和依赖字典的输入也在定义域内，属于错误情形。

**效果。** 有状态；适用通用效果。参数检查先于初始化：NULL `sourceLen`、
非空输入的 NULL 源、NULL `destLen`，或正容量的 NULL 目的缓冲区，返回 `Z_STREAM_ERROR`，
并保持两个已有长度单元不变。初始化失败也保持两个长度不变，且不写输出。
初始化后，每次返回都会在 `*sourceLen` 存储已消费字节数，在 `*destLen` 存储已产生
字节数，包括后续内存失败。此前写入的输出仍可用。

**证明目标。**

- **目标。** `Goal.uncompress2_z_safe`（[Safety/Utilities.lean](../../../ZlibF/Spec/Safety/Utilities.lean)；其命题是 [Public/Utilities.lean](../../../ZlibF/Spec/Public/Utilities.lean) 中的 `UncompressCountedSafe`）；必需。定理：`ZlibF.Spec.Public.Proofs.Uncompress.uncompress2_z_safe`（[public-uncompress-safe.lean](../../../ZlibF/Proof/public-uncompress-safe.lean)）。
- **适用条件**（`UncompressCountedSafe`）：
    1. 堆是库堆（`Fresh`、`Uniq`、`LibraryGlobals`）；
    2. 平台大小上界成立（`ByteObjectsFit`）；
    3. 非 NULL 的 `destLen` 指向一个可读可写的 8 字节单元，非 NULL 的 `sourceLen` 也是如此（`LengthCell`）；
    4. 非 NULL 的 `source` 指向 `*sourceLen` 个可读字节；
    5. 非 NULL 的 `dest` 指向 `*destLen` 个可写字节；
    6. `dest` 范围、`source` 范围和两个长度单元两两不重叠（`UtilitySeparation`）。
- **无条件覆盖。** `destLen` 或 `sourceLen` 为 NULL（调用会拒绝）；源字节的每一种内容：有效的 zlib 流、被截断或畸形的流、裸流或 gzip 数据；每一种分配结果。内存条件与前置条件相同。
- **保证。**
    - *返回。* 调用返回。如果 `sourceLen` 或 `destLen` 为 NULL、`source` 为 NULL 而 `*sourceLen` 非零，或 `dest` 为 NULL 而 `*destLen` 非零，返回值是 `Z_STREAM_ERROR`。否则返回值是 `Z_OK`、`Z_BUF_ERROR`、`Z_DATA_ERROR` 或 `Z_MEM_ERROR`，并且只有在某次分配确实失败之后才返回 `Z_MEM_ERROR`（`AllocationFailed`）。
    - *状态。* 不保留任何状态：调用结束后，它用过的流、状态和窗口都不存在。
    - *写入。* 因上述参数返回 `Z_STREAM_ERROR` 时，不写任何内容。其他情况下只写：`dest` 处的字节，至多为进入时给出的 `*destLen` 个；`*sourceLen`，写入一个不超过其进入值的计数；以及 `*destLen`，写入已写出的字节数。返回 `Z_MEM_ERROR` 时，也可能一个字节都没写，两个单元都保持进入时的值。其他对象都不变（`Store`、`SameObjectsUpToTableShape`）。
    - *分配。* 调用分配的每个块都在返回之前释放，每条路径都是如此：已分配的块与调用前相同。
- **不在本目标内。** 长度单元与缓冲区或另一个长度单元重叠，以及 `source` 与 `dest` 重叠：在所有目标之外（见[偏离记录](../../deviations.md)中“计数解压”一行）。哪种输入返回哪个状态码，以及写出的字节：功能目标 `Goal.uncompress2_z`，安全结论不需要它。

<details markdown="1" class="ar-return-exact" data-return-exact="uncompress2_z"><summary>完整返回条件与边界</summary>

**后置条件。** `Z_OK` 表示完整且通过检查的 zlib 流被解码到输出。
尾随输入未使用。`Z_BUF_ERROR` 表示输出已填满容量，且仍有输入。
`Z_DATA_ERROR` 包括畸形或不完整输入，以及需要预置字典的情形。
`Z_MEM_ERROR` 表示分配失败，且可能发生在部分输出之后。

**边缘情形。** NULL 目的缓冲区配合零容量时，使用私有输出指针，因而可以接受；
完整空流可以成功。空输入在成功初始化后是数据错误。
最终精确映射为：`Z_STREAM_END` 到 `Z_OK`，`Z_NEED_DICT` 到 `Z_DATA_ERROR`，
无剩余输入时 `Z_BUF_ERROR` 到 `Z_DATA_ERROR`。其他解码器返回码保留。

</details>

## uncompress2

```c
int ZEXPORT uncompress2(Bytef *dest, uLongf *destLen, const Bytef *source, uLong *sourceLen);
```

报告输入消费量的 `uLong` 解码条目。

### 返回值与后续调用 {#api-uncompress2-returns}

**返回值类型。** `int` — zlib 状态码；计数由长度参数报告

状态码说明第一个 zlib 流是否完整解码。长度值报告输出及输入消费量。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**完整解码完成** | 第一个 zlib 流已完整解码且校验通过；`*destLen` 报告已写字节数，`*sourceLen` 报告已消费字节数。尾随输入未使用。 | 使用恰好 `*destLen` 字节的输出。可根据 `*sourceLen` 定位未使用的输入。 |
| `Z_BUF_ERROR`<br>**输出已满且仍有输入** | 输出填满容量且仍有输入；`*destLen` 报告已写字节数，`*sourceLen` 报告已消费字节数。已写输出保持可用。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目的缓冲区容量，并把 `*sourceLen` 重新设为原始输入的完整长度。若需完整结果，扩大目的缓冲区容量并从原始输入重新调用；该工具不返回可续用的流。 |
| `Z_DATA_ERROR`<br>**数据、输入完整性或字典错误** | 输入畸形或不完整，或需要预置字典；裸流、gzip 输入也在错误范围内。成功初始化后的空输入亦为数据错误。解码器在无剩余输入时返回的 Z_BUF_ERROR 也映射为此码。 | 不要把部分输出视为已校验的完整结果；检查格式、输入完整性及字典需求，改用合适的调用。 |
| `Z_MEM_ERROR`<br>**初始化分配失败** | 初始化失败；现有长度值均不变，未写入输出。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目的缓冲区容量，并把 `*sourceLen` 重新设为原始输入的完整长度。资源允许时可从原输入重新发起完整调用，并重新提供容量。 |
| `Z_MEM_ERROR`<br>**解码期间分配失败** | 成功初始化后分配失败，可能已有部分输出；`*destLen` 报告已写字节数，`*sourceLen` 报告已消费字节数。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目的缓冲区容量，并把 `*sourceLen` 重新设为原始输入的完整长度。保留需要的已写字节；它们不是已完整校验的结果。新调用须从原输入开始并重新设置容量。 |
| `Z_STREAM_ERROR`<br>**初始化前参数拒绝** | 非空输入的 NULL source，或正容量的 NULL dest，会在初始化前被拒绝；现有长度值均不变。 | 修正已拒绝的参数，再重新调用。 |

**判读要点。**

- 成功初始化后，每次返回都写入实际计数，包括后续内存失败；已写输出仍可读取。每条返回路径均释放所有内部分配。
- 普通适配器会先读取长度单元：destLen 和 sourceLen 均须非 NULL。两者每次返回都会写回。
- 输入、目的缓冲区及长度单元互相分离。NULL 目的缓冲区配合零容量可使用私有输出指针接受完整空流。内部 Z_STREAM_END 映射为 Z_OK，Z_NEED_DICT 映射为 Z_DATA_ERROR，其他解码器返回码保留。

### 调用条件与效果 {#api-uncompress2-contract}

**定义域。** 受限定义域。

**前置条件。** [uncompress2_z](#uncompress2_z) 的受限定义域，且两个长度单元均非 NULL，
因为包装函数会在 `_z` 检查前读取它们。

**效果。** 有状态；输出效果和清理效果与 `uncompress2_z` 相同。每次返回都写回两个长度，包括错误返回。
参数拒绝和初始化失败保持这两个长度的值不变。

**证明目标。**

- **目标。** `Goal.uncompress2_safe`（[Safety/Utilities.lean](../../../ZlibF/Spec/Safety/Utilities.lean)；其命题是 [Public/Utilities.lean](../../../ZlibF/Spec/Public/Utilities.lean) 中的 `UncompressCountedSafe`）；必需。定理：`ZlibF.Spec.Public.Proofs.Uncompress.uncompress2_safe`（[public-uncompress-safe.lean](../../../ZlibF/Proof/public-uncompress-safe.lean)）。
- **适用条件**（`UncompressCountedSafe`）：
    1. 堆是库堆（`Fresh`、`Uniq`、`LibraryGlobals`）；
    2. 平台大小上界成立（`ByteObjectsFit`）；
    3. 非 NULL 的 `destLen` 指向一个可读可写的 8 字节单元，非 NULL 的 `sourceLen` 也是如此（`LengthCell`）；
    4. `destLen` 和 `sourceLen` 不为 NULL；
    5. 非 NULL 的 `source` 指向 `*sourceLen` 个可读字节；
    6. 非 NULL 的 `dest` 指向 `*destLen` 个可写字节；
    7. `dest` 范围、`source` 范围和两个长度单元两两不重叠（`UtilitySeparation`）。
- **无条件覆盖。** 源字节的每一种内容：有效的 zlib 流、被截断或畸形的流、裸流或 gzip 数据；每一种分配结果。内存条件与前置条件相同。
- **保证。**
    - *返回。* 调用返回。如果 `source` 为 NULL 而 `*sourceLen` 非零，或 `dest` 为 NULL 而 `*destLen` 非零，返回值是 `Z_STREAM_ERROR`。否则返回值是 `Z_OK`、`Z_BUF_ERROR`、`Z_DATA_ERROR` 或 `Z_MEM_ERROR`，并且只有在某次分配确实失败之后才返回 `Z_MEM_ERROR`（`AllocationFailed`）。
    - *状态。* 不保留任何状态：调用结束后，它用过的流、状态和窗口都不存在。
    - *写入。* 因上述参数返回 `Z_STREAM_ERROR` 时，不写任何内容。其他情况下只写：`dest` 处的字节，至多为进入时给出的 `*destLen` 个；`*sourceLen`，写入一个不超过其进入值的计数；以及 `*destLen`，写入已写出的字节数。返回 `Z_MEM_ERROR` 时，也可能一个字节都没写，两个单元都保持进入时的值。其他对象都不变（`Store`、`SameObjectsUpToTableShape`）。
    - *分配。* 调用分配的每个块都在返回之前释放，每条路径都是如此：已分配的块与调用前相同。
- **不在本目标内。** 长度单元与缓冲区或另一个长度单元重叠，以及 `source` 与 `dest` 重叠：在所有目标之外（见[偏离记录](../../deviations.md)中“计数解压”一行）。哪种输入返回哪个状态码，以及写出的字节：功能目标 `Goal.uncompress2`，安全结论不需要它。

<details markdown="1" class="ar-return-exact" data-return-exact="uncompress2"><summary>完整返回条件与边界</summary>

**后置条件。** 解码、返回码和已消费计数与 `uncompress2_z` 相同。

</details>

## uncompress_z

```c
int ZEXPORT uncompress_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t sourceLen);
```

解码，但不公开已消费输入计数。

### 返回值与后续调用 {#api-uncompress_z-returns}

**返回值类型。** `int` — zlib 状态码；计数由长度参数报告

状态码说明第一个 zlib 流是否完整解码。长度值报告输出，不报告输入消费量。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**完整解码完成** | 第一个 zlib 流已完整解码且校验通过；`*destLen` 报告已写字节数；已消费输入计数不向调用者公开。尾随输入未使用。 | 使用恰好 `*destLen` 字节的输出。此条目没有计数可用来定位尾随输入。 |
| `Z_BUF_ERROR`<br>**输出已满且仍有输入** | 输出填满容量且仍有输入；`*destLen` 报告已写字节数；已消费输入计数不向调用者公开。已写输出保持可用。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目的缓冲区容量。若需完整结果，扩大目的缓冲区容量并从原始输入重新调用；该工具不返回可续用的流。 |
| `Z_DATA_ERROR`<br>**数据、输入完整性或字典错误** | 输入畸形或不完整，或需要预置字典；裸流、gzip 输入也在错误范围内。成功初始化后的空输入亦为数据错误。解码器在无剩余输入时返回的 Z_BUF_ERROR 也映射为此码。 | 不要把部分输出视为已校验的完整结果；检查格式、输入完整性及字典需求，改用合适的调用。 |
| `Z_MEM_ERROR`<br>**初始化分配失败** | 初始化失败；现有长度值均不变，未写入输出。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目的缓冲区容量。资源允许时可从原输入重新发起完整调用，并重新提供容量。 |
| `Z_MEM_ERROR`<br>**解码期间分配失败** | 成功初始化后分配失败，可能已有部分输出；`*destLen` 报告已写字节数；已消费输入计数不向调用者公开。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目的缓冲区容量。保留需要的已写字节；它们不是已完整校验的结果。新调用须从原输入开始并重新设置容量。 |
| `Z_STREAM_ERROR`<br>**初始化前参数拒绝** | 非空输入的 NULL source，或正容量的 NULL dest，或 NULL destLen，会在初始化前被拒绝；现有长度值均不变。 | 修正已拒绝的参数，再重新调用。 |

**判读要点。**

- 成功初始化后，每次返回都写入实际计数，包括后续内存失败；已写输出仍可读取。每条返回路径均释放所有内部分配。
- `destLen` 可以为 NULL，此时调用经检查后拒绝；非 NULL 的单元须可读写。
- 输入、目的缓冲区及长度单元互相分离。NULL 目的缓冲区配合零容量可使用私有输出指针接受完整空流。内部 Z_STREAM_END 映射为 Z_OK，Z_NEED_DICT 映射为 Z_DATA_ERROR，其他解码器返回码保留。

### 调用条件与效果 {#api-uncompress_z-contract}

**定义域。** 受限定义域。

**前置条件。** [uncompress2_z](#uncompress2_z) 的受限定义域；`sourceLen` 按值传递。
`destLen` 可在经检查的拒绝情形中为 NULL。

**效果。** 有状态；输出长度的写入和完整清理均与 `uncompress2_z` 相同。已消费计数为局部值。

**证明目标。**

- **目标。** `Goal.uncompress_z_safe`（[Safety/Utilities.lean](../../../ZlibF/Spec/Safety/Utilities.lean)；其命题是 [Public/Utilities.lean](../../../ZlibF/Spec/Public/Utilities.lean) 中的 `UncompressSingleSafe`）；必需。定理：`ZlibF.Spec.Public.Proofs.Uncompress.uncompress_z_safe`（[public-uncompress-safe.lean](../../../ZlibF/Proof/public-uncompress-safe.lean)）。
- **适用条件**（`UncompressSingleSafe`）：
    1. 堆是库堆（`Fresh`、`Uniq`、`LibraryGlobals`）；
    2. 平台大小上界成立（`ByteObjectsFit`）；
    3. 非 NULL 的 `destLen` 指向一个可读可写的 8 字节单元（`LengthCell`）；
    4. 非 NULL 的 `source` 指向 `sourceLen` 个可读字节；
    5. 非 NULL 的 `dest` 指向 `*destLen` 个可写字节；
    6. `dest` 范围、`source` 范围和长度单元两两不重叠（`Separate`）。
- **无条件覆盖。** `destLen` 为 NULL（调用会拒绝）；源字节的每一种内容：有效的 zlib 流、被截断或畸形的流、裸流或 gzip 数据；每一种分配结果。内存条件与前置条件相同。
- **保证。**
    - *返回。* 调用返回。如果 `destLen` 为 NULL、`source` 为 NULL 而 `sourceLen` 非零，或 `dest` 为 NULL 而 `*destLen` 非零，返回值是 `Z_STREAM_ERROR`。否则返回值是 `Z_OK`、`Z_BUF_ERROR`、`Z_DATA_ERROR` 或 `Z_MEM_ERROR`，并且只有在某次分配确实失败之后才返回 `Z_MEM_ERROR`（`AllocationFailed`）。
    - *状态。* 不保留任何状态：调用结束后，它用过的流、状态和窗口都不存在。
    - *写入。* 因上述参数返回 `Z_STREAM_ERROR` 时，不写任何内容。其他情况下只写：`dest` 处的字节，至多为进入时给出的 `*destLen` 个；以及 `*destLen`，写入已写出的字节数。返回 `Z_MEM_ERROR` 时，也可能一个字节都没写，该单元保持进入时的值。其他对象都不变（`Store`、`SameObjectsUpToTableShape`）。
    - *分配。* 调用分配的每个块都在返回之前释放，每条路径都是如此：已分配的块与调用前相同。
- **不在本目标内。** 长度单元与缓冲区重叠，以及 `source` 与 `dest` 重叠：在所有目标之外（见[偏离记录](../../deviations.md)中“计数解压”一行）。哪种输入返回哪个状态码，以及写出的字节：功能目标 `Goal.uncompress_z`，安全结论不需要它。

<details markdown="1" class="ar-return-exact" data-return-exact="uncompress_z"><summary>完整返回条件与边界</summary>

**后置条件。** 输出和返回码与 `uncompress2_z` 相同。
忽略尾随字节；调用者得不到用于定位它们的计数。

</details>

## uncompress

```c
int ZEXPORT uncompress(Bytef *dest, uLongf *destLen, const Bytef *source, uLong sourceLen);
```

不报告已消费输入计数的 `uLong` 解码条目。

### 返回值与后续调用 {#api-uncompress-returns}

**返回值类型。** `int` — zlib 状态码；计数由长度参数报告

状态码说明第一个 zlib 流是否完整解码。长度值报告输出，不报告输入消费量。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**完整解码完成** | 第一个 zlib 流已完整解码且校验通过；`*destLen` 报告已写字节数；已消费输入计数不向调用者公开。尾随输入未使用。 | 使用恰好 `*destLen` 字节的输出。此条目没有计数可用来定位尾随输入。 |
| `Z_BUF_ERROR`<br>**输出已满且仍有输入** | 输出填满容量且仍有输入；`*destLen` 报告已写字节数；已消费输入计数不向调用者公开。已写输出保持可用。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目的缓冲区容量。若需完整结果，扩大目的缓冲区容量并从原始输入重新调用；该工具不返回可续用的流。 |
| `Z_DATA_ERROR`<br>**数据、输入完整性或字典错误** | 输入畸形或不完整，或需要预置字典；裸流、gzip 输入也在错误范围内。成功初始化后的空输入亦为数据错误。解码器在无剩余输入时返回的 Z_BUF_ERROR 也映射为此码。 | 不要把部分输出视为已校验的完整结果；检查格式、输入完整性及字典需求，改用合适的调用。 |
| `Z_MEM_ERROR`<br>**初始化分配失败** | 初始化失败；现有长度值均不变，未写入输出。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目的缓冲区容量。资源允许时可从原输入重新发起完整调用，并重新提供容量。 |
| `Z_MEM_ERROR`<br>**解码期间分配失败** | 成功初始化后分配失败，可能已有部分输出；`*destLen` 报告已写字节数；已消费输入计数不向调用者公开。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目的缓冲区容量。保留需要的已写字节；它们不是已完整校验的结果。新调用须从原输入开始并重新设置容量。 |
| `Z_STREAM_ERROR`<br>**初始化前参数拒绝** | 非空输入的 NULL source，或正容量的 NULL dest，会在初始化前被拒绝；现有长度值均不变。 | 修正已拒绝的参数，再重新调用。 |

**判读要点。**

- 成功初始化后，每次返回都写入实际计数，包括后续内存失败；已写输出仍可读取。每条返回路径均释放所有内部分配。
- 普通适配器会先读取长度单元：destLen 须非 NULL，且每次返回都会写回。
- 输入、目的缓冲区及长度单元互相分离。NULL 目的缓冲区配合零容量可使用私有输出指针接受完整空流。内部 Z_STREAM_END 映射为 Z_OK，Z_NEED_DICT 映射为 Z_DATA_ERROR，其他解码器返回码保留。

### 调用条件与效果 {#api-uncompress-contract}

**定义域。** 受限定义域。

**前置条件。** [uncompress2](#uncompress2) 的受限缓冲区定义域，且 `destLen` 非 NULL。

**效果。** 有状态；输出长度的写入、部分输出的保留和完整清理均与 `uncompress2` 相同。

**证明目标。**

- **目标。** `Goal.uncompress_safe`（[Safety/Utilities.lean](../../../ZlibF/Spec/Safety/Utilities.lean)；其命题是 [Public/Utilities.lean](../../../ZlibF/Spec/Public/Utilities.lean) 中的 `UncompressSingleSafe`）；必需。定理：`ZlibF.Spec.Public.Proofs.Uncompress.uncompress_safe`（[public-uncompress-safe.lean](../../../ZlibF/Proof/public-uncompress-safe.lean)）。
- **适用条件**（`UncompressSingleSafe`）：
    1. 堆是库堆（`Fresh`、`Uniq`、`LibraryGlobals`）；
    2. 平台大小上界成立（`ByteObjectsFit`）；
    3. 非 NULL 的 `destLen` 指向一个可读可写的 8 字节单元（`LengthCell`）；
    4. `destLen` 不为 NULL；
    5. 非 NULL 的 `source` 指向 `sourceLen` 个可读字节；
    6. 非 NULL 的 `dest` 指向 `*destLen` 个可写字节；
    7. `dest` 范围、`source` 范围和长度单元两两不重叠（`Separate`）。
- **无条件覆盖。** 源字节的每一种内容：有效的 zlib 流、被截断或畸形的流、裸流或 gzip 数据；每一种分配结果。内存条件与前置条件相同。
- **保证。**
    - *返回。* 调用返回。如果 `source` 为 NULL 而 `sourceLen` 非零，或 `dest` 为 NULL 而 `*destLen` 非零，返回值是 `Z_STREAM_ERROR`。否则返回值是 `Z_OK`、`Z_BUF_ERROR`、`Z_DATA_ERROR` 或 `Z_MEM_ERROR`，并且只有在某次分配确实失败之后才返回 `Z_MEM_ERROR`（`AllocationFailed`）。
    - *状态。* 不保留任何状态：调用结束后，它用过的流、状态和窗口都不存在。
    - *写入。* 因上述参数返回 `Z_STREAM_ERROR` 时，不写任何内容。其他情况下只写：`dest` 处的字节，至多为进入时给出的 `*destLen` 个；以及 `*destLen`，写入已写出的字节数。返回 `Z_MEM_ERROR` 时，也可能一个字节都没写，该单元保持进入时的值。其他对象都不变（`Store`、`SameObjectsUpToTableShape`）。
    - *分配。* 调用分配的每个块都在返回之前释放，每条路径都是如此：已分配的块与调用前相同。
- **不在本目标内。** 长度单元与缓冲区重叠，以及 `source` 与 `dest` 重叠：在所有目标之外（见[偏离记录](../../deviations.md)中“计数解压”一行）。哪种输入返回哪个状态码，以及写出的字节：功能目标 `Goal.uncompress`，安全结论不需要它。

<details markdown="1" class="ar-return-exact" data-return-exact="uncompress"><summary>完整返回条件与边界</summary>

**后置条件。** 输出和返回码与 `uncompress2` 相同；忽略尾随输入。

</details>

## zlibVersion

```c
const char * ZEXPORT zlibVersion(void);
```

返回已链接库的发布版本字符串。

### 返回值与后续调用 {#api-zlibversion-returns}

**返回值类型。** `const char *` — 借用的不可变版本字符串指针

返回已链接库的版本字符串。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `ZLIB_VERSION`<br>**库版本字符串** | 无参数；返回非 NULL、以 NUL 结尾的字符串，在固定的源码中是 `1.4`。 | 读取此静态字符串；不得写入或释放。 |

### 调用条件与效果 {#api-zlibversion-contract}

**定义域。** 完整类型定义域。

**前置条件。** 完整类型定义域；不需要参数或调用者状态。

**效果。** 只读。结果是借用的不可变静态存储；调用者不得写入或释放。
不发生分配或堆变化。

**证明目标。**

- **目标。** `Goal.zlibVersion_safety`（[Safety/Queries.lean](../../../ZlibF/Spec/Safety/Queries.lean)）；必需。定理：`ZlibF.Spec.Public.StatelessSafetyProof.zlibVersion_safety`（[public-stateless-safety.lean](../../../ZlibF/Proof/public-stateless-safety.lean)）。
- **适用条件。** 始终适用：命题没有前提。
- **无条件覆盖。** 每一个堆，包括不是库堆的堆。
- **保证。**
    - *返回。* 调用返回。
    - *状态、写入、分配。* 都没有：调用之后的堆就是调用之前的堆。
- **不在本目标内。** 结果所指向的字符串：功能目标 `Goal.zlibVersion`，安全结论不需要它。

<details markdown="1" class="ar-return-exact" data-return-exact="zlibVersion"><summary>完整返回条件与边界</summary>

**后置条件。** 返回非 NULL 指针，指向以 NUL 结尾的 `ZLIB_VERSION`（在固定的源码中是 `1.4`）。

</details>

## zlibCompileFlags

```c
uLong ZEXPORT zlibCompileFlags(void);
```

报告构建的类型大小和编译期选项。

### 返回值与后续调用 {#api-zlibcompileflags-returns}

**返回值类型。** `uLong` — 构建信息位字段

返回当前构建的类型大小与编译选项编码。此值不是状态码。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `169 (0xa9)`<br>**所选构建的标志** | 本构建的 uInt 为 4 字节，uLong、指针和 z_off_t 为 8 字节；其他标志为零。 | 按位字段读取构建信息；双位大小字段以 0、1、2、3 分别编码 2、4、8、其他字节数。 |

### 调用条件与效果 {#api-zlibcompileflags-contract}

**定义域。** 完整类型定义域。

**前置条件。** 完整类型定义域；不需要参数或调用者状态。

**效果。** 纯标量查询。没有分配、内存写入或错误返回。

**证明目标。**

- **目标。** `Goal.zlibCompileFlags_safety`（[Safety/Queries.lean](../../../ZlibF/Spec/Safety/Queries.lean)）；必需。定理：`ZlibF.Spec.Public.StatelessSafetyProof.zlibCompileFlags_safety`（[public-stateless-safety.lean](../../../ZlibF/Proof/public-stateless-safety.lean)）。
- **适用条件。** 始终适用：命题没有前提。
- **无条件覆盖。** 每一个堆，包括不是库堆的堆。
- **保证。**
    - *返回。* 调用返回。
    - *状态、写入、分配。* 都没有：调用之后的堆就是调用之前的堆。
- **不在本目标内。** 返回的值：功能目标 `Goal.zlibCompileFlags`，安全结论不需要它。

<details markdown="1" class="ar-return-exact" data-return-exact="zlibCompileFlags"><summary>完整返回条件与边界</summary>

**后置条件。** 此构建返回 169（`0xa9`）：`uInt` 为 4 字节；`uLong`、指针和
`z_off_t` 为 8 字节。相应的双位字段将大小 2、4、8 和其他分别编码为 0、1、2 和 3。
所选构建的其他标志为零。

</details>

## zError

```c
const char * ZEXPORT zError(int err);
```

返回 zlib 结果码对应的文本。

### 返回值与后续调用 {#api-zerror-returns}

**返回值类型。** `const char *` — 借用的不可变错误文本指针

把传入的结果码映射为文本。函数本身总是返回非 NULL 字符串指针。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `"need dictionary"`<br>**需要字典文本** | err == 2。 | 读取借用的静态文本；不得写入或释放。 |
| `"stream end"`<br>**流结束文本** | err == 1。 | 读取借用的静态文本；不得写入或释放。 |
| `"file error"`<br>**文件错误文本** | err == -1。 | 读取借用的静态文本；不得写入或释放。 |
| `"stream error"`<br>**流错误文本** | err == -2。 | 读取借用的静态文本；不得写入或释放。 |
| `"data error"`<br>**数据错误文本** | err == -3。 | 读取借用的静态文本；不得写入或释放。 |
| `"insufficient memory"`<br>**内存不足文本** | err == -4。 | 读取借用的静态文本；不得写入或释放。 |
| `"buffer error"`<br>**缓冲区错误文本** | err == -5。 | 读取借用的静态文本；不得写入或释放。 |
| `"incompatible version"`<br>**版本不兼容文本** | err == -6。 | 读取借用的静态文本；不得写入或释放。 |
| `""`<br>**空文本** | err == 0，或 err 不在 -6–2 范围内，包括 int 的最小值和最大值。 | 按需读取空字符串；这既不是 NULL 指针，也不是另一个错误码。 |

**判读要点。**

- 接受每一个 int 值；在索引运算前检查范围。不分配内存，也不改变堆。

### 调用条件与效果 {#api-zerror-contract}

**定义域。** 完整类型定义域。

**前置条件。** 完整类型定义域：每个 `int`，包括最小和最大值。

**效果。** 只读。结果是借用的不可变静态存储；不得写入或释放。
没有分配、堆变化或错误返回。索引计算前会检查 -6–2 范围外的值，
因此两个标量极值均安全返回空文本。

**证明目标。** 没有必需目标：`zlib.h` 把这个函数声明在“`undocumented functions (not part of the zlib API)`”（未文档化的函数，不属于 zlib API）之下。为它陈述了一个目标（非必需）：`Goal.zError`（[Functional/Queries.lean](../../../ZlibF/Spec/Functional/Queries.lean)），定理为 `ZlibF.Spec.Public.Proofs.zError`（[public-zerror.lean](../../../ZlibF/Proof/public-zerror.lean)）。对每一个堆和每一个 `err`，它陈述：调用返回，堆不变，结果是后置条件所述的静态文本。

<details markdown="1" class="ar-return-exact" data-return-exact="zError"><summary>完整返回条件与边界</summary>

**后置条件。** 返回非 NULL 指针，指向下列以 NUL 结尾的文本。

| `err` | 文本 |
| --- | --- |
| 2 | `need dictionary` |
| 1 | `stream end` |
| -1 | `file error` |
| -2 | `stream error` |
| -3 | `data error` |
| -4 | `insufficient memory` |
| -5 | `buffer error` |
| -6 | `incompatible version` |
| 0 或任意其他值 | 空字符串 |

</details>

[返回 API 手册](README.md) · [契约约定](contracts.md)

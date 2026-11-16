<!-- source-sha256: c8eebcdb8185d2de4b3035e2f1fb2df87455aad8dd8f98efe28ed6376dbe53f6 -->

# 流式压缩

[API 手册](README.md) · [共享流规则](streams.md) · [流式解压](inflate-stream.md)

输入分批到达、输出空间有限，或需要选择封装、字典、刷新边界时，使用 `z_stream` 压缩器。封装是在 DEFLATE 压缩数据之外增加的头部、尾部和完整性信息；裸 DEFLATE 则不带这些封装。初始化一次，使用连续的缓冲区调用 `deflate`，即使放弃压缩也要结束流。单个缓冲区的操作见 [compress 和 compress2](utility.md#compress2_z)。

| 任务 | 条目 |
| --- | --- |
| 开始或复用 | [初始化](#deflateinit_)、[配置初始化](#deflateinit2_)、[重置](#deflatereset)、[保留历史的重置](#deflateresetkeep) |
| 提供元数据或历史 | [字典](#deflatesetdictionary)、[读取历史](#deflategetdictionary)、[gzip 头](#deflatesetheader) |
| 压缩与输出大小 | [压缩](#deflate)、[上界](#deflatebound_z)、[待输出数据](#deflatepending)、[最近刷新位数](#deflateused) |
| 调整或分支 | [参数](#deflateparams)、[调优](#deflatetune)、[位预置](#deflateprime)、[复制](#deflatecopy) |
| 释放存储 | [结束](#deflateend) |

这些契约遵循固定版本的 zlib 在应用各[补丁](../../../patches/README.md)之后的 `zlib.h` 和 `deflate.c`，采用默认 LP64 Linux 构建。六个补丁中只有补丁 0006 改动 `deflate.c`。它修改 `deflateBound_z` 中的一个条件，`deflateBound` 调用 `deflateBound_z`，其结果也随之改变；改动的内容见条目 [deflateBound_z](#deflatebound_z)。这个补丁不改动其他函数。这些是聚焦契约：前置条件描述通常的正确用法，有意比函数实际接受的范围窄。前置条件之外、C 仍会处理的情况，写在“错误”或**聚焦范围之外**下。超出前置条件的调用并不因此就是未定义行为，也不一定返回错误码。定义域和效果标签的含义见[契约约定](contracts.md)。

**已证明的内容。** 只证明安全性：每次调用都返回，没有未定义行为和内存错误，只写其目标指明的内容，并且不泄漏（见[安全性](../safety.md)）。各条目在“证明目标”下给出自己的目标，所用的五项和固定用语由[阅读证明目标段落](contracts.md#reading-a-proof-goals-paragraph)定义：目标及其定理；目标适用的条件，按 Lean 命题中的顺序列出；对每一个取值都覆盖的内容；保证的内容（返回、状态、写入、分配）；以及留给其他目标的内容。证明所假设的是那里列出的条件，而不是文档中的前置条件。后置条件、返回值表和各项说明描述的是功能行为：它们读自 C 源码，凡是没有定理陈述的，都**尚未由证明确认**；安全结论不需要它们。哪些目标已完成，见[进度](../../progress.md)。

## 共享约定

在每条所述前置条件下，文档描述的行为是：调用终止且不产生运行时故障，并且后置条件成立。调用之后流仍然存活时，它的表示不变量保持成立。其中已被证明的部分，就是该条目的安全目标。

先看一次调用的数据交接。`next_in` 指向尚未读取的输入的起点，`avail_in` 是从这里开始可读的字节数；`next_out` 指向下一个可写位置，`avail_out` 是剩余输出容量，也以字节计。一次调用可以只消耗部分输入、只交付部分输出。调用者应读取更新后的指针和计数，接走已交付字节，再为同一个流补充输入或输出空间。

- **存活流：** 可写的 `z_stream`，其压缩器状态由成功初始化或复制建立，经过合法调用保持，且尚未结束。调用者不改变其内部状态或分配器字段。同一个流的调用按顺序执行。
- **缓冲区：** 输入覆盖 `avail_in` 个可读字节；输出覆盖 `avail_out` 个可写字节。它们彼此不重叠，也不与流或流拥有的状态重叠。非 NULL 标量结果指向可写单元，与其他结果及流内存分离。这些分离条件是契约的假设。安全目标也假设其中某一条时，该条目的“证明目标”会写明，[偏离记录](../../deviations.md)中也有对应的一行。
- **分配器：** 使用默认分配/释放函数对，或在初始化前将两个字段都置为 NULL。任意一次分配尝试都可能失败。自定义分配器回调不在本页范围内。
- **帧性质与所有权：** 调用只改变自己的流、其拥有的状态和所述输出区域。调用者输入只读。调用者缓冲区和头部记录仍归调用者所有。只有初始化和复制会分配；只有它们失败时的清理与 `deflateEnd` 会释放内存。其他调用保持流的分配集合。
- **头部生命周期：** 保留的 gzip 头及其可选字段在使用期间保持可读且不变。非 NULL 的 `name` 和 `comment` 以零终止；`extra` 覆盖所述长度。本页的契约取 `extra_len <= 65535`。
- **检查后的拒绝：** 除初始化和上界查询外，流检查失败会在正常操作之前返回 `Z_STREAM_ERROR`，不发生写入。`deflateCopy` 还会清空非 NULL 目的流的状态。这种拒绝不修改查询输出单元。
- **受限定义域**指这些显式内存、生命周期和调用顺序条件，加上条目自身的前置条件。它不意味着接受每个可表示的指针或整数。错误概述覆盖各项检查读得到的流记录和状态，不覆盖任意无效地址。
- **可达流：** 证明目标里说的是可达流，契约里说的是存活流（见[契约约定](contracts.md)）。目标所覆盖的调用会延长流的历史：调用返回后，无论返回哪个状态码，流仍然是可达流，下一次调用的目标随之适用。`deflateEnd` 结束这段历史。
- **结果单元作为值：** `deflateGetDictionary`、`deflatePending` 和 `deflateUsed` 通过指针报告结果（`uInt *dictLength`、`unsigned *pending`、`int *bits`）。翻译没有把这些单元建模为内存：各函数只接收“指针是否为 NULL”这一事实，并把结果作为值返回。因此目标不涉及结果单元的地址，也无法表达结果单元与其他对象重叠的情况。

## deflateInit_

```c
int ZEXPORT deflateInit_(z_streamp strm, int level, const char *version, int stream_size);
```

使用默认 zlib 封装和压缩设置启动压缩器。

### 返回值与后续调用 {#api-deflateinit_-returns}

**返回值类型。** `int` — zlib 状态码

返回值区分压缩器已建立、兼容性拒绝、参数拒绝和分配失败。只有 Z_OK 建立需要结束的存活流。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**压缩器已建立** | 兼容性和参数有效，五项分配均成功；采用 zlib 封装、窗口 15、内存级别 8 和默认策略。 | 可以提供缓冲区并开始压缩；最后用 deflateEnd 释放，即使放弃任务。 |
| `Z_VERSION_ERROR`<br>**兼容性拒绝** | version 为 NULL、版本首字节不匹配，或 stream_size 不等于 sizeof(z_stream)。此检查先于 strm 检查，且不改变流。 | 修正版本和结构大小后再初始化；此结果没有建立待释放的新状态。 |
| `Z_STREAM_ERROR`<br>**流指针为 NULL** | 兼容性检查通过，但 strm 为 NULL。 | 提供符合初始化前置条件的可写流记录后再初始化。 |
| `Z_STREAM_ERROR`<br>**参数被拒绝** | level 不是 -1 或 0..9。拒绝发生于分配前，但 msg 已清空，并可能安装默认分配器、清空 opaque。 | 修正参数后按初始化的前置条件再调用；没有新分配需要结束。 |
| `Z_MEM_ERROR`<br>**状态分配失败** | 首项状态分配失败；state 保持进入时的值，没有新分配的块存活。 | 处理内存不足后可按初始化的前置条件重试；无需为此次失败调用 deflateEnd。 |
| `Z_MEM_ERROR`<br>**缓冲分配失败并已清理** | 状态分配成功后，四项缓冲分配全部尝试；任何失败都会释放所有新块，state 变为 NULL，msg 报告内存不足。 | 此调用已完成清理；处理内存不足后可重新初始化。 |

**判读要点。**

- 不消费输入、不写输出。级别 -1 选择 6。

### 调用条件与效果 {#api-deflateinit_-contract}

**定义域：** 受限定义域。**效果：** 分配并初始化。

**前置条件：** `strm` 可写，且不拥有存活的压缩器状态。其分配器字段按上述约定初始化。`level` 为 -1 或 0..9。`version` 的首字节可读，且与 `ZLIB_VERSION` 的首字节匹配，`stream_size == sizeof(z_stream)`。

**证明目标。**

- **目标。** `Goal.deflateInit__safety`（[Safety/Initialisation.lean](../../../ZlibF/Spec/Safety/Initialisation.lean)）；必需。定理：`ZlibF.Spec.Public.InitSafetyProof.deflateInit__safety`（[public-init-safety.lean](../../../ZlibF/Proof/public-init-safety.lean)）。
- **适用条件**（`InitArguments`）：
    1. 堆是库堆（`Fresh`、`Uniq`、`LibraryGlobals`）；
    2. `version` 为 NULL，或其首字节可读（`VersionValue`）；
    3. `strm` 为 NULL；或者指向一个可读的流记录，其 `zalloc` 和 `zfree` 各自为 NULL 或默认函数（`DefaultOrNull`）。
- **无条件覆盖。** 每一个 `level`，无论是否有效；每一个 `stream_size`；`version` 首字节的每一个取值；记录中其他字段的每一个取值，包括 `state`；每一种分配结果。本目标比前置条件宽：它还覆盖 `strm` 为 NULL、版本或 `stream_size` 不对，以及 `state` 不为 NULL 的记录。如果该记录原本是一个存活流，调用仍然返回，但旧状态仍处于已分配状态，而记录不再指向它：账本如实记下这次泄漏，并不排除它。
- **保证**（`InitResultSafe`）。
    - *返回。* 调用返回。`strm` 为 NULL 时，返回值是 `Z_VERSION_ERROR` 或 `Z_STREAM_ERROR`。
    - *状态。* 返回 `Z_OK` 时，`strm` 是可达流。
    - *写入。* `strm` 为 NULL 时不写任何内容：堆不变。否则只写流记录和调用自己分配的块。
    - *分配。* 返回 `Z_OK` 时，调用分配的每个块都是流自己的块，且不释放任何块（`LiveChange`）。返回其他状态码时，已分配的块与调用前相同。
- **不在本目标内。** `zalloc` 或 `zfree` 是自定义函数的流：在所有目标之外（见[偏离记录](../../deviations.md)）。各种拒绝和各种分配失败分别返回哪个状态码，以及调用之后各字段的值：功能目标 `Goal.deflateInit_`（不在计划内；已有定理证明它）。确实存在返回 `Z_OK` 的调用：`Goal.deflate_initialisation_domain`（[Safety/Domains.lean](../../../ZlibF/Spec/Safety/Domains.lean)），必需。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateInit_"><summary>完整返回条件与边界</summary>

**后置条件：** 满足 `deflateInit2_` 的契约，方法为 `Z_DEFLATED`，窗口为 15，`memLevel` 为 8，策略为 `Z_DEFAULT_STRATEGY`。级别 -1 选择 6。不消费输入，不写入输出。成功时返回 `Z_OK`；否则返回 `Z_MEM_ERROR`，并已完成全部清理。

**聚焦范围之外：** 适用与 `deflateInit2_` 相同的版本和参数拒绝。`deflateInit` 宏提供版本和结构大小。

</details>

## deflateInit2_

```c
int ZEXPORT deflateInit2_(z_streamp strm, int level, int method, int windowBits,
                           int memLevel, int strategy, const char *version, int stream_size);
```

选择封装和压缩设置，启动压缩器。

这些参数分别决定不同的事情。`level` 在压缩速度与匹配搜索工作量之间作选择；`method` 选择压缩方法，本条目只接受 DEFLATE；`memLevel` 控制内部索引和符号缓冲的内存配置；`strategy` 调整采用哪种匹配或编码策略。`windowBits` 同时编码封装和窗口大小：去掉符号或所加的常数，得到指数 b，窗口就是 `2^b` 字节。所以 15、-15 和 31 都表示 32768 字节，封装分别是 zlib、裸和 gzip。

### 返回值与后续调用 {#api-deflateinit2_-returns}

**返回值类型。** `int` — zlib 状态码

返回值区分压缩器已建立、兼容性拒绝、参数拒绝和分配失败。只有 Z_OK 建立需要结束的存活流。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**压缩器已建立** | 兼容性和参数有效，五项分配均成功；采用所选封装和设置。 | 可以提供缓冲区并开始压缩；最后用 deflateEnd 释放，即使放弃任务。 |
| `Z_VERSION_ERROR`<br>**兼容性拒绝** | version 为 NULL、版本首字节不匹配，或 stream_size 不等于 sizeof(z_stream)。此检查先于 strm 检查，且不改变流。 | 修正版本和结构大小后再初始化；此结果没有建立待释放的新状态。 |
| `Z_STREAM_ERROR`<br>**流指针为 NULL** | 兼容性检查通过，但 strm 为 NULL。 | 提供符合初始化前置条件的可写流记录后再初始化。 |
| `Z_STREAM_ERROR`<br>**参数被拒绝** | method、level、windowBits、memLevel 或 strategy 不在接受范围。拒绝发生于分配前，但 msg 已清空，并可能安装默认分配器、清空 opaque。 | 修正参数后按初始化的前置条件再调用；没有新分配需要结束。 |
| `Z_MEM_ERROR`<br>**状态分配失败** | 首项状态分配失败；state 保持进入时的值，没有新分配的块存活。 | 处理内存不足后可按初始化的前置条件重试；无需为此次失败调用 deflateEnd。 |
| `Z_MEM_ERROR`<br>**缓冲分配失败并已清理** | 状态分配成功后，四项缓冲分配全部尝试；任何失败都会释放所有新块，state 变为 NULL，msg 报告内存不足。 | 此调用已完成清理；处理内存不足后可重新初始化。 |

**判读要点。**

- 不消费输入、不写输出。级别 -1 选择 6。

### 调用条件与效果 {#api-deflateinit2_-contract}

**定义域：** 受限定义域。**效果：** 分配并初始化。

**前置条件：** 满足 `deflateInit_` 的流和版本条件。参数为：`level` 为 -1 或 0..9；`method == Z_DEFLATED`；`memLevel` 为 1..9；`strategy` 为 0..4；zlib 的 `windowBits` 为 8..15，裸流为 -15..-9，gzip 为 25..31。

**证明目标。**

- **目标。** `Goal.deflateInit2__safety`（[Safety/Initialisation.lean](../../../ZlibF/Spec/Safety/Initialisation.lean)）；必需。定理：`ZlibF.Spec.Public.InitSafetyProof.deflateInit2__safety`（[public-init-safety.lean](../../../ZlibF/Proof/public-init-safety.lean)）。
- **适用条件**（`InitArguments`）：
    1. 堆是库堆（`Fresh`、`Uniq`、`LibraryGlobals`）；
    2. `version` 为 NULL，或其首字节可读（`VersionValue`）；
    3. `strm` 为 NULL；或者指向一个可读的流记录，其 `zalloc` 和 `zfree` 各自为 NULL 或默认函数（`DefaultOrNull`）。
- **无条件覆盖。** 每一个 `level`、`method`、`windowBits`、`memLevel` 和 `strategy`，无论是否有效；每一个 `stream_size`；`version` 首字节的每一个取值；记录中其他字段的每一个取值，包括 `state`；每一种分配结果。本目标比前置条件宽：它还覆盖 `strm` 为 NULL、版本或 `stream_size` 不对，以及 `state` 不为 NULL 的记录。如果该记录原本是一个存活流，调用仍然返回，但旧状态仍处于已分配状态，而记录不再指向它：账本如实记下这次泄漏，并不排除它。
- **保证**（`InitResultSafe`）。
    - *返回。* 调用返回。`strm` 为 NULL 时，返回值是 `Z_VERSION_ERROR` 或 `Z_STREAM_ERROR`。
    - *状态。* 返回 `Z_OK` 时，`strm` 是可达流。
    - *写入。* `strm` 为 NULL 时不写任何内容：堆不变。否则只写流记录和调用自己分配的块。
    - *分配。* 返回 `Z_OK` 时，调用分配的每个块都是流自己的块，且不释放任何块（`LiveChange`）。返回其他状态码时，已分配的块与调用前相同。
- **不在本目标内。** `zalloc` 或 `zfree` 是自定义函数的流：在所有目标之外（见[偏离记录](../../deviations.md)）。各种拒绝和各种分配失败分别返回哪个状态码，以及调用之后各字段的值：功能目标 `Goal.deflateInit2_`（不在计划内；已有定理证明它）。确实存在返回 `Z_OK` 的调用：`Goal.deflate_initialisation_domain`（[Safety/Domains.lean](../../../ZlibF/Spec/Safety/Domains.lean)），必需。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateInit2_"><summary>完整返回条件与边界</summary>

**后置条件：** `Z_OK` 建立存活流，拥有五项分配和所选设置。zlib 窗口请求 8 变为 9。总计数为零，`msg` 为 NULL，`data_type` 为 `Z_UNKNOWN`，裸流/zlib 的 `adler` 为 1，gzip 的为 0。输入／输出指针和可用计数不变；不消费或输出字节。调用者用 `deflateEnd` 释放状态。

`Z_MEM_ERROR` 不留下任何新分配的存活块。如果状态分配失败，`state` 保持进入时的值。如果后续分配失败，`state` 变为 NULL，`msg` 报告内存不足。状态分配成功后，全部四项缓冲区分配都会被尝试，然后才进行失败清理。

**聚焦范围之外：** 版本指针为 NULL、首字节不匹配，或结构大小错误时，返回 `Z_VERSION_ERROR`，不改变流。版本兼容且 `strm` 为 NULL 时，返回 `Z_STREAM_ERROR`。其他超出可接受范围的标量参数在分配前返回 `Z_STREAM_ERROR`，此前会清空 `msg`，并按需安装默认分配器字段。安装默认分配器会清空 `opaque`。安全目标覆盖这些调用：每一个都返回，并且已分配的块保持原样。它们各自返回哪个状态码，由初始化的功能目标陈述。

</details>

## deflateSetDictionary

```c
int ZEXPORT deflateSetDictionary(z_streamp strm, const Bytef *dictionary, uInt dictLength);
```

将预置字节载入压缩历史，不把它们作为输入数据输出。

`dictLength` 是整个给定字典的字节数，`w_size` 是配置的历史窗口字节数；过长字典只把可用后缀留作历史，但 zlib 的字典标识仍覆盖整个给定字典。

### 返回值与后续调用 {#api-deflatesetdictionary-returns}

**返回值类型。** `int` — zlib 状态码

返回值说明预置历史是否被接受；字典不会作为普通的压缩输入输出。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**历史已载入** | 满足字典与流的前置条件；历史保留最多一个窗口的可用后缀，zlib 校验和覆盖完整字典。 | 随后开始压缩；需要预置历史的解码器须获得相同字典。next_in 和 avail_in 已恢复，不交付输出。 |
| `Z_STREAM_ERROR`<br>**字典条件不满足** | 流检查失败，或使用 gzip、NULL 字典、已离开初始状态的 zlib、预读字节数非零，或裸流不在已完成的块边界；均不改变流。 | 先建立合法的字典调用条件。原有的存活流如果仍在，可改用合法操作或 deflateEnd。 |

**判读要点。**

- 安全目标和功能目标都覆盖在合法块边界处替换裸流的字典，以及第一次 deflate 之前重复的 zlib 调用；重复的 zlib 调用累积 Adler-32。

### 调用条件与效果 {#api-deflatesetdictionary-contract}

**定义域：** 受限定义域。**效果：** 更新历史和字典校验和。

**前置条件：** 存活的裸流或 zlib 流，紧接初始化或 `deflateReset`，在第一次 `deflate` 和第一次字典调用之前。`dictionary` 非 NULL，覆盖 `dictLength` 个可读字节，且与窗口分离。

**证明目标。**

- **目标。** `Goal.deflateSetDictionary_safety`（[Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)）；必需。定理：`ZlibF.Spec.Public.StreamCallSafetyProof.deflateSetDictionary_safety`（[public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)）。这个目标有两个子句：对[被拒绝的流](contracts.md#reading-a-proof-goals-paragraph)的拒绝；对可达流的一次调用。`Goal.deflate_refusal`（[Safety/Refusals.lean](../../../ZlibF/Spec/Safety/Refusals.lean)）也是必需目标，它陈述同一个拒绝。
- **适用条件。** 拒绝子句要求 `strm` 是被拒绝的流（`RefusedDeflate`）。对可达流的调用要求（`StreamCallDomain`）：
    1. `strm` 是可达流（`StreamReachable`）；
    2. 平台大小上界成立（`ByteObjectsFit`）；
    3. `dictionary` 为 NULL，或指向 `dictLength` 个可读字节，且在流自己的块之外（`CallerRange`）。
- **无条件覆盖。** 每一个 `dictLength` 和每一种字典内容。每一个可达流，无论处于哪个阶段：第一次 `deflate` 之前、流的中途、收尾期间，以及 `Z_STREAM_END` 之后。本目标比前置条件宽：`dictionary` 可以为 NULL，封装可以是 gzip，调用可以出现在任何时刻。C 会拒绝返回值表中列出的那些情况。拒绝子句中：每一个被拒绝的流，以及其他参数的每个取值。
- **保证**（对可达流的调用是 `StreamCallSafe`）。
    - *返回。* 对被拒绝的流，调用返回 `Z_STREAM_ERROR`。对可达流调用时，调用返回。
    - *状态。* 对可达流调用时，流保持其不变量（`StreamInvariant`）。
    - *写入。* 对被拒绝的流不写任何内容：堆不变。对可达流调用时，只写流记录和流自己的块。
    - *分配。* 对可达流调用时，精确的分配账本（`LiveChange`）。
- **不在本目标内。** `zalloc` 和 `zfree` 已设置、而 `state` 是垃圾指针、指向已释放的状态或指向 inflate 状态的流记录：没有目标覆盖对这种记录的这个调用（见[偏离记录](../../deviations.md#note-2-refused-streams)）。返回哪个状态码，以及调用之后的历史：功能目标 `Goal.deflateSetDictionary`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateSetDictionary"><summary>完整返回条件与边界</summary>

**后置条件：** 返回 `Z_OK`。历史保留字典的可用后缀，最多一个窗口。zlib 的字典校验和覆盖整个给定字典。原 `next_in` 和 `avail_in` 被恢复；`total_in` 增加 `min(dictLength, w_size)`。不交付压缩输出，也不分配。需要字典时，必须向解码器提供相同的预置字典。

**聚焦范围之外：** gzip、NULL 字典、已离开初始状态的 zlib、非零预读字节数，或不在已完成块边界的裸流输入，均返回 `Z_STREAM_ERROR`，不发生变化。合法边界处的裸流字典替换，以及第一次 `deflate` 之前重复的 zlib 调用，安全目标和功能目标都覆盖。重复 zlib 调用会累积 Adler-32，而不是重新开始计算。

</details>

## deflateGetDictionary

```c
int ZEXPORT deflateGetDictionary(z_streamp strm, Bytef *dictionary, uInt *dictLength);
```

读取当前压缩历史，包括已接受的预读输入。

这里的“已接受”不等于已经编码。压缩器在决定匹配的同时，会把一些输入提前读入窗口。内部字段 `strstart` 是下一个待处理字节的数组下标，`lookahead` 是其后的预读字节数。下式中的 `w_size` 是配置的历史窗口字节数，不是整个物理数组的容量 `window_size`。`n` 表示本次最多复制多少历史字节。

### 返回值与后续调用 {#api-deflategetdictionary-returns}

**返回值类型。** `int` — zlib 状态码

状态码说明查询是否成功；实际历史字节和长度由可选输出参数提供。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**历史查询完成** | 存活流；dictionary 若非 NULL，接收窗口区域最后 n 个字节；dictLength 若非 NULL，接收 n，其中 n = min(strstart + lookahead, window size)。 | 使用所请求的结果；两种输出可独立省略，流不变，可继续合法调用。 |
| `Z_STREAM_ERROR`<br>**流检查未通过** | 流检查失败；正常操作尚未开始，流和结果单元均未写入。 | 先建立存活流并满足调用的前置条件；这个结果不表示操作已完成。 |

**判读要点。**

- 长度以字节计，包括已接受的预读输入；不保证包含全部历史输入的一个完整窗口。

### 调用条件与效果 {#api-deflategetdictionary-contract}

**定义域：** 受限定义域。**效果：** 可带输出缓冲区的查询。

**前置条件：** 存活流。`dictionary` 为 NULL，或可写一个窗口且与窗口分离；`dictLength` 为 NULL，或有效标量输出单元。

**证明目标。**

- **目标。** `Goal.deflateGetDictionary_safety`（[Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)）；必需。定理：`ZlibF.Spec.Public.StreamCallSafetyProof.deflateGetDictionary_safety`（[public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)）。这个目标有两个子句：对[被拒绝的流](contracts.md#reading-a-proof-goals-paragraph)的拒绝；对可达流的一次调用。`Goal.deflate_refusal`（[Safety/Refusals.lean](../../../ZlibF/Spec/Safety/Refusals.lean)）也是必需目标，它陈述同一个拒绝。
- **适用条件。** 拒绝子句要求 `strm` 是被拒绝的流（`RefusedDeflate`）。对可达流的调用要求（`StreamCallDomain`）：
    1. `strm` 是可达流（`StreamReachable`）；
    2. 平台大小上界成立（`ByteObjectsFit`）；
    3. `dictionary` 为 NULL，或指向 `min(w_size, strstart + lookahead)` 个可写字节（即本次调用复制的字节数），且在流自己的块之外（`CallerRange`）。
- **无条件覆盖。** 每一个可达流，无论处于哪个阶段：第一次 `deflate` 之前、流的中途、收尾期间，以及 `Z_STREAM_END` 之后。本目标比前置条件宽：前置条件要求整整一个窗口的空间。在翻译中 `dictLength` 是一个值而不是内存（见[共享约定](#shared-conventions)），所以本目标对这个指针没有要求。拒绝子句中：每一个被拒绝的流，以及其他参数的每个取值。
- **保证**（对可达流的调用是 `StreamCallSafe`）。
    - *返回。* 对被拒绝的流，调用返回 `Z_STREAM_ERROR`，不存入长度。对可达流调用时，调用返回。
    - *状态。* 对可达流调用时，流保持其不变量（`StreamInvariant`）。
    - *写入。* 对被拒绝的流不写任何内容：堆不变。对可达流调用时，只写流记录、流自己的块，以及 `dictionary` 起 32768 个字节范围内的字节。
    - *分配。* 对可达流调用时，精确的分配账本（`LiveChange`）。
- **不在本目标内。** `zalloc` 和 `zfree` 已设置、而 `state` 是垃圾指针、指向已释放的状态或指向 inflate 状态的流记录：没有目标覆盖对这种记录的这个调用（见[偏离记录](../../deviations.md#note-2-refused-streams)）。复制出的字节和报告的长度：功能目标 `Goal.deflateGetDictionary`（不在计划内；已有定理证明它）。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateGetDictionary"><summary>完整返回条件与边界</summary>

**后置条件：** 返回 `Z_OK`。设存活状态中的 `n = min(strstart + lookahead, w_size)`。非 NULL 的 `dictionary` 按顺序接收该窗口区域的最后 `n` 个字节；非 NULL 的 `dictLength` 接收 `n`。两种结果均可独立省略。流不变。历史不一定包含此前所有已提供输入中的完整一个窗口。

</details>

## deflateResetKeep

```c
int ZEXPORT deflateResetKeep(z_streamp strm);
```

重新开始输出和进度计数，同时保留压缩历史。

### 返回值与后续调用 {#api-deflateresetkeep-returns}

**返回值类型。** `int` — zlib 状态码

返回值说明输出进度是否已重置；成功仍保留可被后续压缩引用的历史。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**进度已重置，历史保留** | 存活流处于任意阶段。计数、校验和及封装进度重置；待输出数据和未处理完的预读输入丢弃，gzip 头指针清空。 | 仅在允许引用保留历史的任务中继续；需要空历史时使用 deflateReset。分配仍由流拥有。 |
| `Z_STREAM_ERROR`<br>**流检查未通过** | 流检查失败；正常操作尚未开始，流和结果单元均未写入。 | 先建立存活流并满足调用的前置条件；这个结果不表示操作已完成。 |

**判读要点。**

- 这是一个未文档化的条目。不改变 I/O 指针和可用计数，不分配或释放；保留级别、策略及调优。

### 调用条件与效果 {#api-deflateresetkeep-contract}

**定义域：** 受限定义域。**效果：** 重置，保留历史和分配。

**前置条件：** 处于任意阶段的存活流。如果下一个压缩流必须从空历史开始，使用 `deflateReset`。

**证明目标。** 没有必需目标：`zlib.h` 把这个函数声明在“`undocumented functions (not part of the zlib API)`”（未文档化的函数，不属于 zlib API）之下。直接调用它也不是 deflate 序列目标中的一步：`StreamOperation` 没有列出它（见[偏离记录](../../deviations.md)中“直接调用 `deflateResetKeep`”一行）。单次调用有功能目标 `Goal.deflateResetKeep`（[Functional/Lifecycle.lean](../../../ZlibF/Spec/Functional/Lifecycle.lean)）（不在计划内；已有定理证明它）：`ZlibF.Spec.Public.DeflateResetKeepProof.deflate_resetkeep_public`（[public-deflate-reset-keep.lean](../../../ZlibF/Proof/public-deflate-reset-keep.lean)）。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateResetKeep"><summary>完整返回条件与边界</summary>

**后置条件：** 返回 `Z_OK`。总计数变为零，`msg` 变为 NULL，`data_type` 变为 `Z_UNKNOWN`。待输出数据、尚未完成处理的预读输入，以及位/块进度被丢弃；封装输出重新开始，裸流/zlib 的 `adler` 变为 1，gzip 的变为 0。自定义 gzip 头指针清空。级别、策略、调优、窗口和哈希历史保留。输入／输出指针和可用计数不变。不分配或释放。

后续压缩器调用可以引用重置前的历史。因此，仅进行这种重置不保证所得流可以用空字典解码。

</details>

## deflateReset

```c
int ZEXPORT deflateReset(z_streamp strm);
```

复用流，以空历史开始新的压缩。

### 返回值与后续调用 {#api-deflatereset-returns}

**返回值类型。** `int` — zlib 状态码

返回值说明流是否已准备好以空历史复用。成功时保留已有分配。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**已重置为空历史** | 存活流处于任意阶段，包括 Z_STREAM_END 之后。计数、封装及待输出进度重置；历史和字典遗忘，调优恢复为当前级别默认值，gzip 头指针清空。 | 为新任务提供缓冲区；需要时设置它的字典或 gzip 头。最终仍需调用 deflateEnd。 |
| `Z_STREAM_ERROR`<br>**流检查未通过** | 流检查失败；正常操作尚未开始，流和结果单元均未写入。 | 先建立存活流并满足调用的前置条件；这个结果不表示操作已完成。 |

**判读要点。**

- 未完成输入与未交付输出被丢弃；I/O 指针和可用计数不变，级别、策略、封装和内存配置保留。

### 调用条件与效果 {#api-deflatereset-contract}

**定义域：** 受限定义域。**效果：** 重置，保留分配和配置。

**前置条件：** 任意阶段的存活流，包括 `Z_STREAM_END` 之后。

**证明目标。**

- **目标。** `Goal.deflateReset_safety`（[Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)）；必需。定理：`ZlibF.Spec.Public.StreamCallSafetyProof.deflateReset_safety`（[public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)）。这个目标有两个子句：对[被拒绝的流](contracts.md#reading-a-proof-goals-paragraph)的拒绝；对可达流的一次调用。
- **适用条件。** 拒绝子句要求 `strm` 是被拒绝的流（`RefusedDeflate`）。对可达流的调用要求（`StreamCallDomain`；这个调用没有参数条件）：
    1. `strm` 是可达流（`StreamReachable`）；
    2. 平台大小上界成立（`ByteObjectsFit`）。
- **无条件覆盖。** 每一个可达流，无论处于哪个阶段：第一次 `deflate` 之前、流的中途、收尾期间，以及 `Z_STREAM_END` 之后。拒绝子句中：每一个被拒绝的流。
- **保证**（对可达流的调用是 `StreamCallSafe`）。
    - *返回。* 对被拒绝的流，调用返回 `Z_STREAM_ERROR`。对可达流调用时，调用返回。
    - *状态。* 对可达流调用时，流保持其不变量（`StreamInvariant`）。
    - *写入。* 对被拒绝的流不写任何内容：堆不变。对可达流调用时，只写流记录和流自己的块。
    - *分配。* 对可达流调用时，精确的分配账本（`LiveChange`）。
- **不在本目标内。** `zalloc` 和 `zfree` 已设置、而 `state` 是垃圾指针、指向已释放的状态或指向 inflate 状态的流记录：没有目标覆盖对这种记录的这个调用（见[偏离记录](../../deviations.md#note-2-refused-streams)）。返回值和调用之后各字段的值：功能目标 `Goal.deflateReset`（不在计划内；已有定理证明它）。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateReset"><summary>完整返回条件与边界</summary>

**后置条件：** 返回 `Z_OK`。完成 `deflateResetKeep` 的计数、封装和待输出数据重置，且历史在逻辑上为空。此前的字典被遗忘；调优恢复为当前级别的默认值。保留 `deflateParams` 最后选择的级别和策略，以及封装、窗口、内存设置。gzip 头被遗忘。输入／输出指针和可用计数不变。不分配或释放。已经接受但尚未处理完的输入，以及尚未交付的输出被丢弃。

</details>

## deflateSetHeader

```c
int ZEXPORT deflateSetHeader(z_streamp strm, gz_headerp head);
```

选择下一个 gzip 流的头部。

### 返回值与后续调用 {#api-deflatesetheader-returns}

**返回值类型。** `int` — zlib 状态码

返回值说明 gzip 头指针是否已设置；成功不表示头部字节已输出。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**头指针已设置** | 存活的 gzip 流接受 head；NULL 选择默认头，非 NULL 头仍归调用者所有，尚不复制或输出头部字节。 | 在头部输出完成前保持记录和可选字段有效且不变；继续 deflate。两种重置都会清空指针。 |
| `Z_STREAM_ERROR`<br>**流不接受 gzip 头** | 流检查失败或封装不是 gzip；不发生变化。 | 在存活的 gzip 流上，按头部调用的前置条件设置；原存活流仍可合法继续或结束。 |

**判读要点。**

- 聚焦用法在第一次 deflate 前设置；较晚的设置虽被接受，却不重写已经输出的头部字节。

### 调用条件与效果 {#api-deflatesetheader-contract}

**定义域：** 受限定义域。**效果：** 保留调用者拥有的头部指针。

**前置条件：** 存活的 gzip 流，在初始化或重置之后、第一次 `deflate` 之前。`head` 为 NULL 时使用默认值，否则满足共享头部条件。

**证明目标。**

- **目标。** `Goal.deflateSetHeader_safety`（[Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)）；必需。定理：`ZlibF.Spec.Public.StreamCallSafetyProof.deflateSetHeader_safety`（[public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)）。这个目标有两个子句：对[被拒绝的流](contracts.md#reading-a-proof-goals-paragraph)的拒绝；对可达流的一次调用。
- **适用条件。** 拒绝子句要求 `strm` 是被拒绝的流（`RefusedDeflate`）。对可达流的调用要求（`StreamCallDomain`）：
    1. `strm` 是可达流（`StreamReachable`）；
    2. 平台大小上界成立（`ByteObjectsFit`）；
    3. `head` 为 NULL；或者指向一个存活的头部记录，该记录不是流自己的块，它的 `extra` 为 NULL 或指向 `extra_len` 个可读字节且在流自己的块之外，它的 `name` 和 `comment` 各自为 NULL 或以 NUL 结尾的字符串（`HeaderMemory`）；
    4. 自初始化或 `deflateReset` 以来，还没有 `deflate` 调用让流开始工作：流状态仍是 `INIT_STATE` 或 `GZIP_STATE`（`DeflateNotStarted`）。
- **无条件覆盖。** 每一种封装：流不必是 gzip 流，这一点比前置条件宽。调用顺序的要求与前置条件相同。拒绝子句中：每一个被拒绝的流，以及其他参数的每个取值。
- **保证**（对可达流的调用是 `StreamCallSafe`）。
    - *返回。* 对被拒绝的流，调用返回 `Z_STREAM_ERROR`。对可达流调用时，调用返回。
    - *状态。* 对可达流调用时，流保持其不变量（`StreamInvariant`）。
    - *写入。* 对被拒绝的流不写任何内容：堆不变。对可达流调用时，只写流记录和流自己的块。
    - *分配。* 对可达流调用时，精确的分配账本（`LiveChange`）。
- **不在本目标内。** 在 `deflate` 已经让流开始工作之后调用：在所有安全目标之外（见[偏离记录](../../deviations.md)中“头部参数”一行）。`zalloc` 和 `zfree` 已设置、而 `state` 是垃圾指针、指向已释放的状态或指向 inflate 状态的流记录：没有目标覆盖对这种记录的这个调用（见[偏离记录](../../deviations.md#note-2-refused-streams)）。返回值，以及此后由 `deflate` 写出的头部字节：功能目标 `Goal.deflateSetHeader`（不在计划内；已有定理证明它）。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateSetHeader"><summary>完整返回条件与边界</summary>

**后置条件：** 返回 `Z_OK` 并保留 `head`；此时尚不复制或输出头部字节。后续 `deflate` 写入请求的文本标志、时间、操作系统标识，以及可选的 extra 字段、文件名、注释和头部 CRC。压缩设置决定额外标志字节。调用者保持记录和字段有效，直到头部输出完成。两种重置都会清空该指针。不分配，也不转移所有权。

**聚焦范围之外：** 非 gzip 或流检查失败时，返回 `Z_STREAM_ERROR`，不发生变化。gzip 接受较晚的设置，但不会重写已经输出的头部字节。功能目标 `Goal.deflateSetHeader` 包括这一情况；安全目标不包括（见“证明目标”）。

</details>

## deflatePending

```c
int ZEXPORT deflatePending(z_streamp strm, unsigned *pending, int *bits);
```

查询压缩器内部等待输出的数据。

### 返回值与后续调用 {#api-deflatepending-returns}

**返回值类型。** `int` — zlib 状态码

状态码说明所请求的值能否放入各自的输出类型；待输出字节数和位数在输出参数中，不在返回值中。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**查询完成** | 流存活，且 pending 被省略或待输出整字节数可由 unsigned 表示。所请求的 pending 和 bits 接收当前字节数与位数；流和缓冲区不变。 | 使用请求的结果，继续合法流操作；两个输出都可以为 NULL。 |
| `Z_BUF_ERROR`<br>**请求的字节数已饱和** | pending 非 NULL，且内部整字节数超过 unsigned；`*pending` 写为 UINT_MAX。若请求 bits，仍写入位数；流不变。 | 将字节结果视为饱和值，不能视为精确长度；重复相同查询不会恢复精确值。流仍可合法使用。 |
| `Z_STREAM_ERROR`<br>**流检查未通过** | 流检查失败；正常操作尚未开始，流和结果单元均未写入。 | 先建立存活流并满足调用的前置条件；这个结果不表示操作已完成。 |

**判读要点。**

- 正常压缩历史下 bits 为 0..7；这是当前待输出位数，不是 deflateUsed 的最近刷新位数。

### 调用条件与效果 {#api-deflatepending-contract}

**定义域：** 受限定义域。**效果：** 可带标量结果的查询。

**前置条件：** 存活流；每个结果为 NULL，或有效且独立的输出单元。

**证明目标。**

- **目标。** `Goal.deflatePending_safety`（[Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)）；必需。定理：`ZlibF.Spec.Public.StreamCallSafetyProof.deflatePending_safety`（[public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)）。这个目标有两个子句：对[被拒绝的流](contracts.md#reading-a-proof-goals-paragraph)的拒绝；对可达流的一次调用。
- **适用条件。** 拒绝子句要求 `strm` 是被拒绝的流（`RefusedDeflate`）。对可达流的调用要求（`StreamCallDomain`；这个调用没有参数条件）：
    1. `strm` 是可达流（`StreamReachable`）；
    2. 平台大小上界成立（`ByteObjectsFit`）。
- **无条件覆盖。** 每一个可达流，无论处于哪个阶段：第一次 `deflate` 之前、流的中途、收尾期间，以及 `Z_STREAM_END` 之后。在翻译中，结果指针是值而不是内存（见[共享约定](#shared-conventions)）：本目标对它们没有要求，而前置条件要求它们指向可写单元。拒绝子句中：每一个被拒绝的流，以及其他参数的每个取值。
- **保证**（对可达流的调用是 `StreamCallSafe`）。
    - *返回。* 对被拒绝的流，调用返回 `Z_STREAM_ERROR`，两个计数都不存入。对可达流调用时，调用返回。
    - *状态。* 对可达流调用时，流保持其不变量（`StreamInvariant`）。
    - *写入。* 对被拒绝的流不写任何内容：堆不变。对可达流调用时，只写流记录和流自己的块。
    - *分配。* 对可达流调用时，精确的分配账本（`LiveChange`）。
- **不在本目标内。** `zalloc` 和 `zfree` 已设置、而 `state` 是垃圾指针、指向已释放的状态或指向 inflate 状态的流记录：没有目标覆盖对这种记录的这个调用（见[偏离记录](../../deviations.md#note-2-refused-streams)）。返回值和两个计数：功能目标 `Goal.deflatePending`（不在计划内；已有定理证明它）。

<details markdown="1" class="ar-return-exact" data-return-exact="deflatePending"><summary>完整返回条件与边界</summary>

**后置条件：** 返回 `Z_OK`。若请求相应结果，`pending` 接收尚未交付的整字节数，`bits` 接收剩余位数（合法压缩历史下为 0..7）。流及其缓冲区不变。被省略的结果不写入。

若状态中表示的待输出字节数超出 `unsigned` 的范围，所请求的字节计数饱和，并返回 `Z_BUF_ERROR`；若请求了位数结果，仍会写入。功能目标包括这种数值拒绝；默认构建的待输出缓冲区比这小。

</details>

## deflateUsed

```c
int ZEXPORT deflateUsed(z_streamp strm, int *bits);
```

查询最近一次字节边界刷新中，最后一个字节的位使用量。

### 返回值与后续调用 {#api-deflateused-returns}

**返回值类型。** `int` — zlib 状态码

返回值是查询状态；最近一次字节边界刷新的位使用量由可选 bits 输出。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**已读取保存的位数** | 存活流；bits 若非 NULL，接收保存值。正常历史下，字节边界刷新后为 1..8，自初始化或重置以来未发生这种刷新则为 0。 | 使用该保存结果，或以 NULL 省略输出；流不变，可继续合法操作。 |
| `Z_STREAM_ERROR`<br>**流检查未通过** | 流检查失败；正常操作尚未开始，流和结果单元均未写入。 | 先建立存活流并满足调用的前置条件；这个结果不表示操作已完成。 |

**判读要点。**

- 保存值不同于 deflatePending 的当前待输出位数。

### 调用条件与效果 {#api-deflateused-contract}

**定义域：** 受限定义域。**效果：** 可带标量结果的查询。

**前置条件：** 存活流；`bits` 为 NULL，或有效输出单元。

**证明目标。**

- **目标。** `Goal.deflateUsed_safety`（[Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)）；必需。定理：`ZlibF.Spec.Public.StreamCallSafetyProof.deflateUsed_safety`（[public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)）。这个目标有两个子句：对[被拒绝的流](contracts.md#reading-a-proof-goals-paragraph)的拒绝；对可达流的一次调用。
- **适用条件。** 拒绝子句要求 `strm` 是被拒绝的流（`RefusedDeflate`）。对可达流的调用要求（`StreamCallDomain`；这个调用没有参数条件）：
    1. `strm` 是可达流（`StreamReachable`）；
    2. 平台大小上界成立（`ByteObjectsFit`）。
- **无条件覆盖。** 每一个可达流，无论处于哪个阶段：第一次 `deflate` 之前、流的中途、收尾期间，以及 `Z_STREAM_END` 之后。在翻译中，结果指针是值而不是内存（见[共享约定](#shared-conventions)）：本目标对它们没有要求，而前置条件要求它们指向可写单元。拒绝子句中：每一个被拒绝的流，以及其他参数的每个取值。
- **保证**（对可达流的调用是 `StreamCallSafe`）。
    - *返回。* 对被拒绝的流，调用返回 `Z_STREAM_ERROR`，不存入计数。对可达流调用时，调用返回。
    - *状态。* 对可达流调用时，流保持其不变量（`StreamInvariant`）。
    - *写入。* 对被拒绝的流不写任何内容：堆不变。对可达流调用时，只写流记录和流自己的块。
    - *分配。* 对可达流调用时，精确的分配账本（`LiveChange`）。
- **不在本目标内。** `zalloc` 和 `zfree` 已设置、而 `state` 是垃圾指针、指向已释放的状态或指向 inflate 状态的流记录：没有目标覆盖对这种记录的这个调用（见[偏离记录](../../deviations.md#note-2-refused-streams)）。返回值和计数：功能目标 `Goal.deflateUsed`（不在计划内；已有定理证明它）。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateUsed"><summary>完整返回条件与边界</summary>

**后置条件：** 返回 `Z_OK`。若请求结果，存入已保存的位使用计数：字节边界刷新后为 1..8；如果自初始化/重置以来没有发生这种刷新，则为 0。流不变。该保存计数不同于 `deflatePending` 返回的当前待输出位数。

功能目标对每个通过检查的状态返回存储值，不假设任意可表示的状态都满足正常历史下的取值范围。

</details>

## deflatePrime

```c
int ZEXPORT deflatePrime(z_streamp strm, int bits, int value);
```

在裸流的压缩输出前添加调用者提供的位片段。

### 返回值与后续调用 {#api-deflateprime-returns}

**返回值类型。** `int` — zlib 状态码

返回值说明位片段是否加入待输出数据。因缓冲空间不足而拒绝时，片段的任何部分都不会插入。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**位片段已加入** | 流检查通过，bits 为 0..16，且待输出空间足够；追加 value 的低 bits 位，最低有效位优先，完整字节进入待输出缓冲。 | 在前置条件之内，仅在裸流的第一次 deflate 之前插入，并在解释输出时计入前缀；没有字节交付至 next_out。 |
| `Z_BUF_ERROR`<br>**位数超范围** | bits 不在 0..16；在待输出字节紧缩之前拒绝，不插入位。 | 修正位数，并满足位预置调用的前置条件后再调用。 |
| `Z_BUF_ERROR`<br>**待输出空间不足** | bits 为 0..16，但待输出缓冲没有容纳片段所需的空间；不插入位，但已有待输出字节可能已被紧缩。 | 原样重复调用不会腾出空间；先按所选位拼接协议合法处理待输出数据，再决定是否重试。 |
| `Z_STREAM_ERROR`<br>**流检查未通过** | 流检查失败；正常操作尚未开始，流和结果单元均未写入。 | 先建立存活流并满足调用的前置条件；这个结果不表示操作已完成。 |

**判读要点。**

- 实现不检查封装或首次调用时机；接受位片段本身不保证任意插入后的普通流格式有效。没有分配。

### 调用条件与效果 {#api-deflateprime-contract}

**定义域：** 受限定义域。**效果：** 将位追加到待输出数据。

**前置条件：** 存活的裸流，在初始化或 `deflateReset` 后第一次 `deflate` 之前；`bits` 为 0..16，`value` 为任意 `int`。调用者解释后续压缩流时需计入这些前缀位。

**证明目标。**

- **目标。** `Goal.deflatePrime_safety`（[Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)）；必需。定理：`ZlibF.Spec.Public.StreamCallSafetyProof.deflatePrime_safety`（[public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)）。这个目标有两个子句：对[被拒绝的流](contracts.md#reading-a-proof-goals-paragraph)的拒绝；对可达流的一次调用。
- **适用条件。** 拒绝子句要求 `strm` 是被拒绝的流（`RefusedDeflate`）。对可达流的调用要求（`StreamCallDomain`）：
    1. `strm` 是可达流（`StreamReachable`）；
    2. 平台大小上界成立（`ByteObjectsFit`）；
    3. 自初始化或 `deflateReset` 以来，还没有 `deflate` 调用让流开始工作：流状态仍是 `INIT_STATE` 或 `GZIP_STATE`（`DeflateNotStarted`）。
- **无条件覆盖。** 每一个 `bits` 和 `value`；每一种封装。本目标比前置条件宽：前置条件要求流是裸流，且 `bits` 在 0..16 内。调用顺序的要求与前置条件相同。拒绝子句中：每一个被拒绝的流，以及其他参数的每个取值。
- **保证**（对可达流的调用是 `StreamCallSafe`）。
    - *返回。* 对被拒绝的流，调用返回 `Z_STREAM_ERROR`。对可达流调用时，调用返回。
    - *状态。* 对可达流调用时，流保持其不变量（`StreamInvariant`）。
    - *写入。* 对被拒绝的流不写任何内容：堆不变。对可达流调用时，只写流记录和流自己的块。
    - *分配。* 对可达流调用时，精确的分配账本（`LiveChange`）。
- **不在本目标内。** 在 `deflate` 已经让流开始工作之后调用：在所有安全目标之外（见[偏离记录](../../deviations.md)中“其他流参数”一行）。`zalloc` 和 `zfree` 已设置、而 `state` 是垃圾指针、指向已释放的状态或指向 inflate 状态的流记录：没有目标覆盖对这种记录的这个调用（见[偏离记录](../../deviations.md#note-2-refused-streams)）。返回哪个状态码，以及调用之后的待输出位：功能目标 `Goal.deflatePrime`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="deflatePrime"><summary>完整返回条件与边界</summary>

**后置条件：** `Z_OK` 将 `value` 的低 `bits` 位按最低有效位优先的顺序，追加到逻辑待输出位序列。完整字节加入待输出数据，缓冲中剩余少于 8 位。不向 `next_out` 交付字节；不分配。待输出缓冲区空间不足时，`Z_BUF_ERROR` 不插入任何位。在该拒绝之前，已有的待输出字节可能已在其所属缓冲区内被紧缩。

**聚焦范围之外：** 计数不在 0..16 时，在紧缩前返回 `Z_BUF_ERROR`；流检查失败返回 `Z_STREAM_ERROR`。功能目标覆盖每一种封装、每一种调用顺序下对待输出位的精确效果。

</details>

## deflateParams

```c
int ZEXPORT deflateParams(z_streamp strm, int level, int strategy);
```

更改级别和策略，必要时先完成旧块。

### 返回值与后续调用 {#api-deflateparams-returns}

**返回值类型。** `int` — zlib 状态码

返回值说明新级别和策略是否已安装。为完成旧块，本次调用可能先消费输入并交付输出。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**新设置已安装** | 参数有效，且所需旧块处理已完成；级别 -1 选择 6，更改级别会恢复其标准调优。必要刷新使用旧设置，可产生 I/O 进展。 | 按更新后的指针和计数接走输出、保留未消费输入，并以新设置继续。 |
| `Z_BUF_ERROR`<br>**旧块尚未完成** | 所需旧块尚未处理完；级别和策略保持原值，但已消费输入和已交付输出等压缩进展保留。 | 提供更多输出空间，保留更新后的流与剩余输入，重试 deflateParams；存活流及其分配保留。 |
| `Z_STREAM_ERROR`<br>**设置参数被拒绝** | level 不是 -1 或 0..9，或 strategy 不在 0..4；拒绝时不改变流。 | 修正参数后可在合法流阶段重试；新设置尚未生效。 |
| `Z_STREAM_ERROR`<br>**所需刷新被拒绝** | 参数本身有效，但所需 deflate(Z_BLOCK) 返回 Z_STREAM_ERROR，例如收尾已开始或缓冲条件不满足；新设置没有安装。 | 先确定调用开始时流所处的阶段和缓冲条件。收尾已经开始时，按 Z_FINISH 协议完成，或合法重置/结束。 |
| `Z_STREAM_ERROR`<br>**流检查未通过** | 流检查失败；正常操作尚未开始，流和结果单元均未写入。 | 先建立存活流并满足调用的前置条件；这个结果不表示操作已完成。 |

**判读要点。**

- 要选择精确输入边界，先完成 deflate(Z_BLOCK) 直到 avail_out 非零，并在更改参数之前不提供新输入。

### 调用条件与效果 {#api-deflateparams-contract}

**定义域：** 受限定义域。**效果：** 更新设置；可以消费输入并输出数据。

**前置条件：** 存活且尚未开始收尾的流，流缓冲区和任何正在使用的头部均有效；`level` 为 -1 或 0..9，`strategy` 为 0..4。要选择精确输入边界，持续完成 `deflate(Z_BLOCK)`，直到 `avail_out` 非零，并在此次调用前不提供新输入。

**证明目标。**

- **目标。** `Goal.deflateParams_safety`（[Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)）；必需。定理：`ZlibF.Spec.Public.StreamCallSafetyProof.deflateParams_safety`（[public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)）。这个目标有两个子句：对[被拒绝的流](contracts.md#reading-a-proof-goals-paragraph)的拒绝；对可达流的一次调用。`Goal.deflate_refusal`（[Safety/Refusals.lean](../../../ZlibF/Spec/Safety/Refusals.lean)）也是必需目标，它陈述同一个拒绝。
- **适用条件。** 拒绝子句要求 `strm` 是被拒绝的流（`RefusedDeflate`）。对可达流的调用要求（`StreamCallDomain`）：
    1. `strm` 是可达流（`StreamReachable`）；
    2. 平台大小上界成立（`ByteObjectsFit`）；
    3. [deflate](#deflate) 的条件 3 到 6，即对缓冲区和 gzip 头的要求（`StreamBuffers`、`ActiveHeader`）：这个调用可能执行 `deflate(strm, Z_BLOCK)`。
- **无条件覆盖。** 每一个 `level` 和 `strategy`，无论是否有效。每一个可达流，无论处于哪个阶段：第一次 `deflate` 之前、流的中途、收尾期间，以及 `Z_STREAM_END` 之后。本目标在参数取值、阶段和缓冲区三方面都比前置条件宽（缓冲区方面同 [deflate](#deflate)）。拒绝子句中：每一个被拒绝的流，以及其他参数的每个取值。
- **保证**（对可达流的调用是 `StreamCallSafe`）。
    - *返回。* 对被拒绝的流，调用返回 `Z_STREAM_ERROR`。对可达流调用时，调用返回。
    - *状态。* 对可达流调用时，流保持其不变量（`StreamInvariant`）。
    - *写入。* 对被拒绝的流不写任何内容：堆不变。对可达流调用时，只写流记录、流自己的块和 `next_out` 处的 `avail_out` 个字节。
    - *分配。* 对可达流调用时，精确的分配账本（`LiveChange`）。
- **不在本目标内。** `zalloc` 和 `zfree` 已设置、而 `state` 是垃圾指针、指向已释放的状态或指向 inflate 状态的流记录：没有目标覆盖对这种记录的这个调用（见[偏离记录](../../deviations.md#note-2-refused-streams)）。返回哪个状态码、生效的设置和写出的字节：功能目标 `Goal.deflateParams`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateParams"><summary>完整返回条件与边界</summary>

**后置条件：** `Z_OK` 安装请求的设置（级别 -1 表示 6）。更改级别会恢复该级别的标准调优值。必要的块刷新使用旧设置，可能消费部分输入并交付输出。输入／输出指针、可用计数和总计数精确记录这些字节；未消费输入保持可用。

`Z_BUF_ERROR` 表示旧块尚未完成；级别和策略不变，但已发生的压缩推进和输出保留。提供更多输出空间后重试。两种结果都保留存活流及其分配集合。

**聚焦范围之外：** 无效级别/策略返回 `Z_STREAM_ERROR`，不发生变化。必要的块刷新也可能返回 `Z_STREAM_ERROR`，包括收尾已经开始之后的情况。

</details>

## deflateTune

```c
int ZEXPORT deflateTune(z_streamp strm, int good_length, int max_lazy, int nice_length, int max_chain);
```

设置供专家使用的四个匹配搜索调优值。

这些设置改变寻找重复片段时投入多少工作，并不指定输出字节。前三个是以输入字节计的长度，最后一个是候选个数：

| 参数 | 控制的内容 |
| --- | --- |
| `good_length` | 已找到的匹配达到这个长度时，继续搜索的候选链预算减小。 |
| `max_lazy` | 长度阈值：已有匹配短于它时，惰性匹配仍会尝试下一位置；快速匹配器用它限制短匹配之后的逐位置插入。 |
| `nice_length` | 找到达到这个长度的匹配即可提前停止搜索。 |
| `max_chain` | 一次搜索最多检查多少候选。 |

例如增加 `max_chain`，可能让搜索看到更早、更长的匹配，也可能增加比较工作。这不保证每次输出都更小；参数按下面给出的 C 规则存储。

### 返回值与后续调用 {#api-deflatetune-returns}

**返回值类型。** `int` — zlib 状态码

返回值只说明四个调优字段是否存入，不保证任意取值下后续压缩的性质。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**调优值已存入** | 存活流接受所有 int 参数；good_length、max_lazy 和 max_chain 转为 unsigned，nice_length 按 signed 存储。不消费输入或交付输出。 | 选择适用于后续压缩的调优；deflateReset 或 deflateParams 更改级别会恢复标准值。 |
| `Z_STREAM_ERROR`<br>**流检查未通过** | 流检查失败；正常操作尚未开始，流和结果单元均未写入。 | 先建立存活流并满足调用的前置条件；这个结果不表示操作已完成。 |

**判读要点。**

- C 建议 max_lazy >= 3、max_chain >= 4。

### 调用条件与效果 {#api-deflatetune-contract}

**定义域：** 受限定义域（存活流）；覆盖所有 `int` 调优参数。

**效果：** 更新调优字段。

**前置条件：** 存活流。

**证明目标。**

- **目标。** `Goal.deflateTune_safety`（[Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)）；必需。定理：`ZlibF.Spec.Public.StreamCallSafetyProof.deflateTune_safety`（[public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)）。这个目标有两个子句：对[被拒绝的流](contracts.md#reading-a-proof-goals-paragraph)的拒绝；对可达流的一次调用。
- **适用条件。** 拒绝子句要求 `strm` 是被拒绝的流（`RefusedDeflate`）。对可达流的调用要求（`StreamCallDomain`；这个调用没有参数条件）：
    1. `strm` 是可达流（`StreamReachable`）；
    2. 平台大小上界成立（`ByteObjectsFit`）。
- **无条件覆盖。** 四个调优参数的每一个取值。每一个可达流，无论处于哪个阶段：第一次 `deflate` 之前、流的中途、收尾期间，以及 `Z_STREAM_END` 之后。拒绝子句中：每一个被拒绝的流，以及其他参数的每个取值。
- **保证**（对可达流的调用是 `StreamCallSafe`）。
    - *返回。* 对被拒绝的流，调用返回 `Z_STREAM_ERROR`。对可达流调用时，调用返回。
    - *状态。* 对可达流调用时，流保持其不变量（`StreamInvariant`）。
    - *写入。* 对被拒绝的流不写任何内容：堆不变。对可达流调用时，只写流记录和流自己的块。
    - *分配。* 对可达流调用时，精确的分配账本（`LiveChange`）。
- **不在本目标内。** `zalloc` 和 `zfree` 已设置、而 `state` 是垃圾指针、指向已释放的状态或指向 inflate 状态的流记录：没有目标覆盖对这种记录的这个调用（见[偏离记录](../../deviations.md#note-2-refused-streams)）。返回值和存入的字段：功能目标 `Goal.deflateTune`（不在计划内；已有定理证明它）。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateTune"><summary>完整返回条件与边界</summary>

**后置条件：** 返回 `Z_OK`。将 `good_length`、`max_lazy`、`max_chain` 转为无符号后存入，将 `nice_length` 作为有符号值存入。不消费输入、不交付输出、不分配。`deflateParams` 更改级别，或执行 `deflateReset`，会恢复标准调优。仅凭该设置函数的契约，不能确立所有调优选择下的后续压缩上界；C 建议 `max_lazy >= 3` 和 `max_chain >= 4`。

</details>

## deflateBound_z

```c
z_size_t ZEXPORT deflateBound_z(z_streamp strm, z_size_t sourceLen);
```

根据流当前的配置和封装计算大小上界。

这个查询回答“为整份输入准备多少输出字节才足够”。`sourceLen` 是输入字节数，下面记作 `n`；`w` 是头部、尾部及可选字段合计的封装字节数。`floor(x)` 表示向下取整。`SIZE_MAX` 是返回类型 `z_size_t` 能表示的最大值；“饱和”表示数学结果再大也只返回这个最大值，而不回绕成较小数。

### 返回值与后续调用 {#api-deflatebound_z-returns}

**返回值类型。** `z_size_t` — 输出容量上界（字节）

返回值是以字节计的输出容量上界数值，不是 zlib 状态码。结果可能在 SIZE_MAX 处饱和。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `bound`<br>**输出字节数上界** | 存活流按当前窗口、内存级别、压缩级别、策略和完整封装大小选择公式；NULL 或可安全检查的无效流采用固定/存储公式较大者加 18。结果均在 SIZE_MAX 处饱和，堆不变。 | 所述容量保证只在以下条件下适用：在初始化和各项设置之后、压缩之前调用；配置、字典和头部保持不变；使用标准调优；没有预置位。还须满足缓冲区可表示以及 avail_in/avail_out 的容量条件。 |

**判读要点。**

- SIZE_MAX 可能是精确值，也可能是饱和结果；它不保证存在这么大的可寻址缓冲区。没有错误码。
- 在容量保证的各项前提下，把全部输入和至少这么多输出空间交给一次 deflate(Z_FINISH)，必须得到 Z_STREAM_END；仅 Z_NO_FLUSH 后接 Z_FINISH 的安排具有总输出上界，其他刷新可能超出。

### 调用条件与效果 {#api-deflatebound_z-contract}

**定义域：** 受限定义域（存活流和可读的保留头部）；包括每个 `z_size_t sourceLen`。**效果：** 查询。

**前置条件：** 存活流，满足共享头部条件。对于下述输出容量保证，应在初始化及任何字典/头部设置后、压缩前调用。保持配置、头部和字典不变；使用标准调优，不插入预置位。

**证明目标。**

- **目标。** `Goal.deflateBound_z_safety`（[Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)）；必需。定理：`ZlibF.Spec.Public.StreamCallSafetyProof.deflateBound_z_safety`（[public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)）。这个目标有两个子句：对[被拒绝的流](contracts.md#reading-a-proof-goals-paragraph)的拒绝；对可达流的一次调用。
- **适用条件。** 拒绝子句要求 `strm` 是被拒绝的流（`RefusedDeflate`）。对可达流的调用要求（`StreamCallDomain`）：
    1. `strm` 是可达流（`StreamReachable`）；
    2. 平台大小上界成立（`ByteObjectsFit`）；
    3. [deflate](#deflate) 的条件 4 到 6，即对 gzip 头的要求（`ActiveHeader`）；
    4. 已交给 `deflateSetHeader` 的头部记录在本次调用时存活且可读，而不只是在写出头部期间：该记录存活，且不是流自己的块；非 NULL 的 `extra` 指向 `extra_len` 个可读字节，且在流自己的块之外；非 NULL 的 `name` 或 `comment` 是以 NUL 结尾的字符串（`DeflateHeaderLive`）。
- **无条件覆盖。** 每一个 `sourceLen`。每一个可达流，无论处于哪个阶段：第一次 `deflate` 之前、流的中途、收尾期间，以及 `Z_STREAM_END` 之后。拒绝子句中：每一个被拒绝的流，以及其他参数的每个取值。
- **保证**（对可达流的调用是 `StreamCallSafe`）。
    - *返回。* 对被拒绝的流，调用返回的值与 `strm` 为 NULL、`sourceLen` 相同时返回的值相同：这是保守的上界，不是错误码。对可达流调用时，调用返回。
    - *状态。* 对可达流调用时，流保持其不变量（`StreamInvariant`）。
    - *写入。* 对被拒绝的流不写任何内容：堆不变。对可达流调用时，只写流记录和流自己的块。
    - *分配。* 对可达流调用时，精确的分配账本（`LiveChange`）。
- **不在本目标内。** `zalloc` 和 `zfree` 已设置、而 `state` 是垃圾指针、指向已释放的状态或指向 inflate 状态的流记录：没有目标覆盖对这种记录的这个调用（见[偏离记录](../../deviations.md#note-2-refused-streams)）。返回的值：功能目标 `Goal.deflateBound_z`（不在计划内；未完成）。这么多输出空间确实足够：功能目标 `Goal.deflate_sequence` 的子句 `DeflateCompletes`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateBound_z"><summary>完整返回条件与边界</summary>

**后置条件：** 堆不变。要得到的数值是下述数学值，在 `SIZE_MAX` 处饱和，其中 `n = sourceLen`，`w` 为完整封装大小：

- 窗口 15、内存级别 8 且策略不是 `Z_FIXED`：`n + floor(n/4096) + floor(n/16384) + floor(n/33554432) + 7 + w`。
- 否则，若窗口位数不超过哈希位数且级别非零：`n + floor(n/8) + floor(n/256) + floor(n/512) + 4 + w`。
- 否则：`n + floor(n/32) + floor(n/128) + floor(n/2048) + 7 + w`。

哈希位数等于内存级别加 7。第一种情况里“且策略不是 `Z_FIXED`”这几个字就是补丁 0006 的改动：未打补丁的 C 对每一种策略都使用第一个公式。策略为 `Z_FIXED`、窗口 15、内存级别 8 时，打过补丁的函数在级别 1 到 9 使用第二个公式，在级别 0 使用第三个公式。对于级别 1 到 3 的 `Z_FIXED`，第一个公式偏小：在未打补丁的 C 上，一次 `deflate(Z_FINISH)` 调用即使得到这么多输出空间，也可能返回 `Z_OK`（见[发现](../../findings/deflatebound-fixed-far-matches/README.md)，已用真实的 C 复现）。

裸流的 `w` 为 0；zlib 为 6，存在预置历史时再加 4；gzip 为 18，再加可选的 extra 字段（包括两个长度字节）、以零终止的名称/注释和头部 CRC。

**输出容量：** 与数值公式分开，对于大小可表示且足够的缓冲区，如果输入和输出大小能放入 `avail_in` 和 `avail_out`，向一次 `deflate(Z_FINISH)` 提供全部 `n` 个字节及至少为上界的输出空间，必须返回 `Z_STREAM_END`。在 `Z_FINISH` 前仅使用 `Z_NO_FLUSH` 的干净调用安排具有总输出上界。其他刷新安排可能超出此上界。饱和结果不承诺存在这样大小的可寻址缓冲区。

**聚焦范围之外：** NULL 或可安全检查的无效流，得到上述固定/存储公式中的较大值，再加 18，并进行饱和。没有错误码。功能目标覆盖每一种可读的 gzip 头部长度，包括大于 65535 的 `extra_len`；本页的契约不涉及这种长度。

</details>

## deflateBound

```c
uLong ZEXPORT deflateBound(z_streamp strm, uLong sourceLen);
```

返回压缩上界的 `uLong` 形式。

### 返回值与后续调用 {#api-deflatebound-returns}

**返回值类型。** `uLong` — 输出容量上界（字节）

返回 deflateBound_z 上界的 uLong 形式，仍以字节计。ULONG_MAX 是数值上限，不是错误码。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `bound`<br>**uLong 输出字节数上界** | deflateBound_z 的数值可由 uLong 表示时原样返回，否则返回 ULONG_MAX；NULL 或可安全检查的无效流也使用其保守回退公式。流不变。 | 用于容量规划时，遵守 deflateBound_z 关于设置时机、固定设置、调优、无预置位、缓冲区和刷新安排的条件。 |

**判读要点。**

- ULONG_MAX 可能是精确值，也可能是被截到上限的结果；数值相等本身不提供额外容量保证。
- 默认 LP64 下，uLong 和 z_size_t 都为 64 位，两种查询结果一致。

### 调用条件与效果 {#api-deflatebound-contract}

**定义域：** 与 `deflateBound_z` 相同的受限定义域；包括每个 `uLong sourceLen`。

**效果：** 查询。

**前置条件：** 适用 `deflateBound_z` 的条件。

**证明目标。**

- **目标。** `Goal.deflateBound_safety`（[Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)）；必需。定理：`ZlibF.Spec.Public.StreamCallSafetyProof.deflateBound_safety`（[public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)）。这个目标有两个子句：对[被拒绝的流](contracts.md#reading-a-proof-goals-paragraph)的拒绝；对可达流的一次调用。
- **适用条件。** 拒绝子句要求 `strm` 是被拒绝的流（`RefusedDeflate`）。对可达流的调用要求（`StreamCallDomain`）：
    1. `strm` 是可达流（`StreamReachable`）；
    2. 平台大小上界成立（`ByteObjectsFit`）；
    3. [deflate](#deflate) 的条件 4 到 6，即对 gzip 头的要求（`ActiveHeader`）；
    4. 已交给 `deflateSetHeader` 的头部记录在本次调用时存活且可读，而不只是在写出头部期间：该记录存活，且不是流自己的块；非 NULL 的 `extra` 指向 `extra_len` 个可读字节，且在流自己的块之外；非 NULL 的 `name` 或 `comment` 是以 NUL 结尾的字符串（`DeflateHeaderLive`）。
- **无条件覆盖。** 每一个 `sourceLen`。每一个可达流，无论处于哪个阶段：第一次 `deflate` 之前、流的中途、收尾期间，以及 `Z_STREAM_END` 之后。拒绝子句中：每一个被拒绝的流，以及其他参数的每个取值。
- **保证**（对可达流的调用是 `StreamCallSafe`）。
    - *返回。* 对被拒绝的流，调用返回的值与 `strm` 为 NULL、`sourceLen` 相同时返回的值相同：这是保守的上界，不是错误码。对可达流调用时，调用返回。
    - *状态。* 对可达流调用时，流保持其不变量（`StreamInvariant`）。
    - *写入。* 对被拒绝的流不写任何内容：堆不变。对可达流调用时，只写流记录和流自己的块。
    - *分配。* 对可达流调用时，精确的分配账本（`LiveChange`）。
- **不在本目标内。** `zalloc` 和 `zfree` 已设置、而 `state` 是垃圾指针、指向已释放的状态或指向 inflate 状态的流记录：没有目标覆盖对这种记录的这个调用（见[偏离记录](../../deviations.md#note-2-refused-streams)）。返回的值：功能目标 `Goal.deflateBound`（不在计划内；未完成）。这么多输出空间确实足够：功能目标 `Goal.deflate_sequence` 的子句 `DeflateCompletes`（不在计划内；未完成）。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateBound"><summary>完整返回条件与边界</summary>

**后置条件：** 如果 `deflateBound_z` 的结果（含补丁 0006 的改动）能由 `uLong` 表示，则返回该结果，否则返回 `ULONG_MAX`。默认 LP64 目标中两种类型都是 64 位，结果相同。流不变。输出是否足够，仍要求 `deflateBound_z` 单独规定的调用安排和容量条件，不能只由数值相等推出。

</details>

## deflate

```c
int ZEXPORT deflate(z_streamp strm, int flush);
```

接受输入，交付有效压缩流的一部分或全部。

`flush` 描述调用者希望推进到哪里：普通调用交给压缩器选择输出时机，刷新请求建立所选边界，`Z_FINISH` 请求结束整个流。请求不会让有限的输出缓冲区变大：空间用完时，取走输出，再按下述协议继续。

### 返回值与后续调用 {#api-deflate-returns}

**返回值类型。** `int` — zlib 状态码

返回值区分需要继续、整个压缩流完成，以及拒绝或无法推进。更新后的指针和计数给出本次调用消费和交付的字节数。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**尚可能需要继续** | 调用尚未报告完整流结束。可能已消费输入，或已交付头部、数据、刷新标记或尾部的字节；输出填满时仍可能有未消费输入或待输出数据。 | 接走输出并使用更新后的计数；输出填满时补空间，刷新期间保持同一个 `flush` 值。收尾开始后不增加输入，只用 Z_FINISH 继续直到 Z_STREAM_END。 |
| `Z_STREAM_END`<br>**完整压缩流已交付** | 仅在 Z_FINISH 下，所有给定输入及全部压缩输出（包括封装尾部）均已交付。 | 保存最终输出；用 deflateEnd 释放，或 deflateReset 开始新流。此返回本身不释放状态。 |
| `Z_BUF_ERROR`<br>**没有输出空间** | 初始检查通过，但 avail_out 为 0；不消费输入、不交付输出，原存活流保留。 | 提供有效非空输出空间后继续；若正在刷新，保持原来的 `flush` 值，收尾期间只用 Z_FINISH。 |
| `Z_BUF_ERROR`<br>**目前无法推进** | 没有可用输入或待输出数据，且没有比此前更强的刷新请求；当前非 Z_FINISH 调用无法推进。 | 等待新输入，或在应用确实需要时选择更强的合法刷新；不要原样循环。流仍然存活。 |
| `Z_BUF_ERROR`<br>**最终处理后又提供输入** | 最终块处理已开始后仍提供新输入；不接受新输入，但拒绝前可能已交付旧待输出数据。存活流保留。 | 接走实际交付的输出，把未接受的新输入留给另一任务；不再向此流提供输入，仅用 Z_FINISH 完成，或合法重置/结束。 |
| `Z_STREAM_ERROR`<br>**流或调用参数被拒绝** | 流检查失败、`flush` 无效（包括 Z_TREES）、next_out 为 NULL、输入量非零而 next_in 为 NULL，或收尾开始后使用非 Z_FINISH 的刷新。初始拒绝不消费或交付字节。 | 先确定流是存活的，并修正缓冲区或 `flush`；收尾开始后只用 Z_FINISH。流检查失败时，不保证任意状态都可以重试或结束。 |

**判读要点。**

- 状态码不是本轮字节计数；I/O 指针、avail_in/avail_out 和 total_in/total_out 记录实际进展。调用不分配或释放。
- 非结束性的刷新完成后，返回的仍是 Z_OK，不表示流已结束；应结合输出空间和所用刷新协议判断该边界是否完成。错误返回仍可能改变 msg 或记住的 `flush` 值。

### 调用条件与效果 {#api-deflate-contract}

**定义域：** 受限定义域。**效果：** 消费输入、输出数据并更新进度。

**前置条件：** 存活流，缓冲区和任何正在使用的头部均有效。`next_out` 非 NULL，`avail_out > 0`；仅输入为零时 `next_in` 可为 NULL。`flush` 为 `Z_NO_FLUSH`、`Z_PARTIAL_FLUSH`、`Z_SYNC_FLUSH`、`Z_FULL_FLUSH`、`Z_FINISH` 或 `Z_BLOCK`。刷新期间输出填满时，以相同刷新请求和更多空间继续。收尾开始后，不提供新输入，只以 `Z_FINISH` 继续。普通格式有效性要求从初始化/`deflateReset`（或该历史的副本）开始，使用合法字典/头部设置、标准调优，且不进行任意位预置。

**证明目标。**

- **目标。** `Goal.deflate_safety`（[Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)）；必需。定理：`ZlibF.Spec.Public.StreamCallSafetyProof.deflate_safety`（[public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)）。这个目标有两个子句：对[被拒绝的流](contracts.md#reading-a-proof-goals-paragraph)的拒绝；对可达流的一次调用。`Goal.deflate_refusal`（[Safety/Refusals.lean](../../../ZlibF/Spec/Safety/Refusals.lean)）也是必需目标，它陈述同一个拒绝。
- **适用条件。** 拒绝子句要求 `strm` 是被拒绝的流（`RefusedDeflate`）。对可达流的调用要求（`StreamCallDomain`）：
    1. `strm` 是可达流（`StreamReachable`）；
    2. 平台大小上界成立（`ByteObjectsFit`）；
    3. `next_in` 为 NULL，或指向 `avail_in` 个可读字节；`next_out` 为 NULL，或指向 `avail_out` 个可写字节；两个范围都不在流自己的块内，且互不重叠（`StreamBuffers`）；
    4. 在写出 gzip 头期间（流状态为 `GZIP_STATE` 到 `HCRC_STATE`），如果已有头部记录交给 `deflateSetHeader`：该记录存活，且不是流自己的块；非 NULL 的 `extra` 指向 `extra_len` 个可读字节，且在流自己的块之外；非 NULL 的 `name` 或 `comment` 是以 NUL 结尾的字符串（`HeaderMemory`）；
    5. 调用者保留了已经写出的部分：正在写出的字段（`extra`、`name` 或 `comment`）仍然覆盖已写出的那一段，并且没有在写出一部分之后被置为 NULL（`DeflateHeaderProgress`）；
    6. 在写出头部期间：输入范围、输出范围、`extra`（`extra_len mod 2^16` 个字节）、`name` 和 `comment`（各自直到其 NUL）两两不重叠，并且 `extra`、`name`、`comment` 在流自己的块之外（`DeflateHeaderApart`）。条件 4 到 6 合起来就是 `ActiveHeader`。
- **无条件覆盖。** 每一个 `flush` 值，包括不是刷新码的值；每一种输入字节序列。每一个可达流，无论处于哪个阶段：第一次 `deflate` 之前、流的中途、收尾期间，以及 `Z_STREAM_END` 之后。本目标比前置条件宽：`next_out` 可以为 NULL，`avail_out` 可以为零，`next_in` 可以在 `avail_in` 非零时为 NULL，`flush` 可以是任意 `int`。C 会拒绝或报告这些情况（见上面的返回值表）。拒绝子句中：每一个被拒绝的流，以及其他参数的每个取值。
- **保证**（对可达流的调用是 `StreamCallSafe`）。
    - *返回。* 对被拒绝的流，调用返回 `Z_STREAM_ERROR`。对可达流调用时，调用返回。
    - *状态。* 对可达流调用时，流保持其不变量（`StreamInvariant`）。
    - *写入。* 对被拒绝的流不写任何内容：堆不变。对可达流调用时，只写流记录、流自己的块和 `next_out` 处的 `avail_out` 个字节。
    - *分配。* 对可达流调用时，精确的分配账本（`LiveChange`）。
- **不在本目标内。** `zalloc` 和 `zfree` 已设置、而 `state` 是垃圾指针、指向已释放的状态或指向 inflate 状态的流记录：没有目标覆盖对这种记录的这个调用（见[偏离记录](../../deviations.md#note-2-refused-streams)）。返回哪个状态码、写出哪些字节：功能目标 `Goal.deflate`（不在计划内；已有定理证明它）。

<details markdown="1" class="ar-return-exact" data-return-exact="deflate"><summary>完整返回条件与边界</summary>

**后置条件：** 记本轮消费的输入字节数为 `used`，交付的输出字节数为 `made`；`old avail_in` 和 `old avail_out` 是调用前提供的输入量和输出容量。满足 `used <= old avail_in`、`made <= old avail_out`。指针按相应数量推进，可用计数按相应数量减少，总计数按相应数量增加并遵循无符号回绕。输入不变；已交付前缀以外的输出不变。输出填满时可能仍有输入未消费。不分配或释放。

跨调用交付的字节构成已接受输入的一种有效编码的前缀，使用所选封装、设置和预置字典。完成的输出可解码为该输入。这里规定有效输出，而非唯一的压缩字节序列。头部写出之后，`adler` 跟踪已接受的输入：zlib 用 Adler-32，gzip 用 CRC-32；裸流没有输入校验和。

`Z_OK` 表示可能需要继续。`Z_STREAM_END` 只在 `Z_FINISH` 下发生，且所有给定输入及所有压缩输出（包括尾部）都已交付。存活的状态仍被拥有，直到 `deflateEnd` 释放，或通过 `deflateReset` 复用。

请求的刷新完全交付后，`Z_BLOCK` 完成一个块但不填充到字节边界；`Z_PARTIAL_FLUSH` 添加空固定块；`Z_SYNC_FLUSH` 使此前全部输入可供解码器解码，并以对齐的空存储块结尾。`Z_FULL_FLUSH` 还重置匹配历史：后续块不引用该次已完成刷新之前的数据。若要在那里重新启动裸流解码器，需要保留精确边界，并先交付完整刷新标记。`Z_FINISH` 关闭最终块并写入封装尾部。

**错误：** `Z_BUF_ERROR` 覆盖输出空间为零、无输入且无更强刷新请求因而无法推进，或最终块处理已开始后又提供输入。它保留存活流；应按需提供空间/输入。`Z_STREAM_ERROR` 覆盖流检查失败、无效刷新（包括 `Z_TREES`）、无效 NULL 输入／输出组合，或收尾开始后请求非 `Z_FINISH` 的刷新。初始参数拒绝不消费输入、不交付输出。收尾开始后，因新输入而产生的较晚 `Z_BUF_ERROR`，可能先交付旧的待输出数据；不接受新输入。`msg` 和记录的刷新请求可能改变。安全目标和功能目标都包括所有有符号刷新值及这些拒绝。

</details>

## deflateEnd

```c
int ZEXPORT deflateEnd(z_streamp strm);
```

释放压缩器，丢弃任何未完成工作。

### 返回值与后续调用 {#api-deflateend-returns}

**返回值类型。** `int` — zlib 状态码

返回值区分释放前的压缩阶段。Z_OK 和 Z_DATA_ERROR 都表示五项流分配已释放，state 已清空。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**状态已释放** | 存活流的保存状态不是 BUSY_STATE；全部流分配已恰好释放一次，state 为 NULL。 | 保留调用者自有的缓冲区和头部；再次压缩前重新初始化。返回值本身不确认所有输出已交付。 |
| `Z_DATA_ERROR`<br>**未完成任务已释放** | 存活流的保存状态为 BUSY_STATE，报告未完成压缩；全部流分配仍已释放，state 为 NULL。 | 不要为清理再次调用 deflateEnd；未完成压缩已经放弃，再次压缩须重新初始化。 |
| `Z_STREAM_ERROR`<br>**结束请求被拒绝** | 流检查失败，包括第二次结束；本次不释放任何内容。 | 不要把该结果当作释放成功；先确定流的实际生命周期，再做任何压缩或清理。 |

**判读要点。**

- 返回状态取决于内部阶段，不只是输出是否全部交付。调用者输入、输出和头部仍归调用者所有，且不被释放。

### 调用条件与效果 {#api-deflateend-contract}

**定义域：** 受限定义域。**效果：** 释放拥有的状态。

**前置条件：** 任意阶段的存活流，默认释放例程保持完整。

**证明目标。**

- **目标。** `Goal.deflateEnd_safety`（[Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)）；必需。定理：`ZlibF.Spec.Public.StreamCallSafetyProof.deflateEnd_safety`（[public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)）。这个目标有两个子句：对[被拒绝的流](contracts.md#reading-a-proof-goals-paragraph)的拒绝；可达流的结束。
- **适用条件。** 拒绝子句要求 `strm` 是被拒绝的流（`RefusedDeflate`）。可达流的结束要求 `strm` 是可达流（`StreamReachable`）；不要求平台大小上界。
- **无条件覆盖。** 每一个可达流，无论处于哪个阶段：第一次 `deflate` 之前、流的中途、收尾期间，以及 `Z_STREAM_END` 之后。拒绝子句中：每一个被拒绝的流。
- **保证。**
    - *返回。* 对被拒绝的流，调用返回 `Z_STREAM_ERROR`。对可达流调用时，调用返回，返回值为 `Z_OK` 或 `Z_DATA_ERROR`。
    - *状态。* 对可达流调用时，调用之后 `strm->state` 为 NULL。
    - *写入。* 对被拒绝的流不写任何内容：堆不变。对可达流调用时，只写流记录和流自己的块。
    - *分配。* 对可达流调用时，精确的分配账本（`LiveChange`）：流自己的块被释放；除此之外不释放任何块，也不分配任何块。
- **不在本目标内。** `zalloc` 和 `zfree` 已设置、而 `state` 是垃圾指针、指向已释放的状态或指向 inflate 状态的流记录：没有目标覆盖对这种记录的这个调用（见[偏离记录](../../deviations.md#note-2-refused-streams)）。返回两个状态码中的哪一个，以及流的其他字段的值：功能目标 `Goal.deflateEnd`（不在计划内；已有定理证明它）。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateEnd"><summary>完整返回条件与边界</summary>

**后置条件：** 对全部五项拥有的分配恰好释放一次，并将 `state` 置为 NULL。调用者输入/输出及头部存储不变，仍归调用者所有。保存的状态为 `BUSY_STATE` 时返回 `Z_DATA_ERROR`，否则返回 `Z_OK`。两种结果都释放全部资源：`Z_DATA_ERROR` 报告未完成压缩，不表示清理失败。重新初始化前，后续压缩调用均无效。

**聚焦范围之外：** 流检查失败，包括第二次结束，返回 `Z_STREAM_ERROR`，不释放任何内容。返回状态取决于内部压缩阶段，而不只是是否已交付每个产生的字节。

</details>

## deflateCopy

```c
int ZEXPORT deflateCopy(z_streamp dest, z_streamp source);
```

创建压缩进度相同、彼此独立的压缩器。

### 返回值与后续调用 {#api-deflatecopy-returns}

**返回值类型。** `int` — zlib 状态码

返回值说明目的流是否获得独立的压缩状态。失败时的清理涉及的是此次的新分配，源流保持不变。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**独立状态已复制** | 源存活，且目的流满足“另一个空记录”的前置条件；目的流获得五项新分配及等价进度，内部指针重定位，源不变。 | 两个流分别需要 deflateEnd；继续推进两个流之前，给它们各自独立的输出空间。复制的 I/O 指针起初相同，保留的头部仍是两个流共享、归调用者所有的存储。 |
| `Z_MEM_ERROR`<br>**分配失败并已清理** | 任意新分配失败；所有新块已释放，dest->state 清空，目的流的其他字段和源不变，没有新的存活目的流。 | 不要结束失败的目的流；处理内存不足后可按复制的前置条件重试，源仍可合法继续或结束。 |
| `Z_STREAM_ERROR`<br>**目的流为 NULL** | dest 为 NULL，复制未开始。 | 提供不同于源且不拥有状态的可写目的记录，再按复制的前置条件调用。 |
| `Z_STREAM_ERROR`<br>**源检查未通过** | 目的流非 NULL，但源检查失败；dest->state 清空，不进行复制分配。 | 先建立存活的源；只对不同且不拥有状态的目的流调用，不能据此认为任意原有目的流状态已被释放。 |

**判读要点。**

- 契约排除自复制和覆盖已经存活的目的流；这些情况没有无泄漏保证。

### 调用条件与效果 {#api-deflatecopy-contract}

**定义域：** 受限定义域。**效果：** 分配并复制拥有的状态。

**前置条件：** `source` 存活。`dest` 是另一个可写 `z_stream`，不拥有状态，且与源的内存分离。源缓冲区和任何保留的头部满足生命周期要求。

**证明目标。**

- **目标。** `Goal.deflateCopy_safety`（[Safety/Copy.lean](../../../ZlibF/Spec/Safety/Copy.lean)）；必需。定理：`Zlib.Deflate.Universal.deflate_copy_safety`（[public-deflate-copy.lean](../../../ZlibF/Proof/public-deflate-copy.lean)）。这个目标有四个子句：对 NULL `dest` 的拒绝；对 NULL `source` 的拒绝；从可达的源复制（主子句）；对属于[被拒绝的流](contracts.md#reading-a-proof-goals-paragraph)的 `source` 的拒绝。`Goal.deflate_refusal`（[Safety/Refusals.lean](../../../ZlibF/Spec/Safety/Refusals.lean)）也是必需目标，它同样陈述对被拒绝的源的拒绝。
- **适用条件。** 对 NULL `dest` 的拒绝没有条件。对 NULL `source` 的拒绝要求 `dest` 指向一个可读的流记录。对被拒绝的 `source` 的拒绝要求 `dest` 指向一个可读的流记录，并要求 `source` 不是 NULL 且是被拒绝的流（`RefusedDeflate`）；它不要求 `dest` 与 `source` 不同。主子句要求：
    1. `source` 是可达流（`StreamReachable`）。命题还把它的不变量和默认分配器作为假设（`DGood`、`DefAlloc`）；每个可达流都满足它们（`Goal.deflate_sequence_safety` 的第一个子句）；
    2. `dest` 指向一个可读的流记录，且不是 `source` 记录（`source ≠ dest`）。不要求平台大小上界。
- **无条件覆盖。** `dest` 记录的每一种内容；每一种分配结果。拒绝子句中：`dest` 记录的每一种内容，每一个被拒绝的 `source`，以及 `dest` 为 NULL 时的每一个 `source` 指针。本目标比前置条件宽：`dest` 的各字段可以是任意值。如果 `dest` 原本是一个存活流，它的旧状态仍处于已分配状态，而记录不再指向它。
- **保证。**
    - *返回。* `dest` 为 NULL、`source` 为 NULL 或 `source` 被拒绝时，调用返回 `Z_STREAM_ERROR`。从可达的源复制时，调用返回，返回值为 `Z_OK` 或 `Z_MEM_ERROR`。只有在某次分配确实失败之后才返回 `Z_MEM_ERROR`（`AllocationFailed`）。
    - *状态。* 从可达的源复制时：`source` 记录及其状态不变。返回 `Z_OK` 时，`dest` 满足流不变量（`StreamInvariant`），并且按 `StreamReachable` 的定义是可达流。返回 `Z_MEM_ERROR` 时，`dest->state` 为 NULL，`dest` 的其他字段不变。
    - *写入。* `dest` 为 NULL 时不写任何内容：堆不变。`source` 为 NULL 或被拒绝时，只写 `dest->state`，把它置为 NULL；`dest` 的其他字段和堆的其余部分不变。从可达的源复制时，只写 `dest` 记录和调用自己分配的块。
    - *分配。* 三种拒绝都不分配也不释放任何块。从可达的源复制时：返回 `Z_OK` 时，新块恰好有五个：新的状态记录和它的四个缓冲区（`window`、`prev`、`head`、`pending_buf`）。不释放任何块。安全目标没有说 `dest->state` 指向这个记录；功能目标 `Goal.deflateCopy` 说了这一点。返回 `Z_MEM_ERROR` 时，已分配的块与调用前相同。
- **不在本目标内。** `zalloc` 和 `zfree` 已设置、而 `state` 是垃圾指针、指向已释放的状态或指向 inflate 状态的 `source` 记录：没有目标覆盖从这种源的复制（见[偏离记录](../../deviations.md#note-2-refused-streams)）。`source` 可达而 `dest == source`：没有目标覆盖这个调用（见[偏离记录](../../deviations.md)中“复制的目的流”一行）。副本的内容：功能目标 `Goal.deflateCopy`（不在计划内；已有定理证明它）。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateCopy"><summary>完整返回条件与边界</summary>

**后置条件：** `Z_OK` 使 `dest` 获得五项新拥有的分配，包含等价的压缩状态；源不变。复制的流字段包括总计数、分配器字段、输入／输出指针和保留的头部指针。内部拥有的指针被重定位到新分配。两个流各自需要 `deflateEnd`，可独立继续。复制得到的调用者输入／输出指针起初指向相同的缓冲区；继续推进两个流之前，应给它们各自独立的输出空间。头部仍是共享的调用者自有存储。

`Z_MEM_ERROR` 释放每项新分配、清空 `dest->state`，并保持目的流的其他字段和源不变。没有新的存活状态需要释放。

**聚焦范围之外：** NULL 目的流返回 `Z_STREAM_ERROR`；源检查失败还会清空非 NULL 目的流的状态。安全目标和功能目标都假设两个流不同。

</details>

[返回 API 手册](README.md) · [契约约定](contracts.md)

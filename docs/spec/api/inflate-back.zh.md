<!-- source-sha256: 7ae16099487643cd825524f2aab0dd20b872ff6edd0de7d4fa82523afea145f4 -->

# 回调解压

[API 手册](README.md) · [共享流规则](streams.md) · [流式解压](inflate-stream.md)

回调接口允许调用者提供输入块，并直接从窗口接收解码输出。
先用 [inflateBackInit_](#inflatebackinit_) 初始化，再用 [inflateBack](#inflateback) 解码，
最后用 [inflateBackEnd](#inflatebackend) 释放状态。窗口始终由调用者拥有。

这些聚焦契约对应固定版本的 [infback.c](../../../zlib/infback.c) 和
[zlib.h](../../../zlib/zlib.h)，针对默认 LP64 Linux 构建。
定义域和效果标签见[契约约定](contracts.md)。
超出聚焦前提只表示本契约不作保证，不自动等于 C 未定义行为（UB），也不保证一定返回错误码。

**已证明的内容。** 每个函数的必需目标是它的安全目标：没有未定义行为、没有内存错误、没有泄漏，并且终止（见[安全性](../safety.md)）。各条目在“证明目标”下写出这个目标及其前提。证明所假设的是这些前提，而不是文档中的前置条件；两者不同时，以 Lean 陈述为准。这里描述的返回值、输出字节和状态变化属于功能行为：它们读自 C 源码，凡是没有已登记定理陈述的，都还需要由证明核实。它们不在计划的证明目标之内。哪些目标已登记，见[进度](../../progress.md)。

三个函数的必需安全目标都是 [Sequences.lean](../../../ZlibF/Spec/Public/Sequences.lean) 中的
`Goal.inflate_back_sequence_safety`；逐函数的安全目标尚未写出。功能目标 `Goal.inflateBackInit_`、`Goal.inflateBack`
和 `Goal.inflateBackEnd` 在 [Back.lean](../../../ZlibF/Spec/Public/Back.lean) 中。
`Goal.inflateBack` 的解码子句（什么数据到达 `out`）不在计划内。

`inflateBack` 解码 raw DEFLATE。任何 zlib/gzip 头部、尾部和校验和都由调用者处理。
调用者拥有一个至少 `2^windowBits` 字节的可写窗口，它同时也是输出缓冲区。
`windowBits` 是窗口字节数的二进制指数：15 表示 `2^15 = 32768` 字节。对一般流使用这个配置；更小窗口可能拒绝有效的长距离引用。

```mermaid
flowchart LR
    I["inflateBackInit_: 分配状态"] --> B["inflateBack: 解码一个流"]
    B -->|另一个流| B
    B -->|成功或解码错误| E["inflateBackEnd: 释放状态"]
    I -->|无需解码| E
```

回调让库在需要数据时主动调用应用代码。输入回调的参数 `in_desc` 是应用自己的上下文；`buf` 接收下一块输入的起始指针，返回值给出这块输入的字节数。输出回调的 `out_desc` 也是应用上下文；`buf` 和 `len` 给出本次可以读取的输出范围，`len` 以字节计。库把指针和长度交给回调，不转移窗口的所有权。

回调类型如下：

```c
typedef unsigned (*in_func)(void FAR *, z_const unsigned char FAR * FAR *);
typedef int (*out_func)(void FAR *, unsigned char FAR *, unsigned);
```

`in(in_desc, &buf)` 返回字节数并设置 `buf`；零表示没有输入，此时忽略 `buf`。
`out(out_desc, buf, len)` 接收至多一个窗口的字节；零表示成功。
若回调支持 NULL，描述参数可以为 NULL。

## inflateBackInit_

```c
int ZEXPORT inflateBackInit_(z_streamp strm, int windowBits, unsigned char FAR *window,
                             const char *version, int stream_size);
```

**用途。** 分配解码器状态并关联调用者的窗口。
`inflateBackInit` 宏提供 `version` 和 `stream_size`。

### 返回值与后续调用 {#api-inflatebackinit_-returns}

**返回值类型。** `int` — zlib 状态码

结果说明回调解码状态是否已建立并关联调用者窗口。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**回调解码器已建立** | 版本和流大小匹配，8 <= windowBits <= 15，窗口非 NULL 且状态分配成功。 | 保持窗口存活并用 inflateBack 解码；最终调用 inflateBackEnd。 |
| `Z_VERSION_ERROR`<br>**版本或结构大小不匹配** | version 为 NULL、主版本字节不同或 stream_size 错误；在访问流前返回。 | 修正版本及结构大小后重新初始化；本次失败无需结束。 |
| `Z_STREAM_ERROR`<br>**流、窗口或位数被拒绝** | strm 或 window 为 NULL，或 windowBits 不在 8..15 范围内。 | 提供有效的非活跃流、窗口及位数后重新初始化；本次失败无需结束。 |
| `Z_MEM_ERROR`<br>**状态分配失败** | 未能分配状态；msg 和默认分配器字段可能改变，旧 state 字段保留。 | 资源可用时可重新初始化；未保留新分配，本次失败无需 inflateBackEnd。 |

**判读要点。**

- 窗口始终属于调用者；此函数只建立回调 API 状态，不能作为普通 inflate 状态使用。

### 调用条件与效果 {#api-inflatebackinit_-contract}

**定义域。** 受限定义域：有效调用者内存、未活动的流和默认分配器。

**前置条件。** 非 NULL 的 `strm` 指向可写 `z_stream`，其 `zalloc`、`zfree` 和
`opaque` 已初始化。使用 NULL 或默认分配／释放函数对；不得覆盖仍活跃的库状态。
非 NULL 的 `version` 的首字节可读。在初始化路径上，`window` 提供与流分离的
`2^windowBits` 个可写字节。该切片须保持存活直到结束操作。

**效果。** 可能初始化分配器字段和 `opaque`，清除 `msg`，并分配一个状态。
窗口仍由调用者拥有，此处不分配、不清空，也不释放窗口。

**证明目标。** 必需的安全目标：`Goal.inflate_back_sequence_safety`（[Public/Sequences.lean](../../../ZlibF/Spec/Public/Sequences.lean)）。它是序列目标：逐函数目标尚未写出。它的历史是 `BackSafeReachable`：在 `InitDomain` 上以 8..15 的 `windowBits` 和一个非 NULL 的窗口成功初始化，窗口有 `2^windowBits` 个可写字节，并且是某个堆字节块的一段。这个目标的历史从成功的初始化开始。它对失败或被拒绝的初始化调用不作陈述；那些路径在功能目标里。合法的初始化成功、只写流记录、恰好分配一个块，是必需的非空性目标 `Goal.inflate_back_initialisation_domain`。功能目标（非必需）：`Goal.inflateBackInit_`。

<details markdown="1" class="ar-return-exact" data-return-exact="inflateBackInit_"><summary>完整返回条件与边界</summary>

**后置条件。** `Z_OK` 关联供 `inflateBack` 使用的新状态，且 `8 <= windowBits <= 15`。
输入／输出指针、可用计数、累计计数、`adler` 和 `data_type` 不变。
只初始化指定的状态字段；该状态须用于回调 API。

**错误。** NULL 版本、主版本字节不同或流大小错误，会在访问流前返回 `Z_VERSION_ERROR`。
NULL `strm`／`window`，或位数不在 8..15 内，返回 `Z_STREAM_ERROR`。
分配失败返回 `Z_MEM_ERROR`：`msg` 和默认分配器字段可能已改变，但保留原 `state` 字段。
没有分配状态，因此在此未活动流定义域内，初始化失败后不需要结束调用。

</details>

## inflateBack

```c
int ZEXPORT inflateBack(z_streamp strm, in_func in, void FAR *in_desc,
                        out_func out, void FAR *out_desc);
```

**用途。** 通过输入和输出回调解码一个完整 raw 流。

### 返回值与后续调用 {#api-inflateback-returns}

**返回值类型。** `int` — zlib 状态码

结果覆盖一个完整 raw 流的回调解码。此函数不返回 Z_OK，每次调用都会从一个新流开始。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_STREAM_END`<br>**raw 流及输出已完成** | 完整 raw DEFLATE 流已解码，且每个输出回调均返回零。 | 保留 next_in/avail_in 指示的未读后缀；可解码另一个独立流，或调用 inflateBackEnd。 |
| `Z_BUF_ERROR`<br>**输入回调没有更多数据** | 返回时 next_in 为 NULL；输入回调返回零，输入耗尽。 | 当前解码未完成；可结束，或准备完整输入后从头开始新的解码，不能当作暂停续接。 |
| `Z_BUF_ERROR`<br>**输出回调失败** | 返回时 next_in 非 NULL；输出回调返回非零。最终输出失败会把原 Z_STREAM_END 改为此值。 | 处理调用者输出故障；可结束，或从头开始独立解码，不能按普通 inflate 的方式续接。 |
| `Z_DATA_ERROR`<br>**DEFLATE 格式错误** | 发现畸形 raw DEFLATE 并设置 msg；此前可能已经输出数据，最终输出失败不覆盖此错误。 | 可调用 inflateBackEnd；再次 inflateBack 会从新流开始，须重新准备输入。 |
| `Z_STREAM_ERROR`<br>**缺少流或状态** | strm 或 state 为 NULL；不调用回调。 | 先用 inflateBackInit_ 建立有效回调解码器；普通 inflate 状态不可用于此接口。 |

**判读要点。**

- Z_BUF_ERROR 时用 next_in 是否为 NULL 区分输入耗尽与输出失败；这不是普通 inflate 的缓冲重试协议。
- 输入回调返回字节数，零表示无输入；输出回调返回零表示成功。错误之前及最终错误路径都可能交付输出。

### 调用条件与效果 {#api-inflateback-contract}

**定义域。** 受限定义域：活跃的回调解码器、有效且分离的切片，以及有限、会返回的
回调协议。包括任意畸形输入字节。

**前置条件。** 初始化成功且尚未结束。保持流、状态和窗口存活。
初始化 `next_in`；NULL 表示立即请求回调输入，并忽略 `avail_in`。
否则初始化 `avail_in`，并在 `next_in` 提供相应数量的可读字节。
初始输入切片和回调提供的输入切片均不与窗口、流或私有状态重叠。
两个回调均非 NULL。每次回调都安全返回，且提供的输入总量有界。

回调只能读取收到的输入／输出字节以及自身的有效对象。
可以修改、分配或释放自身内存，但须保持流、私有状态和窗口切片不变。
输入块在下一次输入回调或函数返回前须持续可读且不变，包括跨越输出回调时。
输出回调最多读取 `len` 个窗口字节。
若所用字节切片不重叠，回调存储与窗口可共用一次分配。
禁止对该流进行并发或重入访问。

**效果。** 重置解码以处理新流，消费输入、写窗口并调用回调。
完整窗口和最终非空的部分窗口均交给 `out`，包括错误路径。
因此回调可能在后续格式或输入失败之前已观察到输出。
库本身不分配或释放内存；回调分配的内存仍由调用者负责。

**证明目标。** 必需的安全目标：`Goal.inflate_back_sequence_safety`（[Public/Sequences.lean](../../../ZlibF/Spec/Public/Sequences.lean)）。它是序列目标：逐函数目标尚未写出。它的历史是 `BackSafeReachable`：在 `InitDomain` 上以 8..15 的 `windowBits` 和一个非 NULL 的窗口成功初始化，窗口有 `2^windowBits` 个可写字节，并且是某个堆字节块的一段。再调用一次的前提：`next_in` 为 NULL，或覆盖 `avail_in` 个可读字节且不与窗口重叠；回调遵守某个 `CallbackProtocol`，其输入总量少于 `2^48` 字节（`inputBound`）；每个字节对象小于 `2^63` 字节，并且回调保持这一点（`BackPlatform`）；每个输入块，包括第一块和 `in` 交出的每一块，都位于堆字节块中（`BackFirstChunk`、`BackPlatform`）。输入字节任意。结论：调用返回 `Z_STREAM_END`、`Z_DATA_ERROR` 或 `Z_BUF_ERROR`，状态在同一窗口上保持有效，只改变流记录、状态记录、回调自己的块和窗口那一段，回调自有块之外的存活块不变。NULL 流在同一个目标里被拒绝。比 `zlib.h` 更窄的前提在[偏离记录](../../deviations.md)中各有一行。功能目标（非必需）：`Goal.inflateBack`。

<details markdown="1" class="ar-return-exact" data-return-exact="inflateBack"><summary>完整返回条件与边界</summary>

**后置条件。** `Z_STREAM_END` 表示完整 raw 流已解码，且每次输出调用都成功。
拼接各块得到其未压缩字节，不使用预置字典。
`next_in`／`avail_in` 指出初始输入块或最后一个回调块的未读后缀。
输入耗尽后两者为 NULL／零；否则指针按已消费字节数前移。
累计计数、`adler` 和 `data_type` 不变；`next_out`／`avail_out` 不用于输出接口。
流保留状态和窗口，可供下次独立解码或结束操作使用。

**错误。** `Z_BUF_ERROR` 表示输入耗尽或输出结果非零；本函数从不返回 `Z_OK`。
对 `Z_BUF_ERROR`，NULL `next_in` 表示输入耗尽，非 NULL 表示输出失败。
`Z_DATA_ERROR` 表示畸形 DEFLATE，并设置 `msg`。
最终输出失败会将 `Z_STREAM_END` 改为 `Z_BUF_ERROR`，但不替换此前已选定的其他错误。
NULL `strm` 或 NULL 状态返回 `Z_STREAM_ERROR`，不调用回调。
其他无效状态不在本定义域内：普通 `inflateInit_` 产生的状态不是回调解码器。
解码错误后，结束操作仍释放状态；再次调用则从一个新流开始。

</details>

## inflateBackEnd

```c
int ZEXPORT inflateBackEnd(z_streamp strm);
```

**用途。** 释放回调初始化所分配的状态。

### 返回值与后续调用 {#api-inflatebackend-returns}

**返回值类型。** `int` — zlib 状态码

结果说明内部回调状态是否已释放；调用者窗口始终由调用者管理。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**内部状态已释放** | 有效回调解码器的内部状态已释放，state 置为 NULL；窗口及其他字段不变。 | 现在可释放或复用调用者窗口；再次解码前重新初始化。 |
| `Z_STREAM_ERROR`<br>**未执行释放** | strm、state 或 zfree 为 NULL；不释放任何内存。 | 确认生命周期及匹配的释放函数；不能由这些检查推断任意非 NULL 状态有效。 |

### 调用条件与效果 {#api-inflatebackend-contract}

**定义域。** 受限定义域：使用有效默认释放函数的活跃回调解码器，另包括经检查的
NULL 流、NULL 状态和 NULL 释放函数拒绝情形。

**前置条件。** 清理时初始化已成功、尚未结束，且没有解码或回调正在活动。
流和所关联状态仍有效；保留匹配的 `zfree` 和 `opaque`。
成功解码或任何解码错误后均允许清理。

**效果。** 恰好释放内部状态，并清除 `state`。

**证明目标。** 必需的安全目标：`Goal.inflate_back_sequence_safety`（[Public/Sequences.lean](../../../ZlibF/Spec/Public/Sequences.lean)）。它是序列目标：逐函数目标尚未写出。它的历史是 `BackSafeReachable`：在 `InitDomain` 上以 8..15 的 `windowBits` 和一个非 NULL 的窗口成功初始化，窗口有 `2^windowBits` 个可写字节，并且是某个堆字节块的一段。对这个调用的结论：在每段这样的历史上，它返回 `Z_OK`，清空状态指针，只写流记录和状态块，并且恰好释放状态块。这个函数的拒绝情形在功能目标里。功能目标（非必需）：`Goal.inflateBackEnd`。

<details markdown="1" class="ar-return-exact" data-return-exact="inflateBackEnd"><summary>完整返回条件与边界</summary>

**后置条件。** `Z_OK` 使 `state` 为 NULL。调用者的窗口及其他所有流字段不变。
调用者此时可释放或复用窗口；库从不释放它。

**错误。** NULL `strm`、NULL 状态或 NULL `zfree` 返回 `Z_STREAM_ERROR`，不释放任何内存。
这些检查不会验证任意非 NULL 状态，也不会检测所有权错误。

[返回 API 手册](README.md) · [契约约定](contracts.md)

</details>

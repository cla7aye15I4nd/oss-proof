<!-- source-sha256: 0bdcab58e82ffe293fbc27da81aeae29ed1532f21425e9a78d956a09af2db493 -->
# 缓冲区工具函数：源码上的决定

本页列出 `compress.c`、`uncompr.c` 以及 `deflate.c` 的上界函数中，C 的做法需要模型小心表示的地方。每一处都说明 C 做了什么，模型做了什么，以及是否有定理覆盖它。这些函数的安全证明在另外两页；本页是它们的源码阅读配套页。

[API 契约](../spec/api/utility.md)给出调用者的义务。术语见[术语表](../glossary.md)。

## 结果在哪里

| 函数 | 安全定理（必需） | 页面 |
| --- | --- | --- |
| `compress`、`compress_z`、`compress2`、`compress2_z` | `compress_safety`、`compress_z_safety`、`compress2_safety`、`compress2_z_safety`（`ZlibF/Proof/public-compress-safe-mid.lean`） | [`compress*` 的安全性](compress-safety.md) |
| `uncompress`、`uncompress_z`、`uncompress2`、`uncompress2_z` | `uncompress_safe`、`uncompress_z_safe`、`uncompress2_safe`、`uncompress2_z_safe`（`ZlibF/Proof/public-uncompress-safe.lean`） | [`uncompress*` 的安全性](uncompress-safety.md) |
| `deflateBound`、`deflateBound_z` | `deflateBound_safety`、`deflateBound_z_safety`（`ZlibF/Proof/public-stream-call-safety.lean`） | [流压缩](deflate.md) |
| `compressBound`、`compressBound_z` | `compressBound`、`compressBound_z`（`ZlibF/Proof/public-compress-bound.lean`）：公式的精确值。这两个函数不读内存，所以清单把这两个完整契约用作它们的安全目标 | [`compress*` 的安全性](compress-safety.md#the-bound-functions) |

这些定理[已登记](../checking/README.md)，并[已在提交 `bde170e9` 上验收](../checking/README.md)（[进度，Scope 一节](../progress.md#scope)）。这些函数的功能契约，例如 `uncompress` 写出的字节，或者压缩器的每个输出都不超过上界，不是安全结果所必需的。

对 C 的某种读法如果没有定理陈述，就标为**尚未由证明确认**。

## 各项决定

### 局部流是自动存储

- **C。** `compress2_z` 和 `uncompress2_z` 把 `z_stream stream;` 声明为局部变量。创建它不会失败，也不是对分配器的调用。
- **模型。** 局部流是由 `allocLocalZ` 建立的一条新分配的记录。它不消耗分配失败预言的一次调用，也不移动库自身各次分配的序号。每次返回之前它都被释放。被取了地址的标量局部变量按同样的方式处理。
- **状态。** 已覆盖：安全定理带着这个局部变量运行翻译，并证明没有任何东西仍处于已分配状态。[分配回归测试](../../tests/regression/compress-allocation/README.md)对每一个失败的分配序号，把返回码、存入的长度、分配尝试次数和存活块与 C 作比较。那是证据，不是证明。

### 包装函数在调用 `_z` 之前读取长度单元

- **C。** `compress2` 在调用 `compress2_z` 之前执行 `z_size_t got = *destLen;`。`uncompress2` 以同样的方式读取 `*destLen` 和 `*sourceLen`。`_z` 函数内部的 `NULL` 测试来得太晚，保护不了这些读取：`NULL` 单元在包装函数里就是未定义行为。
- **模型。** 在 `compress2`、`compress`、`uncompress2` 或 `uncompress` 中，`NULL` 单元是 `Fault.ub`。
- **状态。** 这四个函数的安全目标取非 `NULL` 的单元；`_z` 形式接受 `NULL`，并以 `Z_STREAM_ERROR` 拒绝它。`zlib.h` 没有为包装函数提供 `NULL` 单元。分配回归测试里有一个演示这次读取的见证程序；带 `NULL` 单元的调用不是比较中的一行，因为它不是合法调用。

### `compress*` 的长度单元是值，不是内存

- **C。** `destLen` 指向调用者的一个单元。`compress2_z` 读取它，并在结束时通过它存入输出长度。
- **模型。** 翻译接收 `*destLen` 的值（`NULL` 对应 `none`），并把存入的值作为第二个结果返回（[翻译](../design/translation.md#the-accepted-normalisations)）。这个单元不是内存。
- **状态。** 这限制了安全目标：与源缓冲区或目的缓冲区重叠的长度单元无法表达，所以这样的调用在定理之外。[偏离记录](../deviations.md)的 “整缓冲区压缩” 一行记录了这一点。`uncompress*` 的长度单元是内存，是八字节的块；它们与各缓冲区分离、彼此也分离，是一条显式前提（“计数解压” 一行）。

### `compress2_z` 中容量为零的 `NULL` 目的缓冲区

- **C。** `dest == NULL` 且 `*destLen == 0` 能通过参数检查。函数在结束时计算 `stream.next_out - dest`，两个指针都是 `NULL`。
- **模型。** 一般的指针差 `Ptr.diff` 在 `NULL` 上产生故障。这一条语句的翻译使用 `ptrDiff`，它对 `NULL - NULL` 返回 0（`ZlibF/Zlib/compress.c.lean`）。
- **状态。** 安全定理是对带有这一放宽的翻译证明的。对于选定的构建，C 语言是否定义了 `NULL - NULL`，**尚未由证明确认**；结果相等和 sanitizer 没有报告都不能定论。它是可信基础中的一项，不是一个未证明的证明步骤（[安全，空指针](../spec/safety.md#null-pointers-and-pointer-differences)）。

### `uncompress2_z` 的占位输出指针

- **C。** 对于 `dest == NULL` 且 `*destLen == 0`，函数令 `dest = (Bytef *)&stream.reserved`，因为 `next_out` 不可以是 `NULL`。这个指针只会在 `avail_out == 0` 时作为 `next_out` 传递。
- **模型。** 占位对象是一个单独的八字节局部块，每次返回之前都被释放。模型不表示它是流记录的一部分。
- **状态。** `uncompress2_z_safe` 对翻译覆盖了这种情形。**尚未由证明确认**：在 `avail_out == 0` 时解码器不通过 `next_out` 写任何东西，所以记录的一个字段与一个单独的块之间的差别无法被观察到。

### 循环用 64 位长度补充 32 位计数

- **C。** `avail_in` 和 `avail_out` 是 `unsigned`；剩余长度是 `z_size_t`。每一轮循环给空了的计数补充至多 `(uInt)-1` 个字节。循环只在 `Z_OK` 时继续。初始化成功之后会运行 `deflateEnd` 或 `inflateEnd`，返回码在最后被映射。
- **模型。** 翻译逐条保留这些语句。
- **状态。** 由安全定理覆盖；它们的终止度量在两个安全页上。解码器较晚的内存失败可能出现在已经写出一些输出之后：`uncompress*` 的安全目标允许 `Z_MEM_ERROR` 伴随非空的输出。

### `compressBound_z`：回绕的加法与饱和

- **C。** 公式使用回绕的 `z_size_t` 加法，并在和发生回绕时返回最大值。
- **模型。** `UInt64` 上的一个纯函数。
- **状态。** `compressBound` 和 `compressBound_z` 对每个输入证明了精确值。压缩器的每个输出都不超过上界，是另一条单独的功能陈述，安全结果用不到它。

### `deflateBound_z`：`2 + extra_len` 按 32 位计算

- **C。** `deflateBound_z` 读取包装状态和可选的 gzip 头字符串；每次字符串扫描都包含结尾的 NUL。对于 extra 字段，它把按 32 位 `unsigned` 求值的 `2 + extra_len` 加到 64 位的包装开销上。当 `extra_len >= 0xfffffffe` 时这个和会回绕，而头部写入函数只输出 `extra_len & 0xffff` 个字节。
- **模型。** 翻译计算同一个回绕的和。
- **状态。** 安全性已覆盖（`deflateBound_safety`、`deflateBound_z_safety`）。这一点关系到上界的值，不关系到安全。当 `extra_len` 为 `2^32 - 2` 和 `2^32 - 1` 时上界偏小；这已在 C 上复现（[发现](../findings/deflatebound-extra-len/README.md)）。有人在一次[上游讨论](https://github.com/madler/zlib/pull/1360)中提出用 `2 + (z_size_t)(extra_len & 0xffff)` 来修正；没有为它应用补丁（`patches/README.md` 列出了各补丁）。输出是否不超过上界是功能问题，安全结果用不到它。另一项发现给出了一种输出超过上界的配置：[级别 1 到 3 的 `Z_FIXED`](../findings/deflatebound-fixed-far-matches/README.md)。**尚未由证明确认**：在源数据和头部定义域的其余部分上，输出不超过上界。

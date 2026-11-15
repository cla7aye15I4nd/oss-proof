<!-- source-sha256: ba19c0ae522fea944bc790cd9eef9baff22446ef94729e6c0da8d5bb2d6818aa -->
# 流式解码：`inflate` 为什么是安全的

源文件：`zlib/inflate.c`。翻译：`ZlibF/Zlib/inflate.c.lean`。

`inflate` 和其他 `inflate*` 函数，对任意输入、对输入输出缓冲区的任意切分、在任意一串被允许的调用上，都是安全的。证明维护解码器状态的一个不变量：`inflateInit2_` 建立它，每次调用保持它，而 C 代码的每一次内存访问都落在不变量描述的范围之内。本页解释这个不变量、每一步为什么保持它，以及解码循环为什么会结束。

本页以[解码表](inftrees.md)和[快速解码](inffast.md)为基础。翻译怎样跟随 C 的细节，见[解码器的源码笔记](inflate-source-notes.md)。`updatewindow` 的内部契约是[内部契约](../spec/internal-contracts.md)中的 `I-uw-*`。

## 结论

除非某一行另有说明，下面的定理都已登记在 `tests/audit/theorems.txt` 中，并在提交 `bde170e9` 上已验收。层级的定义见[证明地图](README.md#status-levels)。

| 目标 | 内容 | 定理 | `ZlibF/Proof/` 下的模块 |
| --- | --- | --- | --- |
| `Goal.inflate_sequence_safety` | 序列结论，见下 | `inflate_sequence_safety_public` | `public-inflate-sequence-safety.lean` |
| 十个目标：`Goal.inflate_safety`、`Goal.inflateSetDictionary_safety`、`Goal.inflateGetDictionary_safety`、`Goal.inflateSync_safety`、`Goal.inflateReset_safety`、`Goal.inflateReset2_safety`、`Goal.inflatePrime_safety`、`Goal.inflateMark_safety`、`Goal.inflateGetHeader_safety`、`Goal.inflateEnd_safety` | 在可达的流上调用一次该函数是安全的 | `inflate_safety` 以及形式相同的另外九条 | `public-stream-call-safety.lean` |
| `Goal.inflateInit__safety`、`Goal.inflateInit2__safety` | 对 `zlib.h` 允许的每一组参数，初始化都是安全的 | `inflateInit__safety`、`inflateInit2__safety` | `public-init-safety.lean` |
| `Goal.inflateCopy_safety` | `inflateCopy` 是安全的 | `inflateCopy_safety` | `public-inflate-copy-safety.lean` |
| `Goal.inflate_refusal` | 见[拒绝](#refusals) | `inflate_refusal` | `public-stream-refusal.lean` |
| `Goal.inflate_initialisation_domain` | 序列目标的前提可以被满足（非空性） | `inflate_initialisation_domain_public` | `public-inflate-init.lean` |

这些目标写在 `ZlibF/Spec/Safety/` 中：`Sequences.lean`、`Streams.lean`、`Initialisation.lean`、`Copy.lean`、`Refusals.lean` 和 `Domains.lean`。

**序列结论**有三部分（`StreamSequenceSafety`，`ZlibF/Spec/Public/Sequences.lean`）。

1. 每个可达的流都满足公开不变量 `StreamInvariant`。
2. 在可达的流上，再做一次被允许的调用，调用会返回且不出故障。之后不变量仍然成立。调用只改动了流记录、流拥有的块、挂接的 `gz_header` 记录，以及交给它的调用者区域（这是它的*帧*）。存活块集合的变化，恰好是流新得到或释放掉的块（这是*分配账本*）：没有任何泄漏。
3. 在可达的流上调用 `inflateEnd`，返回 `Z_OK`，并释放流拥有的每一个块。

一个流是*可达*的，指它来自一次成功的 `inflateInit2_`，之后经过任意多次被允许的调用、成功的 `inflateCopy` 调用，以及调用者对四个缓冲区字段的修改。各函数的定理就是第 2 部分在一个函数上的情形，它们是序列定理的推论。

`inflate_sequence_safety_public` 由 `inflate_sequence_safety`（`inflate.c.sequence-safety.lean`）推出，后者已检查而未登记。

这个文件也有功能结论。它们不是安全结论所必需的，列在[功能结论](#functional-results)一节。

## 拒绝

*被拒绝*的流（`RefusedInflate`）是 `NULL`，或者是一个可读但被状态检查 `inflateStateCheck` 拒绝的记录。`Goal.inflate_refusal` 覆盖七个函数：`inflate`、`inflateEnd`、`inflateReset`、`inflateReset2`、`inflateGetDictionary`、`inflateSetDictionary` 和 `inflateCopy`。在被拒绝的流上，它们都返回 `Z_STREAM_ERROR`，不出故障。

- `inflate` 不改动它的帧之外的任何东西，也不分配。
- `inflateCopy` 把目的流的 `state` 字段置为 `NULL`。
- 其余五个函数让堆保持原样。

`state` 字段里是垃圾指针的记录不在这个结论之内；原因见[偏离记录](../deviations.md)中“被拒绝的流”一行。其他 `inflate*` 函数的拒绝情形，在它们的功能目标里，或者在已登记但不属于必需目标的引理里，例如 `inflateSync_check`。

## 假设

下面是序列目标和各函数目标（`StreamCallDomain`）的全部前提。每一条在[偏离记录](../deviations.md)中都有一行。

| 前提 | 内容 | 属于 |
| --- | --- | --- |
| 可达的流（`StreamReachable .inflate`） | 历史从一次成功的 `inflateInit2_` 开始：堆是良构的，`zalloc` 和 `zfree` 各自是 `NULL` 或默认函数，版本字符串的第一个字符是 `1`，结构体大小是 112 | 每个目标 |
| 调用者的修改（`Rebuffer`） | 两次调用之间，调用者只改 `next_in`、`avail_in`、`next_out`、`avail_out`，以及不属于流的内存 | 历史 |
| `ByteObjectsFit` | 每个字节对象都少于 `2^63` 字节 | 每次调用 |
| `StreamBuffers` | 输入区域和输出区域在各自的长度内可读、可写，两者互不重叠，并且在流拥有的块之外 | `inflate` |
| `ActiveHeader` | 挂接的 `gz_header` 记录以及它的 `extra`、`name`、`comment` 缓冲区是存活的，并在声明的容量内可写。读取头部期间，`extra` 与尚未读的输入互不重叠，`extra_len` 不小于还要读的长度（`InflateHeaderProgress`） | `inflate` |
| 字典区域（`CallerRange`） | 字典缓冲区是 `NULL`，或者可读（对 `inflateGetDictionary` 要可写）并且在流拥有的块之外 | 两个字典调用 |
| 同步输入 | `next_in` 为 `NULL` 且 `avail_in = 0`，或者是流的块之外的一段可读区域 | `inflateSync` |
| 头部记录 | 交给 `inflateGetHeader` 的记录不是 `NULL`，它的缓冲区可写 | `inflateGetHeader` |

默认分配器不是单独的前提：它由历史推出，并由不变量携带（子句 `alloc`）。

有 `InflateHeaderProgress` 这条前提，是因为缺了它 C 会出故障。在 `EXTRA` 模式里，C 往 `head->extra + extra_len - length` 处复制。`extra` 缓冲区若与输入重叠，就是一次重叠的 `memcpy`；调用者若在读头部的中途把 `extra_len` 调小，这个偏移就会回绕（`tests/regression/inflate-gzip-extra`）。

## 一次调用的轮廓

```c
int inflate(z_streamp strm, int flush) {
    /* 入口检查：state、next_out、next_in */
    LOAD();                       /* 取出 next_in、avail_in、next_out、avail_out、hold、bits 的本地副本 */
    for (;;) switch (state->mode) {
        case HEAD: ...            /* 每个 case 读若干位、写输出，或者改变模式 */
        case LEN:
            if (have >= 6 && left >= 258 && bits < 8) {
                RESTORE(); inflate_fast(strm, out); LOAD(); break;
            }
            ...                   /* 否则在这里解码一个符号 */
        case DONE: ret = Z_STREAM_END; goto inf_leave;
        ...
    }
  inf_leave:
    RESTORE();                    /* 把本地副本写回 */
    updatewindow(...);            /* 把输出的末尾保存为历史 */
    ...
}
```

一次调用可以经过许多模式，快速路径和慢速路径可以交替出现。一次调用还可能在任何地方停下：输入用完时，`NEEDBITS` 经 `inf_leave` 离开，下一次调用从同一个模式继续。所以不变量必须描述每一个模式下的状态，而不只是块与块之间的状态。

```mermaid
stateDiagram-v2
    state "头部" as Header
    state "字典" as Dictionary
    state "块类型" as Type
    state "存储块" as Stored
    state "建表" as Tables
    state "符号" as Symbols
    state "尾部校验" as Check
    state "完成" as Done
    state "数据错误" as Bad
    [*] --> Header
    Header --> Dictionary: FDICT
    Header --> Type: 头部读完
    Dictionary --> Type: 字典已设置
    Type --> Stored: 存储块
    Type --> Tables: 动态块
    Type --> Symbols: 固定块
    Tables --> Symbols: 表已安装
    Stored --> Type: 块结束
    Symbols --> Symbols: 字面量或匹配
    Symbols --> Type: 块结束符
    Type --> Check: 最后一块结束
    Check --> Done
    Header --> Bad: 格式错误
    Tables --> Bad: 格式错误
    Symbols --> Bad: 格式错误
    Done --> [*]
    Bad --> [*]
```

图里把模式分了组。证明对 C 中每个真实的模式各有一个情形。

## 内存与所有权

```mermaid
flowchart LR
    Stream["z_stream（调用者的）"] --> State["inflate_state（流拥有）"]
    State --> Window["窗口，2^wbits 字节（流拥有，首次使用时分配）"]
    State --> Codes["lens、work、codes（在状态内部）"]
    State --> Fixed["固定表（静态，只读）"]
    State --> Header["gz_header 及其缓冲区（调用者的）"]
    Stream --> Input["输入区域（调用者的）"]
    Stream --> Output["输出区域（调用者的）"]
```

流拥有两个块：它的状态，以及分配之后的窗口。`lens[320]`、`work[288]` 和 `codes[1444]` 是状态内部的数组。`lencode` 和 `distcode` 指向 `codes` 内部，或者指向静态的固定表。`head` 指向调用者拥有的记录。

## 不变量

不变量是 `InflateInv`（`ZlibF/Proof/inflate.c.invariant.lean`），有十二个子句。写这张表时，最后一列里的定义都读过。

| 子句 | 白话说明 | 定义 |
| --- | --- | --- |
| `good` | 流记录可读，它的 `state` 是一个存活的 inflate 状态，并且指回这个流。状态里各数组的大小与 C 声明一致。窗口具有下面的形状 W。`bits ≤ 39`。`next` 指向 `codes` 内部，下标不超过 1444。`lencode` 和 `distcode` 要么都指向 `codes` 内部，要么就是那两张固定表。一个块编号不会同时表示两个对象 | `Good`（`inflate.c.base.lean`） |
| `alloc` | `zalloc` 和 `zfree` 是默认函数 | `DefAlloc` |
| `tables` | 在 `LEN_`、`LEN`、`LENEXT`、`DIST`、`DISTEXT`、`MATCH` 和 `LIT` 模式下：`lencode` 和 `distcode` 指向的表，对 `lenbits` 和 `distbits` 具有安全的表形状（[解码表](inftrees.md#the-table-shape)），并且每个字面量/长度叶子至少用掉一位 | `DataTableInvariant` |
| `pending` | `sane = 1`。在 `LENEXT` 中：附加位至多 5 位，`3 ≤ length`，`length + 2^extra ≤ 259`。在 `DIST` 和 `DISTEXT` 中：`3 ≤ length ≤ 258` 且 `was = length`；在 `DISTEXT` 中还有附加位至多 13 位、`offset ≥ 1`。在 `MATCH` 中：`0 < length ≤ was ≤ 258` 且 `offset > 0` | `DataPendingInvariant` |
| `lengths` | 在 `CODELENS` 中：`lencode` 就是 `codes[0]`，是一张形状安全的码长表；`nlen ≤ 286`，`ndist ≤ 30`，`have ≤ nlen + ndist`；已经读到的 `have` 个码长都不超过 15 | `CodeLengthInvariant` |
| `headerLengths` | 在 `LENLENS` 中：`ncode ≤ 19`，`have ≤ ncode`，`nlen ≤ 286`，`ndist ≤ 30`；已经写入的 `have` 项都是 3 位的值 | `LengthHeaderInvariant` |
| `held` | `hold < 2^bits`：位计数以上没有置位的位 | |
| `config` | `wrap` 和 `reqwrap` 取 0、1、2、3、5、6、7 之一。`wbits` 是 8 到 15；或者是 0，这时没有窗口，头部还没读，模式是 `HEAD`、`BAD`、`MEM` 或 `SYNC`。只有允许 gzip 解码时才会挂接 `gz_header` | `InflateConfig` |
| `modes` | `HEAD ≤ mode ≤ SYNC` | |
| `phase` | 只有读过头部之后，或者在 raw 模式下，才会进入块模式。gzip 头部模式 `FLAGS` 到 `HCRC` 只在允许 gzip 解码时出现 | `InflatePhase` |
| `origin` | `lencode` 是 `codes[0]`，或者 `lencode` 和 `distcode` 是那两张固定表。两次调用之间不会存下别的形状 | `CopyTableOrigin` |
| `globals` | 静态表（固定编码、CRC、`trees.c` 的表）保持初始内容 | `LibraryGlobals` |

有三个子句描述中途停下的调用：`pending`（停在一次匹配当中）、`lengths`（停在码长序列当中）和 `headerLengths`（停在码长编码的头部当中）。下一次调用靠它们才能继续。

还有一条事实在两次调用之间成立，它放在不变量旁边，叫 `DecoderHeldBits`：在 `BAD`、`MEM` 和 `SYNC` 之外，`bits ≤ 32`。在一次调用内部 `bits` 可以达到 39：`n ≤ 32` 的 `NEEDBITS(n)` 只在 `bits < n` 时才取一个字节，所以取字节时 `bits ≤ 31`，取完至多是 39。

序列目标陈述的是较小的公开谓词 `StreamInvariant`，也就是 `good` 和 `alloc` 两个子句。`InflateInv` 蕴含它。

### 窗口形状 W

W 是 `good` 中关于滑动窗口的部分（`WinInv`）。

1. `wbits ≤ 15`。
2. `window` 是 `NULL`，或者指向一个恰好 `2^wbits` 字节的可写块的开头。`window` 为 `NULL` 时 `wsize = 0`。
3. `wsize` 是 0 或 `2^wbits`。
4. `whave ≤ wsize`。`wnext < wsize`，或者两者都是 0。
5. 如果 `whave < wsize`，那么 `wnext = whave`：还没填满的窗口是从下标 0 开始填的。

W 说明对窗口的读写落在哪里，不涉及窗口里的字节是什么。

`updatewindow(strm, end, copy)` 保存最后 `copy` 个输出字节。它有三种情形。下面取 `wsize = 8`，`h` 表示旧字节，`n` 表示新字节：

```
copy >= wsize                 [ n n n n n n n n ]   wnext = 0   whave = 8

copy <= wsize - wnext         [ h h h . . . . . ]   wnext = 3   whave = 3
(copy = 2)                    [ h h h n n . . . ]   wnext = 5   whave = 5

copy >  wsize - wnext         [ h h h h h h . . ]   wnext = 6   whave = 6
(copy = 4)                    [ n n h h h h n n ]   wnext = 2   whave = 8
```

- 第一种情形：一次 `wsize` 字节的 `memcpy` 填满整个块。
- 第二种情形：一次 `memcpy` 写到 `[wnext, wnext + copy)`，它的终点不超过 `wsize`。然后 `wnext` 前进，到 `wsize` 时回到 0。如果窗口原先没满，W.5 给出 `whave = wnext`，所以给 `whave` 加上同样的数，W.5 仍然成立。
- 第三种情形：第一次 `memcpy` 把 `wsize - wnext` 字节写到块的末尾，第二次把剩下的写到下标 0 处。之后窗口是满的。

`updatewindow_safe`（`inflate.c.uw.lean`，已登记）证明这个调用不会出故障，并且之后 `Good` 仍然成立。如果需要分配窗口而分配失败，调用返回 1，状态不变，只有分配计数前进了。

## 每一步为什么保持不变量

`reachable_invariant_kind`（`inflate.c.reachable.lean`）对历史做归纳，证明每个可达的流都满足 `InflateInv` 和 `DecoderHeldBits`。归纳的每个情形是一条定理。

| 步骤 | 定理 | 为什么成立 |
| --- | --- | --- |
| `inflateInit2_` 成功 | `inflateInit2_invariant_of`、`inflateInit2_held` | 状态先被清零，然后 `inflateReset2` 设置 `wrap` 和 `wbits`，`inflateResetKeep` 设置 `mode = HEAD`、`hold = 0`、`bits = 0`、`lencode = distcode = next = codes`。窗口是 `NULL`，`wsize = 0` |
| 调用者修改缓冲区字段 | `rebuffer_invariant` | 没有哪个子句提到 `next_in`、`avail_in`、`next_out` 或 `avail_out`，调用者也不能碰流拥有的块 |
| `inflate` | `inflate_preserves`，来自 `inflate_call` 和 `inflate_call_refused` | 见下 |
| `inflateReset`、`inflateReset2`、`inflateResetKeep` | `inflateReset_preserves`、`inflateReset2_preserves`、`inflateResetKeep_preserves` | 三者都重置模式和位缓冲。`inflateReset` 还清空窗口计数，但保留窗口块。只有 `windowBits` 改变时的 `inflateReset2` 才释放窗口；这时账本记下这次释放 |
| `inflatePrime` | `inflatePrime_preserves` | 位数大于 16 或合计大于 32 时它拒绝，所以 `bits ≤ 32` 和 `held` 仍然成立 |
| `inflateSetDictionary`、`inflateGetDictionary` | `inflateSetDictionary_preserves`、`inflateGetDictionary_preserves` | 前者经过 `updatewindow`；后者只读窗口 |
| `inflateSync` | `inflateSync_preserves` | 它扫描输入，找到标记后通过 `inflateReset` 重置 |
| `inflateGetHeader`、`inflateMark` 和未写入文档的查询函数 | `inflateGetHeader_preserves`、`inflateMark_preserves` 等 | 它们只写一两个不受任何子句约束的字段，或者什么都不写 |
| `inflateCopy` 成功 | `inflateCopy_invariant` | 副本得到自己的状态块和窗口块。子句 `origin` 说明了 `lencode` 可能是什么，所以副本可以照同样的方式指向自己的表 |

`operation_preserves` 汇总了流调用的各行。序列结论的第 2 部分还需要每次调用的帧和账本，它们是 `inflate_call_safe` 和 `operation_safe_other`（`inflate.c.sequence-safety.lean`）。第 3 部分是 `inflateEnd_invariant`。

### 一次 `inflate` 调用的内部 {#the-mode-proof}

`inflate_call`（`inflate.c.call-default.lean`）处理通过了入口检查的调用。`inflate_call_refused` 处理在入口处返回 `Z_STREAM_ERROR` 的调用。前者除了安全性之外，还证明了返回码和各计数更新的完整清单；安全性只用到其中一部分。

下表对每组模式说明：哪次访问需要论证，哪条事实提供了论证。

| 模式 | 需要论证的访问 | 为什么安全 |
| --- | --- | --- |
| 每个 `NEEDBITS`、`PULLBYTE` | 读 `*next`；移位 `<< bits` | 读之前先检查 `have > 0`。移位发生在 `bits ≤ 31` 时 |
| `HEAD` 到 `HCRC` | 写 `head->extra`、`head->name`、`head->comment` | 每次写都受容量 `extra_max`、`name_max` 或 `comm_max` 约束，而 `ActiveHeader` 保证这些容量内可写。`extra` 的偏移用到 `InflateHeaderProgress` |
| `STORED`、`COPY` | 从输入到输出的 `memcpy` | `copy = min(length, have, left)` 限定了两段区域；`StreamBuffers` 保证它们不重叠 |
| `TABLE` | 之后的下标 `lens[have]` | C 拒绝 `nlen > 286` 或 `ndist > 30`，所以 `nlen + ndist ≤ 316 < 320` |
| `LENLENS` | `lens[order[have]]`，以及对 `inflate_table` 的调用 | `have < ncode ≤ 19`。19 个码长都是 3 位的值，这正是 [`inflate_table`](inftrees.md#assumptions) 对 `CODES` 的前提 |
| `CODELENS` | 查表、`lens[have++]`、`lens[have - 1]` | 子句 `lengths`。会超过 `nlen + ndist` 的重复被拒绝。`have = 0` 时的代码 16 在访问 `lens[have - 1]` 之前被拒绝 |
| `CODELENS` 的末尾 | 两次调用 `inflate_table`，写入 `codes[1444]` | `852 + 592 = 1444`。`inflate_table_safe` 给出无故障；`inflate_table_decoder_safe` 给出子句 `tables` 需要的表形状 |
| `LEN` 到 `DISTEXT` | 查表 | 子句 `tables`：掩码后的下标在表内，表项是叶子，或是通向叶子的链接 |
| `LEN`，快速路径 | 对 `inflate_fast` 的调用 | `inflate_fast_raw_entry`（`inflate.c.fast-entry.lean`）由不变量和 `StreamBuffers` 建立[快速解码](inffast.md#assumptions)的入口条件 |
| `MATCH` | 从窗口或更早的输出复制 | `offset > 0`（子句 `pending`）。距离超出本次调用的输出时去读窗口；因为 `sane = 1`，距离超过 `whave` 时 C 会拒绝。W 限定了窗口下标 |
| `LIT` | 往 `*put` 写一个字节 | 先检查 `left > 0` |
| `CHECK`、`LENGTH` | 对本次调用的输出计算校验和 | 这些字节是本次调用写的，在输出区域之内 |
| `inf_leave` | 对本次调用的输出执行 `updatewindow` | 源是输出区域，`StreamBuffers` 保证它与窗口不重叠 |

<a id="table-and-trailer-statement-boundaries"></a>
各个模式的运行引理已登记，例如 `inflate_TABLE_run`、`inflate_LENLENS_run` 和 `inflate_CHECK_run`。表模式和尾部模式的引理假设了什么，见[源码笔记](inflate-source-notes.md#statements-of-the-table-and-trailer-lemmas)。

## 循环为什么会结束

分派循环 `for (;;) switch (state->mode)` 在 C 里没有界。它会结束，是因为每一轮只要不离开循环，就有一个秩在下降（`ZlibF/Proof/inflate.c.dispatch-rank.lean`）。

```
mass = bits + 8 * have + left
rank = 64 * mass + credit(mode)
```

`mass` 数的是还可用的输入位数和还空着的输出字节数。`credit` 对每个模式是一个小于 64 的固定数：`HEAD` 60，`STORED` 48，`TABLE` 47，`LENLENS` 46，`CODELENS` 45，`LEN` 21，`LIT` 20，`TYPE` 8，`CHECK` 4，`DONE` 2，等等。

- 没有哪一轮会让 mass 增加：位从 `have` 移到 `bits`，然后被丢弃（`dispatchMass_advance`）。
- 写了输出或丢弃了输入位的一轮，使 `mass` 至少减一。一个单位的 mass 值 64，比 credit 的任何变化都大。
- 两样都没做的一轮，会转到 credit 更小的模式（`dispatchRank_advance`）。两个例子：raw 流上的 `HEAD`（60）什么都不读就转到 `TYPEDO`（9）；存储块结束时的 `COPY`（17）转到 `TYPE`（8）。

每组模式都有一条引理，说“要么离开，要么秩下降”：`inflate_dispatch_data_rank`、`inflate_dispatch_type_rank`、`inflate_dispatch_stored_rank`、`inflate_dispatch_gzip_header_rank` 以及同类的其他引理（`inflate.c.control-rank.lean` 和它旁边的模块）。快速路径算作一轮：`inflate_fast_safe_progress` 说明，没有结束当前块的一次快速调用用掉了输出空间。

翻译里的循环带有 `2^64` 轮的燃料，燃料耗尽是故障。由于 `bits ≤ 39`，而 `have` 和 `left` 是 32 位的，秩小于燃料（`dispatchRank_fuel`），所以这种故障不会发生。

内层循环直接有界：存储块的复制受 `copy` 约束，码长循环受 `nlen + ndist - have` 约束，匹配复制受 `length` 约束，`syncsearch` 受输入长度约束。

## 难点在哪里

难点不在某一个循环。难在一次调用可以在任何一个 `NEEDBITS` 处停下再继续，所以不变量必须在大约三十个模式中的每一个里都足够强，同时又能被每一个模式重新建立。有三处花的功夫最多。

- **gzip 头部。** 这是 `inflate` 往输出之外的调用者缓冲区里写东西的唯一地方。对某些调用者布局，真实的 C 在这里会出故障，所以才有前提 `InflateHeaderProgress` 和它的 sanitizer 回归测试。
- **终止性。** 有几种转移既不用输入也不写输出。只看输入和输出的度量在这些地方不会下降；秩里的 credit 项处理的就是它们。
- **快速路径。** `inflate_fast` 的入口条件比它周围的模式更严。这些条件要在 `RESTORE()` 留下的堆上，从同一个不变量建立起来，包括输入和输出是同一个块里两段区域的情形。

## 没有定理陈述的 C 解读

- 匹配从窗口读到的字节是先前写过的。原因是 W.5：在没有填满的窗口里，有效历史是 `[0, whave)`，而 C 会拒绝超过 `whave` 的距离。定理只陈述了读落在块内。在模型里，读一个从未写过的字节会得到任意值，不算故障（[可信基础](../trusted-base.md)）。**尚未由证明确认**。
- 窗口里按顺序存着输出和字典最近的 `whave` 个字节。这是关于含义的事实，安全性不需要它，也没有安全定理陈述它。**尚未由证明确认**。

- 状态的每个指针字段在被读之前都写过。`inflateInit2_` 和 `inflateCopy` 在使用新状态之前先用 `zmemzero` 把它清零。模型自己说明不了这一点：在模型里，新分配的内存中的指针字段读出来是 `NULL`，不出故障（[安全性](../spec/safety.md#uninitialised-memory)）。**尚未由证明确认**。

更多这类解读，即翻译怎样跟随 C 的各条语句，见[源码笔记](inflate-source-notes.md)。

## 功能结论

这些结论说的是函数算出了什么。它们已登记，但不是安全结论所必需的。

| 结论 | 定理 | 模块 |
| --- | --- | --- |
| `Goal.inflate`：一次调用的完整契约，包括进展、返回码、计数、帧和所有权。`uncompress*` 和 gzip 读取端的安全证明用到它 | `inflate_public` | `public-inflate.lean` |
| 其他函数的完整契约，例如 `Goal.inflateCopy`、`Goal.inflateReset`、`Goal.inflateSetDictionary` | `inflate_copy_public`、`reset_public`、`inflateSetDictionary_public` 等 | `public-inflate-*.lean` |

没有定理说 `inflate` 的输出等于输入在 DEFLATE 格式下的含义。`inflate_decodes` 只是关于抽象模型的命题。

### 跨调用的因果关系与历史

这一小节记录对早先两条关于含义的命题所做的修正。两者都不是 zlib 的缺陷。

一个解码出的符号由输入位的一段前缀支撑。解码器可能已经读得更远：`inflate_fast` 会提前取入整字节，再把没用到的还回去。早先有一条命题要求输出与解码器读过的全部内容一致。这是错的，因为提前读入的字节可能格式有误，而已经解码的符号是有效的。修正后的关系只把每个符号与支撑它的那些位联系起来。它登记为 `inflate_deferred_distance` 和 `inflate_deferred_distance_rejects_legacy_consistency`，回归测试是 `tests/regression/inflate-deferred-distance`。

早先的第二条命题说，数据错误会在它的起因之后八个字节以内被发现。它有反例，把常数调大也修不好。依赖它的模型目标 `Api.Goal.inflate_rejects_invalid` 不在计划内（[进度，范围](../progress.md#scope)）。

错误可能出现在真实的输出之后：窗口是在调用结束时分配的，所以 `inflate` 可能在写出一些字节之后返回 `Z_MEM_ERROR`。`Goal.inflate` 保留了这种效果。

关于跨调用的功能命题需要涵盖什么（字典、预置位、恢复），早先的笔记保存在[历史](../history/proof-functional-notes.md)中。

## 在 `inflateCopy` 中发现的缺陷

未打补丁的 `inflateCopy` 用 `>=` 和 `<=` 来判断 `lencode` 是否落在 `codes` 之内。当 `lencode` 指向静态固定表时，这两个指针属于不同的对象，这种比较是未定义行为。补丁 0001 把它换成了指针相等的判断（`patches/README.md`；[发现与 sanitizer 复现](../findings/inflate-copy-fixed/README.md)）。翻译和 `inflateCopy_safety` 针对的都是打过补丁的源码。

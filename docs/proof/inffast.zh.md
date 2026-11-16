<!-- source-sha256: 56ec28319b26916cec2dc24e1d3883593f2c73b687e334681556bf4d9cc6b55a -->
# 快速解码：`inflate_fast` 为什么是安全的

源文件：`zlib/inffast.c`。翻译：`ZlibF/Zlib/inffast.c.lean`。

`inflate_fast` 解码字面量和匹配时，并不在每次读写时检查输入和输出是否还有剩余。它之所以安全，是因为调用者只在至少有 6 个输入字节和 258 个输出字节时才进入它，而它的循环每一轮至多读 6 个字节、至多写 258 个字节。本页列出定理假设的入口条件，给出循环不变量，并解释这两个界。

`inflate_fast` 是内部函数。调用它的是 `inflate`（[流式解码](inflate.md)）和 `inflateBack`（[回调解码器](callbacks.md)）。翻译怎样跟随 C 的细节，见[解码器的源码笔记](inflate-source-notes.md#inffastc)。

## 结论

| 结论 | 定理 | `ZlibF/Proof/` 下的模块 |
| --- | --- | --- |
| `Goal.fast_safe`（`ZlibF/Spec/Common/Inflate/InflateFast.lean`）：在入口条件下，调用返回且不出故障；后置条件 `FastPost` 准确说明了改动了什么 | `inflate_fast_safe` | `inffast.c.final.lean` |
| 循环的一轮是安全的：至多读 6 个字节，至多写 258 个字节，循环继续时至少写了一个字节（`Goal.step_safe`） | `inflate_fast_body_step_safe` | `inffast.c.body.lean` |
| 静态固定表具有表形状 | `lenfix_tableSafe`、`distfix_tableSafe` | `inffast.c.tableok.lean` |
| 同样的安全性命题，外加：结束时模式不是 `TYPE` 或 `BAD` 的调用，留下的输出空间比进入时少 | `inflate_fast_safe_progress` | `inffast.c.progress.lean` |
| 同上，外加：一次调用绝不使 `bits + 8 * avail_in` 增加，并且除非结束于 `TYPE` 或 `BAD`，都使它减小 | `fast_consumes` | `inffast.c.consume.lean` |

表中前三行的定理列在 `tests/audit/theorems.txt` 中。`inflate_fast_safe` 是针对 `inflate` 的入口条件（`Env`）陈述的。表中最后两条定理 `inflate_fast_safe_progress` 和 `fast_consumes` 是针对两个调用者的入口条件（`EnvG`）陈述的；它们是调用者的证明内部的引理，本身没有列出。每项结论的层级记录在[进度，范围](../progress.md#scope)中。

调用者这样使用这些定理：

- **`inflateBack`。** `fast_env`（`infback.c.safety-fast.lean`）证明入口条件。同一文件中的 `LEN_fast_p` 从它取得这些条件，并应用 `fast_consumes`。这在 `inflate_back_sequence_safety` 的证明内部。从 `inflateBack` 发出的调用靠它才安全，这个调用者的循环也靠它才终止。
- **`inflate`，输入和输出位于两个不同的堆块。** `inflate_fast_raw_entry`（`inflate.c.fast-entry.lean`）在这条前提下证明入口条件，然后对它们应用 `inflate_fast_safe_progress`。
- **`inflate`，每一种布局。** `inflate_sequence_safety_public` 允许输入和输出是同一个块里的两段。对快速调用，它的证明用的是 `inflate_fast_default_view_buffers_progress`（`inflate.c.fast-view-public-step.lean`），它是那个证明的一条引理，本身没有列出。这条定理对块没有前提。它是对同一个翻译后的函数的第二个证明，针对调用者的区域和解码器不变量陈述（`inflate.c.fast-view-*.lean`）；它不使用 `EnvG`。`fast_consumes` 没有用于 `inflate`。见[流式解码](inflate.md#the-fast-path)。
- **`inflate`，功能结论。** `inflate_fast_entry`（`inflate.c.meaning-fast.lean`，功能方面工作的定理，没有列在 `tests/audit/theorems.txt` 中）对每一种布局证明入口条件。功能定理 `fast_call_meaning` 用到它；安全结论不用它。

`FastPost` 说的是：流的 `next_in`、`avail_in`、`next_out`、`avail_out` 和 `msg`，以及状态的 `mode`、`hold` 和 `bits` 被写过；输出字节只在本次调用写入的范围内发生变化；`bits < 8` 和 `hold < 2^bits` 重新成立；模式不变，或者变成 `TYPE`（块结束），或者变成 `BAD`。堆里其他东西都没有变，也没有发生分配。

关于 `inflate_fast` 也有功能结论，见[功能结论](#functional-results)。

## 假设

这些定理假设下面的入口条件。在 Lean 里它们是记录 `EnvG` 的字段（`ZlibF/Spec/Common/Inflate/FastEnv.lean`）。`Env` 是 `inflate` 的情形，这时窗口绝不是输出对象；`inflate_fast_safe` 是针对 `Env` 陈述的。这些是内部前提：调用者在应用本页的定理之前证明它们。`fast_env`（`infback.c.safety-fast.lean`）为 `inflateBack` 做这件事。`inflate_fast_raw_entry`（`inflate.c.fast-entry.lean`）在输入和输出位于两个不同的堆块时为 `inflate` 做这件事；它带有这条前提（`ib ≠ ob`）。`inflate_fast_entry`（`inflate.c.meaning-fast.lean`）为每一种布局下的 `inflate` 做这件事。

- **流。** `strm` 指向一个可写的流记录，它的 `state` 是 inflate 状态。
- **输入。** `next_in` 指向一个少于 `2^63` 字节的字节对象内部。`avail_in ≥ 6`，这 `avail_in` 个字节都在对象内。字节对象是一个堆块，或者模型里其他的字节数组，例如状态记录内部的数组。
- **输出。** `next_out` 指向一个少于 `2^63` 字节的可写字节对象内部。`avail_out ≥ 258`，这 `avail_out` 个字节都在对象内。`start ≥ avail_out`，并且在同一个对象里 `next_out` 之前有 `start - avail_out` 个字节；所以下面的 `beg` 是指向该对象内部的指针。
- **分离。** 输入和输出是不同的字节对象，或者是同一个对象里互不重叠的两段。
- **位缓冲。** `bits < 8`，`hold < 2^bits`，`sane ≠ 0`。
- **窗口。** `wsize ≤ 32768`，`whave ≤ wsize`，`wnext ≤ wsize`。如果 `whave ≠ 0`，`window` 指向某个堆块内的 `wsize` 个字节。对 `inflate`，这个块不是输出对象。对 `inflateBack`，它可以就是输出对象；这时 `wnext = 0`，并且窗口的末尾落在输出区域之内。
- **表。** `lencode` 和 `distcode` 指向的表，对 `lenbits` 和 `distbits` 具有安全的形状（`LenTableSafe`、`DistTableSafe`；见[解码表](inftrees.md#the-table-shape)）。

[内部契约](../spec/internal-contracts.md)页面用 `I-if-pre-room`、`I-if-pre-bits`、`I-if-pre-tables` 和 `I-if-pre-window` 这些名字描述 `inflate_fast` 的入口。那里的描述若比上面的列表多，安全定理假设的是上面的列表。

没有哪条前提提到模式。也没有哪条前提说窗口里的字节是什么，或者说 `whave < wsize` 蕴含 `wnext = whave`。安全性只需要上面这些界；其余的属于[功能论证](#functional-results)。

`fast_consumes` 多一条前提：每个字面量/长度叶子至少用掉一位（`LenLeavesPositive`）。对建出来的表，`inflate_table_len_leaves_positive` 证明了它；对固定表，`lenfix_leavesPositive` 证明了它。

## 循环及其不变量

```c
last = in + (strm->avail_in - 5);       /* 当 in  < last 时继续循环 */
beg  = out - (start - strm->avail_out); /* 外层调用的输出起点 */
end  = out + (strm->avail_out - 257);   /* 当 out < end  时继续循环 */
do {
    /* 解码一个字面量，或者一组长度和距离并完成复制 */
} while (in < last && out < end);
/* 把没用到的整字节还回去；把 in、out、hold、bits 写回 */
```

记 `in0` 和 `out0` 为入口处 `next_in` 和 `next_out` 的值。

```
输出块   beg ........ out0 ........ out ............ end ... out0 + avail_out
         | 更早的输出  | 本次调用 |   空闲；进入循环时至少 258 字节
输入块   in0 ........ in ............ last ... in0 + avail_in
         | 已读      |   未读；进入循环时至少 6 字节
```

每一轮开始时，下面各条成立（`ZlibF/Spec/Common/Inflate/FastEnv.lean` 中的 `LS`，以及 `inffast.c.loop.lean` 中 `fast_loop_wp` 的循环不变量）。

| 名字 | 内容 |
| --- | --- |
| I1 | `in0 ≤ in`，并且 `in + 6 ≤ in0 + avail_in`：可以读六个字节 |
| I2 | `out0 ≤ out`，并且 `out + 258 ≤ out0 + avail_out`：可以写 258 个字节 |
| I3 | `bits ≤ 30` 且 `hold < 2^bits` |
| I4 | `bits + 8 * in0 ≤ bits_entry + 8 * in`：手里的每一位要么来自入口，要么来自本次调用读入的字节 |
| I5 | `[out0, out)` 之外的输出字节与入口时相同 |

因为这是 `do` 循环，第一轮不经检查就进入。入口条件直接给出它的 I1 和 I2。之后各轮由循环条件得到它们。

## 每一轮为什么保持不变量

### 至多读六个字节

一轮里有四处读输入。

| 位置 | 条件与读取 | 之后 |
| --- | --- | --- |
| R1，查长度表之前 | `bits < 15`：读两个字节 | 16 到 30 位 |
| R2，长度的附加位 | `bits < op`，其中 `op ≤ 5`：读一个字节 | 够 `op` 位 |
| R3，查距离表之前 | `bits < 15`：读两个字节 | 16 到 30 位 |
| R4，距离的附加位 | `bits < op`，其中 `op ≤ 13`：读一个字节；若仍有 `bits < op`，再读一个 | 够 `op` 位 |

一个编码至多用 15 位，包括二级查表在内；这是表形状的一部分。所以在 R1 或 R3 之后，或者它们被跳过时，后面的编码都有足够的位。`op` 的界 5 和 13 也是表形状的一部分。因此每次 `bits -= op` 拿走的都是确实存在的位，每次移位的位数都小于操作数的宽度。

把四处的最大值加起来是七个字节。七个字节不可能出现。假设 R1、R2、R3、R4 分别读了 2、1、2、2 个字节。

1. R1 之后手里至少有 16 位。长度编码至多用 15 位：至少剩 1 位。
2. R2 加上 8 位，长度的附加位至多用 5 位：至少剩 4 位。
3. R3 加上 16 位，距离编码至多用 15 位：至少剩 5 位。
4. R4 只有在读完第一个字节后手里的位数仍少于 `op ≤ 13` 时，才读第二个字节。那么 R4 之前手里的位数少于 5。这与第 3 步矛盾。

所以一轮至多读六个字节，这就是 `last` 比输入末尾提前五个字节的原因。一轮写一个字面量，或者一次至多 258 字节的匹配，这就是 `end` 比输出末尾提前 257 个字节的原因。258 这个界来自表形状：长度基值加上它最大的附加值至多是 258。`inflate_fast_body_step_safe` 陈述了这两个界。

### 读表

根下标是 `hold & ((1 << lenbits) - 1)`，小于 `2^lenbits`；表形状保证这 `2^lenbits` 个表项都在数组之内。根表项是叶子或链接。链接指定一张二级表，它整个在数组之内，并且只含叶子，所以每个编码至多发生一次 `goto dolen` 或 `goto dodist`。

无效编码设置 `msg` 和模式 `BAD`，然后离开循环。块结束符设置模式 `TYPE`，然后离开循环。两者经过的出口代码与正常结束相同。

### 匹配复制 {#match-copies-f3-and-f4}

设 `dist ≥ 1` 是解码出的距离，`len` 是长度，`3 ≤ len ≤ 258`。

**从输出复制。** 如果 `dist ≤ out - beg`，源 `out - dist` 不早于 `beg`，在输出块里。复制逐字节向前进行。它读到的每个字节，要么在这一轮之前就写好了，要么是同一次复制中更早的一步写的；`dist < len`、两段区域重叠时也是如此。

**从窗口复制。** 否则有 `op = dist - (out - beg)` 个字节来自窗口。C 检查 `op > whave`，由于 `sane ≠ 0`，这时它报错离开。检查之后 `1 ≤ op ≤ whave ≤ wsize`。特别地 `whave ≠ 0`，所以窗口块存在。源位置有三种。

| 条件 | 窗口中的起始下标 | 为什么在 `[0, wsize)` 之内 |
| --- | --- | --- |
| `wnext == 0` | `wsize - op` | `1 ≤ op ≤ wsize` |
| `0 < wnext < op` | `wsize + wnext - op` | `op ≤ wsize` 且 `wnext < op`。复制一直进行到环的末尾，再从下标 0 继续，至多 `wnext` 个字节 |
| `wnext ≥ op` | `wnext - op` | `op ≤ wnext ≤ wsize` |

每一段复制的字节数，取窗口在那里所存的数量与匹配还需要的数量中较小的一个。如果匹配更长，剩下的部分从输出复制，如上所述。

对 `inflateBack`，窗口就是输出缓冲区本身。这时 `wnext = 0`，只有第一行适用；窗口末尾落在输出区域之内这条前提，保证读操作不出块。

### 归还字节与写回

```c
len = bits >> 3;
in -= len;
bits -= len << 3;
hold &= (1U << bits) - 1;
```

I4 给出 `bits ≤ bits_entry + 8 * (in - in0)`。加上 `bits_entry < 8`，就得到 `len ≤ in - in0`：函数归还的只是它自己读入的字节，`in` 不会退到 `in0` 之前。之后 `bits < 8`，所以掩码的移位在合法范围内。入口条件 `bits < 8` 就用在这里。没有它，函数可能退过调用者已经消耗掉的字节。

`inflate` 在选择快速路径的条件里自己检查了 `bits < 8`。`inflateBack` 不检查。它的分派循环的证明把这个事实放在循环不变量里：每一轮以 `TYPE`、`TABLE` 或 `LEN` 模式开始时，持有的位都少于 8 个（`Short`，`infback.c.safety-modes.lean`）。`LEN_fast_p` 并不证明入口处的 `bits < 8`：它把这一点当作前提，由上述不变量提供，并证明调用之后它再次成立。

随后函数算出新的 `avail_in` 和 `avail_out`，两者各由同一个块内的指针差得到，连同两个游标、`hold` 和 `bits` 一起存回（`fast_finish_wp`，`inffast.c.final.lean`）。

## 循环为什么会结束

主循环的度量是剩余的输出空间 `out0 + avail_out - out`（`fast_loop_wp`）。不离开循环的一轮至少写一个字节，所以度量下降。它小于 `2^63`，远小于 `2^64` 的循环燃料。

在一轮之内，复制循环跑 `op` 或 `len` 次并递减计数，一个编码至多多查一次表。

## 难点在哪里

两个余量都很小，而且恰好够用。循环之所以安全，只是因为一轮绝不会读第七个字节，而这一点在任何单独一条语句里都看不出来：它来自四处补位与表所允许的位数之间的相互作用。证明在堆上、对每一张形状安全的表，照着上面论证里同样的分情形方式进行。

第二个难点是输出块。它在同一轮里既被读又被写，匹配的源可以与目的重叠，输入和输出还可能是同一个块里的两段（`tests/regression/inflate-shared-block`）。因此循环不变量跟踪的是整个输出数组，而不是分开的“旧”字节和“新”字节两个视图。

## 没有定理陈述的 C 解读

- 匹配从窗口读到的字节是先前写过的。对 `inflate`，这来自[流式解码](inflate.md#window-shape-w)的窗口形状 W.5：没有填满的窗口里 `wnext = whave`，所以只可能出现表的第三行，它读的位置在 `wnext` 之前。`EnvG` 不带 W.5，安全定理也不需要它：在模型里，读一个从未写过的字节会得到任意值，不算故障（[可信基础](../trusted-base.md)）。**尚未由证明确认**。

## 功能结论

这些结论说的是快速解码器算出了什么。它们已证明，但不是安全结论所必需的。

| 结论 | 定理 | 模块 |
| --- | --- | --- |
| 一轮恰好消耗格式中一个记号的那些位，并且它消耗的位就是源中接下来的位 | `actual_body_refines_token`、`actual_body_preserves_origin` | `inffast.c.body-token.lean`、`inffast.c.body-origin.lean` |
| 查长度表或距离表得到的是格式规定的符号 | `length_lookup_matches_format`、`distance_lookup_matches_format` | `inffast.c.length-semantics.lean`、`inffast.c.distance-semantics.lean` |
| 匹配复制就是格式中的 LZ77 复制 | `actual_distance_refines_lz77`、`actual_copy_match_refines_lz77` | `inffast.c.distance-result.lean`、`inffast.c.match-history.lean` |

这些结论用的不变量更大：它把已消耗的位与源数据流联系起来，把窗口内容与更早的输出联系起来。`fast_call_meaning`（`inflate.c.meaning-fast.lean`，没有列在 `tests/audit/theorems.txt` 中）把这层含义带过 `inflate` 中 `LEN` 的快速分支，输入和输出可以在任何字节对象里：调用之后，已解码的记号仍然能按格式的规定解析；或者模式是 `BAD`，并且已读的输入没有任何合法的续接。它是带条件的往返定理的一步（[流式解码](inflate.md#functional-results)）。提前读入又归还的字节，与已解码符号的含义无关；见[流式解码](inflate.md#causality-and-history-across-calls)。关于功能不变量需要携带什么，早先的一条笔记保存在[历史](../history/proof-functional-notes.md)中。

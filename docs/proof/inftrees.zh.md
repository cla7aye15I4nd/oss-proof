<!-- source-sha256: 31528d82c64d30effe77bf2a19339c5e7da504b8cd923ea01db5c01ae89a43d9 -->
# 解码表：`inflate_table` 为什么安全，它建的表为什么可以放心读

源文件：`zlib/inftrees.c`。翻译：`ZlibF/Zlib/inftrees.c.lean`。

`inflate_table` 把一列码长变成一张查找表。这里证明了两件事。其一，调用本身不会出故障，只写它的工作数组和表空间。其二，它留下的表具有下文定义的一种形状；在这种形状下，`inflate` 和 `inflate_fast` 之后的每一次查表，读到的都是表内一个已经初始化的表项。本页解释这两件事，以及它们所依赖的规范编码算术。

`inflate_table` 是内部函数。调用它的是 `inflate`（[流式解码](inflate.md)）和 `inflateBack`（[回调解码器](callbacks.md)）。

## 结论

本表中的定理都已登记在 `tests/audit/theorems.txt` 中，并在提交 `bde170e9` 上已验收（[层级](README.md#status-levels)）。模块在 `ZlibF/Proof/` 下。

| 结论 | 定理 | 模块 |
| --- | --- | --- |
| **T1.** 对每一次满足前提的调用，`inflate_table` 返回且不出故障。只有 `work` 和表空间发生变化。返回值是 0、1 或 -1 | `inflate_table_safe` | `inftrees.c.lean` |
| 返回 -1 当且仅当这组码长不是可接受的编码；返回 1 只出现在 `LENS` 和 `DISTS` | `inflate_table_correct_ret` | `inftrees.c.lean` |
| **T2.** 调用返回 0 之后，表对返回的根宽度具有[表形状](#the-table-shape) | `inflate_table_decoder_safe` | `inftrees.c.decoder-safe.lean` |
| 调用返回 0 之后，返回的指针在 `*table` 之后 `used` 项处，`used` 至多是 128、852 或 592。对 `LENS` 和 `DISTS`，根表以及每个链接指定的二级表，都在第 `used` 项或之前结束（`TableReadExtent`），所以不会走到建在这张表后面的另一张表里 | `inflate_table_read_extent` | `inftrees.c.read-extent.lean` |
| T2 的证明用到的两条引理，它们说的是码长列表，不涉及堆。`root_cover`：对没有超额分配的码长，每个根下标要么恰好被一个码长不超过 `root` 的编码填充，要么存着一组更长编码的链接，要么没有被写；最后一种情形要求 Kraft 和够不到这个下标，完整的编码排除了它（`RootCell`）。`group_cover`：对完整的编码，如果二级表的宽度容得下它那一组编码，表里每个下标恰好属于这一组中的一个编码。关于堆的事实，即查表能到达的每个表项都是符合表形状的叶子或链接，是 T2 | `root_cover`、`group_cover` | `inftrees.c.cover.root.lean`、`inftrees.c.cover.group.lean` |
| `inflate_fixed` 让状态指向两张静态表，改动四个字段 | `inflate_fixed_ok` | `inftrees.c.fixed.lean` |
| 对 `LENS` 和 `DISTS`，在调用返回 0 之后：慢速解码器在手里位数还少时接受的表项，在更多的位到来之后不变 | `constructor_establishes_query_stability` | `inftrees.c.decode.stability.lean` |

另有一条定理已检查而未登记：`inflate_table_len_leaves_positive`（`inftrees.c.decoder-safe.lean`）。它说，一次返回 0 的 `LENS` 调用之后，表里每个字面量/长度叶子至少用掉一位。两个调用者都用到它，都是在两条已登记的序列定理的证明内部。`inflate` 需要它来建立[它的不变量](inflate.md#the-invariant)的子句 `tables`，这个子句包含这条事实（`inflate.c.dynamic-install.lean`）。回调解码器的终止性需要它（`infback.c.safety-table-lens.lean`；[快速解码](inffast.md#assumptions)）。

关于表项含义的功能结论列在[功能结论](#functional-results)一节。

## 假设

`inflate_table(type, lens, codes, table, bits, work)` 不检查自己的参数。定理假设下面这些条件（`CallPre`，`ZlibF/Proof/inftrees.c.main.lean`）。它们是内部前提：每个调用者在每次调用处证明它们。在[内部契约](../spec/internal-contracts.md)里，它们是 `I-it-pre-lens`、`I-it-pre-codes`、`I-it-pre-work` 和 `I-it-pre-table`。

| 前提 | `CODES` | `LENS` | `DISTS` |
| --- | --- | --- | --- |
| 符号个数 `codes` | 至多 19 | 至多 288 | 至多 32 |
| 每个码长 `lens[i]`，`i < codes` | 至多 7 | 至多 15 | 至多 15 |
| 请求的根宽度 `*bits` | 至少 7 | 任意 | 任意 |
| `*table` 之后可写的表空间 | 128 项 | 852 项 | 592 项 |

三种情形下都有：`lens` 有 `codes` 个可读的项，`work` 有 `codes` 个可写的项，`work` 与 `lens` 不是同一个数组。

不完整的编码和超额分配的编码都在定义域之内；对它们调用返回 -1。调用者传入的值比定理允许的更窄：`CODES` 是 19 个三位码长和根宽度 7，`LENS` 至多 286 个符号，`DISTS` 至多 30 个。

## 函数做了什么

```c
for (sym = 0; sym < codes; sym++) count[lens[sym]]++;     /* 1. 统计各码长的个数   */
/* 求出 min 和 max；把 root 限制在两者之间 */
left = 1;
for (len = 1; len <= MAXBITS; len++) {                     /* 2. Kraft 检查          */
    left <<= 1; left -= count[len];
    if (left < 0) return -1;
}
if (left > 0 && (type == CODES || max != 1)) return -1;
for (...) offs[len + 1] = offs[len] + count[len];          /* 3. 按码长给符号排序    */
for (sym = 0; sym < codes; sym++)
    if (lens[sym] != 0) work[offs[lens[sym]]++] = (unsigned short)sym;
for (;;) {                                                 /* 4. 每轮处理一个编码    */
    /* 在低位等于 huff 的每个下标处，写入 work[sym] 的表项 */
    /* 把 huff 反向步进到下一个编码 */
    /* 码长超过 root 时：确定一张新二级表的大小，并链接它 */
}
/* 5. 如果编码不完整，把剩下的那一个表项填成无效标记 */
```

## 表形状

T2 说，成功的调用留下的表具有下面的形状。`LenTableSafe` 和 `DistTableSafe`（`ZlibF/Proof/inffast.c.tableok.lean`）针对从数组下标 `o` 开始、根宽度为 `R` 的表陈述它。

- `R ≤ 15`，`2^R` 个根表项都在数组之内。
- 每个根表项是叶子或链接。
- **叶子**是字面量、长度或距离的基值、块结束符，或者无效编码。长度基值至多带 5 个附加位，基值至少是 3，基值加上最大的附加值至多是 258。距离基值至多带 13 个附加位，基值至少是 1。
- **链接**有一个 1 到 15 之间的下标宽度 `op` 和一个偏移 `val`。`o + val` 处的 `2^op` 个表项都在数组之内，而且全是叶子。
- 根表项的位数，加上经它到达的叶子的位数，至多是 15。

`CODES` 的形状更简单（`CodeLengthTableSafe`）：没有链接，根宽度至多 7，每个表项用掉 1 到 `root` 位，存着一个小于 19 的符号或一个无效标记。

固定表 `lenfix` 和 `distfix` 具有同样的形状（`lenfix_tableSafe`、`distfix_tableSafe`）。解码器的不变量把这个形状从建表的那次调用一直带到表上的每一次查找（[`InflateInv`](inflate.md#the-invariant) 的子句 `tables`）。

## 每一步为什么安全

### 计数与 Kraft 检查

`count[lens[sym]]` 不越界，因为每个码长至多是 15，而 `count` 有 16 项。

设 `c_l` 是码长为 `l` 的符号个数。循环维持

```
left_0 = 1
left_l = 2 * left_(l-1) - c_l
```

一旦 `left_l` 为负就返回 -1。把每个码长的第一个编码定义为

```
B_1 = 0
B_(l+1) = 2 * (B_l + c_l)
```

那么 `left_l = 2^l - B_l - c_l`。所以通过检查的调用满足 `B_l + c_l ≤ 2^l`：码长为 `l` 的所有编码都放得进 `l` 位。`left` 是有符号的 `int`；它最大是 `2^15`，所以移位和减法都不会溢出。

循环结束后，`left` 为正表示编码不完整。C 只在一种情况下接受它：类型不是 `CODES` 且 `max = 1`，也就是只有一个码长为 1 的符号。

### 排序：F2

`offs[1] = 0`，`offs[l+1] = offs[l] + c_l`。按符号顺序，码长为 `l` 的第 i 个符号写到 `work[offs[l] + i]`。这个下标小于码长非零的符号总数 `m`，而 `m ≤ codes`，所以写操作在 `work` 之内。不同的符号写到不同的槽。之后 `work[0..m)` 里是有编码的符号，先按码长、再按符号排好序。这是[方法](method.md#structural-facts-used-by-several-proofs)中的事实 **F2**。主循环只对 `sym < m` 读 `work[sym]`。

### 编码的步进

DEFLATE 发送编码时最高位在前，而表下标取输入位时最低位在前。所以函数把当前编码按位反转之后存在 `huff` 里。设 `rev_l(v)` 是把 `v` 的低 `l` 位倒过来。循环不变量是

```
huff = rev_len(B_len + i)      对码长为 len 的第 i 个编码
```

因此 `huff < 2^len`。

- 第一个编码是 0，反转后也是 0。
- 要步进到同一码长的下一个编码，C 从最高位往下清掉 `huff` 开头连续的 1，再把遇到的第一个 0 置 1。这是倒着做的加一。如果 `huff` 全是 1，它变成 0。
- 下一个符号的码长更大时，规范编码要在低位补零。反转之后这些零在高位，所以 `huff` 已经是正确的值。

对完整的编码，最后一步让 `huff` 回到 0。对只有一个符号的编码，它停在 1。循环之后 C 用 `huff != 0` 来决定是否写第 5 步的无效标记。

`ZlibF/Proof/inftrees.c.math.lean` 证明了反转和加一的这些事实，不涉及堆。

### 写根表项

对 `len ≤ root` 的编码，C 把表项写到这些下标：

```
huff + (2^root - 2^len), ..., huff + 2 * 2^len, huff + 2^len, huff
```

`fill` 从 `2^root` 开始，它是 `2^len` 的倍数，每次减去 `2^len` 直到 0，所以不会回绕。由于 `huff < 2^len`，每个下标都小于 `2^root`。它们恰好是低 `len` 位等于 `huff` 的那些根下标。

### 确定二级表的大小并链接

当 `len > root` 时，`huff` 的低 `root` 位相同的那些编码共用一张二级表。C 在写之前先确定它的大小：

```c
curr = len - drop;                 /* drop = root */
left = (int)(1 << curr);
while (curr + drop < max) {
    left -= count[curr + drop];
    if (left <= 0) break;
    curr++;
    left <<= 1;
}
```

`left` 是当前宽度下还空着的槽数。如果这个码长的编码把槽用完了，宽度就够了。否则宽度加一位。循环最迟在 `max` 处停下，所以读 `count[curr + drop]` 时下标至多是 15。循环之后，这一组里每个编码都满足 `len - root ≤ curr`。然后像写根表那样写表项，只是用 `huff >> drop` 代替 `huff`，用 `2^curr` 代替 `2^root`。

新表从 `next` 开始，它等于表的基址加上此前所有表的大小。`used` 就是这个总和。对 `LENS` 和 `DISTS`，C 先把新表的大小 `2^curr` 加到 `used` 上，再把这个和与 852（`LENS`）或 592（`DISTS`）比较，更大时返回 1。通过之后它才链接新表；表项在随后的各轮里写入。根表在主循环之前做同样的比较，那时 `used = 2^root`。所以每次写都在前提给出的空间之内。

根链接把宽度 `curr` 存进 `op`，把偏移 `next - *table` 存进 16 位字段 `val`。这时 `next - *table = used - 2^curr`，所以

```
val + 2^op = used ≤ 852   对 LENS
val + 2^op = used ≤ 592   对 DISTS
```

这个偏移放得进该字段，它指定的表也在空间之内结束。有两条定理对成功调用返回的表陈述了这一点。`inflate_table_read_extent` 对每个根链接给出 `val + 2^op ≤ used`，其中 `used ≤ 852` 或 `used ≤ 592`。`inflate_table_decoder_safe` 对每个根链接给出：`val` 处的 `2^op` 个表项在数组之内，并且都是叶子（`LinkOK`，表形状的一部分）。

`CODES` 没有这项检查，也不需要：每个码长至多是 7，请求的根宽度至少是 7，于是 `root = max`，没有比根更长的编码，表有 `2^root ≤ 128` 项。这就是 `CODES` 的前提更强的原因。

### 每个下标都被覆盖

填充写和链接写合起来必须覆盖每一个下标，否则查表可能读到从未写过的表项。

给每个码长为 `l` 的编码分配一个区间：以它开头的那些 15 位字，共 `2^(15-l)` 个。对完整的编码，这些区间互不相交，并且盖住全部 `2^15` 个字（`inftrees.c.cover.tile.lean`）。一个根下标代表以它那 `root` 位开头的字。要么有一个码长不超过 `root` 的编码是这些字的前缀，它的填充写了这个下标；要么有更长的编码共用这个前缀，其中第一个在这里写了链接（`root_cover`）。在二级表内做同样的论证，就得到 `group_cover`。

有两种情形不是完整编码，要单独处理。

- 只有一个码长为 1 的符号：`root = 1`。循环写下标 0，第 5 步在下标 1 处写无效标记。
- 一个符号都没有：C 写两个无效表项，置 `*bits = 1`，把 `*table` 前移两项，返回 0。

### 叶子里存着什么

符号 `w` 的表项，其 `op` 和 `val` 取自静态数组 `lbase` 和 `lext`（对 `LENS`，从符号 257 起）或 `dbase` 和 `dext`（对 `DISTS`）。这些数组的下标是 `w - 257` 或 `w`。它不越界，因为 `codes ≤ 288` 或 `codes ≤ 32`；数组分别有 31 项和 32 项。对 `CODES`，基值指针和附加位指针用不到：每个符号都小于 19，走的是字面量分支。

`inftrees.c.cover.leaf.lean` 逐项检查了四个数组里的每个值，确认它给出的叶子符合上面的形状。`inflate_table_decoder_safe` 把覆盖和叶子的取值合在一起。

### 移位

函数里每个移位的位数都是一个码长或一个表宽度：`1U << root`、`1U << (len - drop)`、`1 << curr`、`1U << (len - 1)`。求值时码长在 1 到 15 之间；`drop` 是 0 或 `root`，在二级表里有 `root < len`。所以每个移位位数都在 0 到 15 之间。

## 循环为什么会结束

`inflate_table_safe` 包含终止性。每个循环有自己的界。

- 计数、Kraft、偏移和排序这几个循环的范围是固定的：16 个码长，或 `codes` 个符号。
- 主循环每轮处理一个有编码的符号；`sym` 从 0 走到 `m`，`m ≤ 288`。
- 在一轮之内：填充循环把 `fill` 以 `2^len` 为步长减到 0；反向加一把一个一位的掩码至多下移 15 位；确定大小的循环每轮把 `curr` 加一，并在 `max ≤ 15` 处停下。

这些都远小于 `2^64` 的循环燃料。

## 难点在哪里

一旦知道 `huff < 2^len`，写操作的安全性就容易了。难的是覆盖：任何一张表都没有一个下标漏写。它需要规范编码的整套理论（上面的区间），需要一个模型来描述哪些编码共用一张二级表，还需要证明那个向前查看 `count` 的确定大小的循环，给每一组的宽度恰好是它的编码所需要的。覆盖看起来像功能性质，但解码器的安全性依赖它，因为解码器使用表项之前并不检查。

## 没有定理陈述的 C 解读

- “常数 852 和 592 对每一种有效编码都够用。”这里没有定理陈述这一点。证明也不需要它：空间用完时 C 返回 1，解码器报错。这个说法来自 zlib 自己的穷举搜索（`examples/enough.c`）。**尚未由证明确认**。

## 源码笔记 {#c-correspondence-checks}

固定表是 `inffixed.h` 的副本。它们不是 `inflate_table` 的输出：`lenfix` 有四项，即下标 99、227、355 和 483 处，在无效编码的标志上不同。这一条以及翻译怎样跟随 `inftrees.c` 的其他笔记，见[解码器的源码笔记](inflate-source-notes.md#inftreesc)。

## 功能结论

这些结论说的是表项的含义。它们已登记，但不是安全结论所必需的。

| 结论 | 定理 | 模块 |
| --- | --- | --- |
| 写入的表项就是给定码长对应的规范叶子和链接 | `inflate_table_content`、`constructor_establishes_decode_table_invariant` | `inftrees.c.content.lean`、`inftrees.c.decode.invariant.lean` |
| 在表中查找，解码出的是格式为这些输入位规定的符号 | `decode_table_matches_format`、`decode_table_leaf_sound`、`decode_table_classifies_input` | `inftrees.c.decode.*.lean` |

规范编码的数学定义是[格式指南](../spec/format/README.md)中的 `F-code-*`。

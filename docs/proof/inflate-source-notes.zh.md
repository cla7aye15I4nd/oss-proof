<!-- source-sha256: 64b8e9ee77183ba17d399d952676011a437b5c2bf80ea38f3211add029e35aa5 -->
# 解码器的源码笔记：`inflate.c`、`inffast.c`、`inftrees.c`

本页记录 C 源码里的一些细节：在这些地方，翻译若走捷径，程序的行为就会改变。它们涉及求值顺序、整数转换、贯穿（fall-through），以及跨辅助函数保留的值。本页写给拿 `zlib/*.c` 与 `ZlibF/Zlib/*.c.lean` 对照的读者。

这些笔记是对 C 的解读，不是定理。定理陈述的是翻译（[流式解码](inflate.md)、[快速解码](inffast.md)、[解码表](inftrees.md)），差分测试把翻译与编译出来的 C 做比较；这些测试是忠实性的证据，不是证明。翻译遵循的规则见[翻译语义](../design/translation.md)。

## `inflate.c`

### 控制流与位缓冲

翻译把 `inflate` 的 C 寄存器（`next`、`have`、`put`、`left`、`hold`、`bits` 等）放在一个记录 `IL` 里。每个模式是一个辅助函数，它像 C 一样有三种返回方式：

- switch 的 `break` 回到分派器，分派器重新从堆里读 `state->mode`；
- `goto inf_leave` 带着当时的寄存器跳到公共出口。此前做过的读写都保留；
- `return` 立刻离开函数。

贯穿到下一个 case 的情形，调用下一个 case 的辅助函数。

C 里这些细节是可以观察到的：

- `TYPE` 贯穿到 `TYPEDO` 时不写 `mode`。如果因为输入不足读不出块头，保存下来的模式仍是 `TYPE`。这会体现在 `data_type` 和下一次进入时。
- `PULLBYTE` 先检查有没有输入，再做任何改动。失败的 `NEEDBITS` 保留前几轮取入的每个字节。`DROPBITS` 先改 `hold`，再从 `bits` 中减。`BYTEBITS` 的两个表达式用的都是旧的位数。
- `BITS(n)` 先把 `hold` 转成 `unsigned`，再用 `(1U << n) - 1` 做掩码。`hold` 本身是 `unsigned long`。
- 在 `HEAD` 中，头部校验把一个移位后的 32 位项与 `hold >> 8` 按 64 位算术相加。`inflatePrime` 放进去的高位也参与运算。
- `DICT` 在 `RESTORE` 和更新 `total_in` 之后返回 `Z_NEED_DICT`。它不经过 `inf_leave`。`MEM` 和 `SYNC` 也是直接返回。
- `CHECK` 更新输出总数和校验和，然后重置本地的输出基准 `out`。出口代码用的是新的基准，所以同一批字节不会被数两次。
- `inf_leave` 先恢复寄存器，再更新窗口。如果窗口分配失败，函数在后面更新总数和校验和之前就返回 `Z_MEM_ERROR`。已经写出的输出仍然留着。

`inflatePrime` 在位数为负时清空位缓冲。它拒绝大于 16 的位数和大于 32 的合计位数。它在 `long` 表达式里对 `value` 做掩码，之后才转成 `unsigned long`，所以负的 `value` 经过的就是这个转换顺序。

`inflateMark` 把 `back` 做符号扩展，转成 `unsigned long`，左移 16 位，再转回 `long`，然后加上条件项。在这个平台上，超出范围的转换按模运算。出错时结果是 `-65536`。

### 窗口、字典、复制

`updatewindow` 分配窗口时不初始化，然后复制最后 `wsize` 个字节，或者复制在环的末尾处断成两段的一个后缀。`inflateGetDictionary` 先返回从 `window + wnext` 到末尾的部分，再返回 `wnext` 之前的部分。`inflateSetDictionary` 在 `DICT` 模式下检查 Adler-32 标识，并把字典的末尾传给 `updatewindow`。

窗口在两个地方分配：在 `updatewindow` 中，当它被调用而 `window == NULL` 时（调用来自 `inflate` 的出口代码和 `inflateSetDictionary`）；以及在 `inflateCopy` 中，为带窗口的流的副本分配。窗口在四个地方释放：

- `inflateReset` 在 `wbits != reqbits` 时释放它，然后置 `wbits = reqbits`。无论哪种情况，它都把 `wsize`、`whave` 和 `wnext` 置为 0。两个宽度相等时，窗口块保留下来并被再次使用。
- `inflateReset2` 在窗口的宽度 `wbits` 与新 `windowBits` 所要求的宽度不同时释放它，然后调用 `inflateReset`。
- `inflateSync` 在匹配成功之后调用 `inflateReset`。之后如果 `wbits == 0`，它释放仍然存在的窗口，并置 `wbits = 15`。
- `inflateEnd` 释放它，然后释放状态。

`inflateResetKeep` 什么都不释放。窗口块和三个计数器保持原样。

`inflateCopy` 通过源流的分配器分配。如果窗口分配失败，它释放新的状态。当状态检查拒绝源流时，以及两种分配失败时，它都把 `dest->state` 置为 `NULL`。成功时它复制两个记录并修复回指指针。如果 `lencode` 是状态自己的 `codes` 数组，它让 `lencode` 和 `distcode` 指向副本的数组；指向固定表的指针保持不变。它重新定位 `next`，并复制 `whave` 个窗口字节。指针修复的证明用到不变量子句 `origin`（`CopyTableOrigin`）和 `CopyTableOrigin.dynamic_geometry`：`next` 和动态的 `distcode` 是 `codes` 内的偏移，`next` 可以恰在它末尾之后一个位置。

在模型里，同一个字节对象中两段不相交区域之间的 `memcpy` 是允许的。区域重叠则是故障。

### 初始化、恢复与指针

`inflateInit2_` 把新状态清零，然后设置字段并调用 `inflateReset2`。版本检查看的是版本字符串的第一个字节和结构体大小，本构建中是 112。`inflateReset2` 在取负之前就拒绝小于 `-15` 的 `windowBits`，所以 `INT_MIN` 不会走到取负那一步。

`inflateStateCheck` 从左到右求值它的各项检查，在第一项失败处停下，所以不会通过一个已被前面的检查拒绝的指针去读字段。在模型里，指向 deflate 状态的指针不是合法的 inflate 状态，不管两个结构体的布局如何。`inflateBackInit_` 和 `inflateInit2_` 创建的是不同的对象，各有各的结束函数。

`inflateGetHeader` 保存调用者的指针，并且不检查 `NULL` 就写 `head->done`。在 `EXTRA` 中，C 在条件里做赋值；`NAME` 和 `COMMENT` 用的是后置自增。

`syncsearch` 通过指针接收 `have`。翻译传入它的值并返回新值，`inflateSync` 在 C 调用返回的位置把它存回去。`inflateSync` 先搜索位缓冲里留着的字节，再搜索调用者的输入，并在重置之后恢复 `total_in`、`total_out` 和封装相关的事实。`inflateSync` 和头部 CRC 用的四字节局部数组是真实的临时字节存储，在每条返回路径上都被释放。

`inflateGetDictionary` 通过指针接收可选的长度。翻译改为返回这个值。所以定理不覆盖 `dictLength` 单元与调用者其他数据重叠的情形。

### 表模式与尾部模式引理的命题

`inflate_TABLE_run` 涵盖三个计数的提取，以及长度符号或距离符号过多时的出口。`inflate_LENLENS_run` 假设 `have ≤ ncode ≤ 19`，并假设已写入的项都是 3 位的值（`Good3`）；前者由 `TABLE` 给出，后者由前几轮给出。`ll1_run`、`lz_run` 和 `llTail_run` 是它的三个循环部分。

为码长编码调用 `inflate_table` 时，用的是 `inflate_table_safe` 和 `inflate_table_correct_ret`。`inflate_CHECK_run` 假设静态的校验和表完好（`StaticsOK`），并指明本次调用期间写入的字节（`PutAt`）。对不是规范形式的 Adler-32 值，单字节更新有它自己的关系（[Adler-32](adler32.md)）；目标并不假设种子是规范的。

## `inffast.c`

`inflate_fast` 用无符号减法构造 `last = in + (avail_in - 5)` 和 `end = out + (avail_out - 257)`。六个输入字节和 258 个输出字节的入口余量保证两者都不回绕。`beg = out - (start - avail_out)` 是外层调用的输出起点：`inflate` 把它最初的 `avail_out` 作为 `start` 传入，`inflateBack` 传入窗口大小。

`here` 是指向表项的指针；`inflate.c` 里的慢速解码器则是把表项复制出来。`dolen` 和 `dodist` 是标签，表项是链接时用向后的 `goto` 跳到它们。出错或遇到块结束符时的 `break` 跳过循环条件。循环条件和最后的结算比较的都是指向同一对象的指针。

匹配复制是每次展开三个字节的循环，读写顺序与 C 相同。匹配可以与它自己的输出重叠：某一步写下的字节会被后面的一步读到。换成 `memcpy`，或者从源的快照复制，结果就不同了。每个 `do { ... } while (--op)` 循环进入时计数都是正的。

在每一个出口，包括遇到无效编码或距离太远之后，函数都把没用到的整字节还给输入，保留 `bits & 7` 位，并写回指针和剩余计数。

## `inftrees.c`

### 表项与标志顺序

一个 `code` 有两个字节字段 `op` 和 `bits`，以及一个 16 位的 `val`。表空间是 `ENOUGH_LENS = 852` 加 `ENOUGH_DISTS = 592` 项，共 1444 项。码长至多是 15。码长编码的各个码长按这个顺序到达：`16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15`。

| `op` | 含义 |
| --- | --- |
| 0 | 字面量 |
| 1 到 15 | 指向二级表的链接；低位给出它的下标宽度 |
| 16 + e | 带 e 个附加位的长度或距离基值 |
| 96 | 块结束符（32 和 64 两位都置位） |
| 64、71 或 77 | 无效编码 |

解码器按固定的顺序检查这些标志。慢速的字面量/长度解码器先检查块结束，再检查无效。快速解码器依次检查字面量、长度、链接，然后是块结束或无效。`DIST` 没有 `LEN` 那样的 `op != 0` 检查。`CODELENS` 不看 `op` 就读 `val`。码长全为零的字母表给出两个 `val = 0` 的无效表项；之后流会因为缺少块结束符而失败。

固定表是 `inffixed.h` 的副本：512 个字面量/长度表项，根宽度 9；32 个距离表项，根宽度 5。它们不是 `inflate_table` 的输出。用 `inflate_table` 来建会改变四个字面量/长度表项，即保留符号 286 和 287 的表项：生成出来的无效标志在下标 99 和 355 处是 71，在下标 227 和 483 处是 77（`lext` 的最后两项），而头文件里是 64。这三个值都会拒绝保留符号：每个值的 64 位置位，16 位和 32 位都未置位。翻译用的是头文件里的值。

基值数组、附加位数组和顺序数组是常量。错误消息是只读字符串；调用者可以通过 `strm->msg` 读到它们。

### `inflate_table`

函数按这个顺序执行各步：统计码长、检查 Kraft 和、给符号排序、填表、写尾部。它不检查自己的参数。没有符号的情形写两个无效表项，并在返回 0 之前更新两个输出参数。超额分配的编码，或者不被允许的不完整编码，返回 -1。表空间用完返回 1，这时可能已经写了一些表项。

C 以指针传递 `table` 和 `bits`。翻译按值传入 `*table` 和 `*bits`，并返回新值。出错返回时这两个值不变，但已经写入的表项仍留在那里。在 `CODELENS` 中，调用者在为长度表调用之前给 `lencode` 赋值，在为距离表调用之前用前进后的 `next` 给 `distcode` 赋值。

算术上的细节：

- `count` 和 `offs` 是 16 位值的数组，带有 C 的提升和截断。
- `left` 是有符号的，移位和减法也是有符号的。后面的 `1 << curr` 是有符号表达式；前面的 `1U << root` 是无符号的。
- 变量 `min` 在 `min = fill` 处改变了含义：从那以后它存的是当前表的大小。
- `fill -= incr`，以及调用者最后的 `while (copy--)`，都是无符号的。
- 根链接存的是截断到 16 位的指针差。`inflate_table_decoder_safe` 针对存下来的这个值陈述：它指定的二级表在数组之内，并且只含叶子（`LinkOK`）。

### 位数不足时的慢速查表

慢速解码器可以在手里还不到 `root` 位时就查根表项。如果表项自己的长度不超过手里的位数，它就接受这个表项；否则它取一个字节再查。它接受的表项在更多的位到来之后不变（`constructor_establishes_query_stability`，针对 `inflate_table` 以 0 返回的 `LENS` 或 `DISTS` 表）。链接则需要第二次查表和两个长度。

提前读入的字节为什么不必有效，见[流式解码](inflate.md#causality-and-history-across-calls)。

<!-- source-sha256: 613d46df6f6601e6dd041ba53b02526413a2fa17819b0d08650431d279304509 -->
# 翻译 C 而不改变它的行为

选定源码中的每个 C 函数，都由人工逐语句改写成一个 Lean 函数。本页给出规则、四条采纳的规范化，以及两个连同 C 一起列出的函数，让读者能够自己把翻译与源码对照。内核不对照 C 检查翻译。做这件事的是审查和差分测试；测试是忠实性的证据，不是证明。

[架构](architecture.md)定义这里用到的类型（`M`、`Fault`、`cwhile`、指针）。[可信基础](../trusted-base.md)记录模型的限制。

## 规则

翻译按原有顺序保留 C 函数的语句。它不重排检查，不丢掉任何一次读或写，也不替换算法。证明难做不是改动翻译的理由。与 C 不一致就是翻译缺陷：对照 C 改正它，并加入一个能抓住它的差分测试。

采纳的规范化有四条（所有者 2026-11-15 的决定）。它们连同例子列在[采纳的规范化](#the-accepted-normalisations)里：

1. 内部函数的输出参数按值传入，并作为第二个结果返回。
2. 对同一位置的两次读取，中间没有写入，就算一次读取。
3. 对同一个记录的字段的连续赋值，算一次记录更新。
4. 同一函数中在前的检验已把某个有符号运算限制在范围之内时，这个运算用普通运算符书写。

这四条之外的任何改动都是翻译缺陷。

## 被翻译的源码

只翻译一种构建：默认的 x86_64 Linux、静态库、LP64。运行时参数绝不会选出另一个编译分支。预处理选择是对照 `zlib/` 加上按文件名顺序应用的 `patches/` 补丁来确定的。

| 源码族 | 选定的分支 |
| --- | --- |
| 压缩 | 启用 gzip；禁用 `FASTEST`、`LIT_MEM`、`UNALIGNED_OK` 和调试检查；默认的 `MAX_WBITS` 15 和 `MAX_MEM_LEVEL` 9 |
| 解码表和 inflate | 启用 gzip 和快速解码；禁用 `BUILDFIXED`、`MAKEFIXED`、`PKZIP_BUG_WORKAROUND`、`INFLATE_STRICT` 和无效距离恢复。固定表来自 `inffixed.h` |
| CRC | 静态表；braid 参数 `N = 5` 和 `W = 8`。运行的是小端分支；大端分支没有被走到 |
| Gzip 文件 | LP64 的大文件入口和 C99 格式化；不选 Windows、宽字符和 `Z_SOLO` 的路径。一次 I/O 请求至多 `2^30` 字节 |

每个翻译文件都在文件头注释里列出它的预处理选择。这些选择是针对这种构建对源码的解读。没有证明检查它们：它们**尚未由证明确认**，要靠对照预处理后的源码来审查。

`zlib/X.c` 翻译在 `ZlibF/Zlib/X.c.lean` 里，`zlib/X.h` 翻译在 `ZlibF/Zlib/X.h.lean` 里。（`deflate.c` 拆成三个文件。）翻译文件里没有证明。每个函数保留它的 C 名字，文档字符串以 C 签名开头。每一块的 C 文本都引在翻译它的 Lean 行上方的注释里。

## 一个完整的例子：`syncsearch`

`syncsearch` 是 `zlib/inflate.c` 中 `inflateSync` 的辅助函数。它在缓冲区里搜索模式 `00 00 FF FF`。

```c
local unsigned syncsearch(unsigned FAR *have, const unsigned char FAR *buf,
                          unsigned len) {
    unsigned got;
    unsigned next;

    got = *have;
    next = 0;
    while (next < len && got < 4) {
        if ((int)(buf[next]) == (got < 2 ? 0 : 0xff))
            got++;
        else if (buf[next])
            got = 0;
        else
            got = 4 - got;
        next++;
    }
    *have = got;
    return next;
}
```

它在 `ZlibF/Zlib/inflate.c.lean` 中的翻译：

```lean
/-- `local unsigned syncsearch(unsigned FAR *have, const unsigned char FAR *buf, unsigned len)`.
`have` is the value of `*have`; the result is (return value, `*have` afterwards). -/
def syncsearch (have_ : UInt32) (buf : BPtr) (len : UInt32) : M (UInt32 × UInt32) := do
  -- got = *have; next = 0;
  let (next, got) ← cwhile (σ := UInt32 × UInt32)
    -- while (next < len && got < 4) {
    (fun (next, got) => pure (next < len && got < 4, (next, got)))
    (fun (next, got) => do
      let b ← index8 buf next.toNat
      -- if ((int)(buf[next]) == (got < 2 ? 0 : 0xff)) got++; else if (buf[next]) got = 0; else got = 4 - got;
      let got := if b.toNat == (if got < 2 then 0 else 0xff) then got + 1 else if b != 0 then 0 else 4 - got
      -- next++;
      pure (next + 1, got))
    (0, have_)
  -- *have = got; return next;
  return (next, got)
```

怎样读它：

| C | Lean | 要核对什么 |
| --- | --- | --- |
| 函数返回 `unsigned`，并且可能有未定义行为 | 结果类型 `M (UInt32 × UInt32)` | `M α` 就是 `Heap → Except Fault (α × Heap)`：一个值和新堆，或者 `Fault.ub`，或者 `Fault.outOfFuel`。 |
| `unsigned *have` | 参数 `have_ : UInt32`，以及结果的第二个分量 | 规范化 1。调用者在调用前读出这个单元，在调用后把第二个结果写回去；见下文。 |
| 局部变量 `got`、`next` | 循环状态 `(next, got) : UInt32 × UInt32` | 循环会改动的局部变量作为循环状态携带。`unsigned` 是 `UInt32`。起始状态 `(0, have_)` 就是 `next = 0; got = *have`。 |
| `while (c) body` | `cwhile cond body start` | `cwhile` 检验条件、运行循环体，如此重复，至多检验 `2^64` 次；之后是 `Fault.outOfFuel`。这个循环运行不到 `2^32` 次，因为 `next` 一直增加到 `len`。 |
| `next < len && got < 4` | `next < len && got < 4` | 两个操作数都只读局部变量，所以短路求值的顺序观察不到。 |
| `buf[next]` | `index8 buf next.toNat` | `index8 p i` 是指针算术再加一次读取。`buf` 为 NULL、它的数组已被释放、下标在数组之外时，它都发生故障。C 里的一次越界读取在这里就是 `Fault.ub`。 |
| `else if` 里再读一次的 `buf[next]` | 同一个 `b` | 规范化 2。两次读取之间没有写入。 |
| `(int)(buf[next]) == (got < 2 ? 0 : 0xff)` | `b.toNat == (if got < 2 then 0 else 0xff)` | 提升为 `int` 的字节落在 0..255 内；把两个值当作自然数来比较，结果相同。 |
| `got++`、`4 - got`、`next++` | `UInt32` 上的 `got + 1`、`4 - got`、`next + 1` | 无符号算术在 C 里和在 `UInt32` 里都回绕。这里不需要检查。 |
| `*have = got; return next;` | `return (next, got)` | 见输出参数那一行。 |

`inflateSync` 中的调用处显示了输出参数的另一半：

```c
len = syncsearch(&(state->have), strm->next_in, strm->avail_in);
```

```lean
let (len, hv) ← syncsearch (← rdS st (·.«have»)) z.next_in z.avail_in
wrS st fun s => { s with «have» := hv }
```

`rdS st f` 读状态记录 `*st` 的一个字段，`wrS st f` 把这个记录换成 `f` 作用于它的结果。C 在被调用函数内部写 `state->have`；Lean 在被调用函数刚返回之后写它。这中间没有任何东西读这个字段。被调用函数内部的故障在两边都结束这次运行。

## 第二个例子：有符号算术与记录字段

`zlib/inflate.c` 中 `inflateReset2` 的开头：

```c
    if (inflateStateCheck(strm)) return Z_STREAM_ERROR;
    state = (struct inflate_state FAR *)strm->state;

    if (windowBits < 0) {
        if (windowBits < -15)
            return Z_STREAM_ERROR;
        wrap = 0;
        windowBits = -windowBits;
    }
    else {
        wrap = (windowBits >> 4) + 5;
        if (windowBits < 48)
            windowBits &= 15;
    }

    if (windowBits && (windowBits < 8 || windowBits > 15))
        return Z_STREAM_ERROR;
    if (state->window != Z_NULL && state->wbits != (unsigned)windowBits) {
        ZFREE(strm, state->window);
        state->window = Z_NULL;
    }
```

它的翻译：

```lean
  -- if (inflateStateCheck(strm)) return Z_STREAM_ERROR;
  if (← inflateStateCheck strm) != 0 then return Z_STREAM_ERROR
  let z ← ldZStream strm
  let state ← castInflateState z.state
  let mut windowBits := windowBits
  let mut wrap : Int32 := 0
  -- if (windowBits < 0) { if (windowBits < -15) return Z_STREAM_ERROR; wrap = 0; windowBits = -windowBits; }
  if windowBits < 0 then
    if windowBits < -15 then return Z_STREAM_ERROR
    wrap := 0
    windowBits ← chkI32 (-(windowBits.toInt))
  else
    -- wrap = (windowBits >> 4) + 5;
    wrap ← chkI32 ((windowBits >>> 4).toInt + 5)
    -- if (windowBits < 48) windowBits &= 15;
    if windowBits < 48 then windowBits := windowBits &&& 15
  -- if (windowBits && (windowBits < 8 || windowBits > 15)) return Z_STREAM_ERROR;
  if windowBits != 0 && (windowBits < 8 || windowBits > 15) then return Z_STREAM_ERROR
  -- if (state->window != Z_NULL && state->wbits != (unsigned)windowBits) { ZFREE; window = Z_NULL; }
  let s ← ldInflateState state
  if s.window != .null && s.wbits != i2u windowBits then
    ZFREEB strm s.window
    wrS state fun s => { s with window := .null }
```

| C | Lean | 要核对什么 |
| --- | --- | --- |
| `int windowBits`、`int wrap` | `Int32` | `int` 是 `Int32`。`let mut` 是会被再次赋值的局部变量。 |
| `strm->state` | `ldZStream strm`，然后取字段 `z.state` | 对 `z_stream *` 而言，`ldZStream p` 就是 `*p`。`p` 为 NULL 或它的记录已被释放时，它发生故障。 |
| `(struct inflate_state *)strm->state` | `castInflateState z.state` | 流的状态指针可能指向 inflate 状态，也可能指向 deflate 状态。它指向 deflate 状态时这个转换发生故障：C 会通过错误的类型去读。 |
| `-windowBits` | `chkI32 (-(windowBits.toInt))` | 取负是在无界整数上计算的。结果放得下时 `chkI32` 返回这个 `Int32`，放不下时返回 `Fault.ub "signed integer overflow"`。 |
| `(windowBits >> 4) + 5` | `chkI32 ((windowBits >>> 4).toInt + 5)` | 对加法作同样的检查。在这个分支里 `windowBits` 不为负，所以移位不涉及符号问题。 |
| `windowBits &= 15`，各处比较 | `Int32` 上的 `&&&`、`<`、`>` | 这些运算不会溢出。 |
| `state->window`、`state->wbits` | `ldInflateState state`，然后取 `s` 的字段 | 对记录的一次读取供两次字段读取使用（规范化 2）。 |
| `(unsigned)windowBits` | `i2u windowBits` | `int` 到 `unsigned` 的转换在 C 里有定义：对 `2^32` 取模。 |
| `ZFREE(strm, state->window)` | `ZFREEB strm s.window` | 这个宏调用 `strm->zfree`。只对默认分配器建模：该字段是 `zcfree` 时 `ZFREEB` 释放这个块，是任何其他函数指针时为 `Fault.ub`。释放一个不存活的块会发生故障。 |
| `state->window = Z_NULL` | `wrS state fun s => { s with window := .null }` | 一次字段写入是：读取记录、更新记录、写回记录。 |

C 里提前的 `return` 就是 Lean 的 `do` 块里的 `return`：块中余下的部分不运行。

## 采纳的规范化

**1. 内部函数的输出参数按值传入，并作为第二个结果返回。** 模型里没有指向记录的标量字段或指向标量局部变量的指针。例子是上面的 `syncsearch`：`unsigned *have` 成了参数 `have_` 和第二个结果，由调用者写回。其他用到的地方：`inflate_table`（`table`、`bits`）、`gz_load`（`have`），以及 `inflateBack` 输入回调的 `&next`。

一些公开函数的标量输出参数也用同样的表示：`compress*` 的 `destLen`，`inflateGetDictionary` 和 `deflateGetDictionary` 的 `dictLength`，`deflatePending` 的 `pending` 和 `bits`，以及 `deflateUsed` 的 `bits`。在那里它同时也是模型的一个限制：调用者的单元不是内存，所以一个与某个缓冲区重叠的单元无法表达。[偏离记录](../deviations.md)里有 `compress*` 的那一行。`uncompress*` 的长度单元和 `gzerror` 的 `errnum` 单元是内存：前者是八字节的块，后者是一个四字节的块。

**2. 对同一位置的两次读取，中间没有写入，就算一次读取。** 在 `syncsearch` 里：

```c
        if ((int)(buf[next]) == (got < 2 ? 0 : 0xff))
            got++;
        else if (buf[next])
```

```lean
      let b ← index8 buf next.toNat
      let got := if b.toNat == (if got < 2 then 0 else 0xff) then got + 1 else if b != 0 then 0 else 4 - got
```

C 的两次读取给出同一个字节，并在相同的情形下发生故障，因为两者之间没有任何写入。

**3. 对同一个记录的字段的连续赋值，算一次记录更新。** 在 `inflateSync` 里：

```c
        state->mode = SYNC;
        state->hold >>= state->bits & 7;
        state->bits -= state->bits & 7;
```

```lean
      let h ← shr64 s.hold (s.bits &&& 7)
      wrS st fun s => { s with mode := SYNC, hold := h, bits := s.bits - (s.bits &&& 7) }
```

三条语句写三个不同的字段，每条的右边只读它之前的语句没有写过的字段。所以各个值与 C 中相同。`shr64` 是带检查的移位；这里它的计数至多为 7，所以它不发生故障，它排在更新之前这一点也观察不到。

**4. 同一函数中在前的检验已把某个有符号运算限制在范围之内时，这个运算用普通运算符书写。** 在 `zError` 里（`zutil.c`，经由 `zutil.h` 的宏 `ERR_MSG`）：

```c
#define ERR_MSG(err) z_errmsg[(err) < -6 || (err) > 2 ? 9 : 2 - (err)]
```

```lean
  let i : Int32 := if err < -6 || err > 2 then 9 else 2 - err
```

Lean 的 `Int32` 减法回绕；C 的减法在溢出时未定义。这个减法只在 `-6 ≤ err ≤ 2` 时执行，所以结果在 0..8 内，两者一致。另一处是 `adler32_combine_` 中 `Int64` 上的 `%`，在检验 `len2 < 0` 之后。

没有这种检验的有符号运算使用带检查的辅助定义（第二个例子里的 `chkI32`）。这些辅助定义列在[架构](architecture.md#where-the-trusted-semantics-is)里。

## 整数类型与算术

宏按源码顺序展开。读、写、分支条件、提前返回和短路求值都保留。整数提升和通常的算术转换都明确写出：在这个目标上，`unsigned short + int` 按 `int` 计算。

| C 类型 | LP64 上的 Lean 类型 |
| --- | --- |
| `unsigned char` | `UInt8` |
| `unsigned short` | `UInt16` |
| `unsigned`、`unsigned int` | `UInt32` |
| `unsigned long`、`size_t`、`z_size_t` | `UInt64` |
| `int` | `Int32` |
| `long`、`z_off_t`、`z_off64_t` | `Int64` |

无符号运算按各自的位宽回绕。有符号运算要检查结果是否可表示，规范化 4 的情形除外。移位要检查操作数位宽和计数，包括负的计数。Lean 的算术是全函数；单凭这一点绝不能说明某个 C 运算是正当的。

一个枚举常量有两个名字：一个 `UInt32` 名字用于无符号的状态字段，一个带后缀 `_i` 的 `Int32` 名字用于 C 类型为 `int` 的用法。与枚举常量重名的宏命名为 `GZ_<name>`：`GZ_COPY` 是 `gzguts.h` 的宏，`COPY` 是 `inflate.h` 的枚举常量。

## 每种 C 对象怎样表示

| C 对象或操作 | 表示 |
| --- | --- |
| 结构体 | 它那一种的堆表中的一个记录，按块编号引用 |
| `p->f` 和 `p->f = v` | 记录字段的读取和记录更新，没有 ABI 偏移算术 |
| 内嵌数组 | 一个数组字段；复制记录就复制了它 |
| 指向内嵌数组内部的指针 | 一个指明记录、字段和下标的引用 |
| 字节缓冲区 | 一个堆字节块加一个偏移 |
| `head` 和 `prev` 字数组 | 一个堆字块加一个元素偏移 |
| 静态表 | 一个静态引用或一张带检查的常量表；写入会发生故障 |
| 被取地址的局部变量 | 一个表示出来的对象，在声明处建立，在每个返回之前释放 |
| 字符串字面量 | 指向源码字面量的封闭只读表的 `strLitRef`；不作分配 |
| `ZALLOC` 和 `ZFREE` | 带失败预言的默认分配器；自定义分配器是 `Fault.ub` |

记录类型根据 C 头文件生成（[运行时结构](../runtime-schema.md)）。翻译者通过生成器向结构里添加内容，不另写第二套记录布局。生成的数组字段在类型里不带它声明的长度；这个事实由证明携带。

局部对象不消耗分配失败预言的一次调用：给它 `ZALLOC` 的语义，会改变哪一次真实的分配失败。被取地址的局部变量在它的 C 生命周期结束之后不再存活。

## 新分配的内存

新分配的整数内容是任意的。定理对每个值都成立，包括在 `prev` 的已初始化部分之外、或在匹配前瞻的已初始化部分之外读到或复制的值。翻译不把这些内容换成零。

新分配的指针字段在这个模型里是 NULL。这比 C 弱，在 C 里它是不确定的。对每个从新分配的记录中读出的指针字段，翻译里有一条注释指出此前写它的那条语句，证明则建立这个先后顺序。与 NULL 的比较、复制和 `free(NULL)` 都发现不了没写过的字段。证明不假设对未初始化单元的重复读取结果一致，尽管模型给这个单元一个稳定的值。

对结构中的记录类型 `K`，`K.zeroed` 是 C 中一条真实的整记录清零语句之后的记录，`K.garbage` 是一个新分配的记录。两者不能互换。见[安全，第 3 节](../spec/safety.md#3-faults-undefined-behaviour-and-model-gaps)。

## 库操作

下面的 `K` 代表一种记录，如 `stZStream` 和 `copyInflateState` 中那样。

| C 操作 | 翻译 |
| --- | --- |
| 字节的 `memcpy`、`zmemcpy` | `memcpyB`，带范围检查和不重叠检查 |
| 整记录的 `memcpy` | `copyK dst src`；它检查重叠，这与先读取再写入不同 |
| `memmove` | 移动操作，它允许重叠 |
| 字节的 `memset` | `memsetB` |
| 把更宽的数组清零 | `Ptr.fill p 0 n`，带元素个数 |
| 用字节 `c` 填充更宽的数组 | `Ptr.memset p c n`，它在每个元素里重复 `c` |
| 整记录清零 | `stK p K.zeroed` |

`memcpy` 既复制已初始化的值，也复制任意值。即使复制长度为零，运行时遇到 NULL 也发生故障。建模的操作按元素计数，所以 C 的字节数要换算。它们由 `Libc.lean` 和生成的 `LibcTables.lean` 定义；[可信基础](../trusted-base.md)列出它们与 C 的差别。

## 控制流

循环通过运行时的循环，把它的局部变量放在明确的状态里携带。`do … while` 先运行循环体再检验。循环内的 `break`、`continue` 和 `return` 使用控制标签，这些标签保持它们各自不同的去向。`goto` 要么用一个异常来建模（`inflate` 中的 `goto inf_leave`），要么用一个让某个块再运行一遍的标志来建模（`inflate_fast` 中的 `goto dolen`）。switch 的贯穿是对下一个分支的尾调用。`inflate.c.lean` 和 `inffast.c.lean` 的文件头注释描述了各自的方案。

循环的上界不是提前停下的许可。耗尽是 `Fault.outOfFuel`，终止证明把它排除。C 能到达的每一种未定义操作，在已记录的模型差别之内，都作为 `Fault.ub` 保持可见：指针边界、存活性、对只读对象的写入、无效的比较、有符号算术和重叠的复制。

## 新增或改动一份翻译时要一并提供什么

- 与该 C 文件对应的源码模块。
- 一个函数级的差分测试。
- 注释，把每个翻译决定记在它所涉及的 C 行旁边。

对 `ZlibF/Runtime/` 的改动自成一个提交，写明理由和受它影响的证明，因为每个函数证明都依赖它。只有确认了与 C 不一致，才改动运行时。[检查](../checking/README.md)描述审计和证明变异体。

当一个证明暴露出可能的上游缺陷时，公开定义域保持不变。原因是四种之一：证明技术、错误的规格、翻译不一致，或真实的 C 缺陷。最后一种只有在有具体输入和 sanitizer 复现时，才称为已确认的发现。

[设计](README.md) · [文档首页](../README.md)

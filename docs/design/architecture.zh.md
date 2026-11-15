<!-- source-sha256: fe93506616300088cd97c82ed1a0db1d6b291884077cf4a9b5f58bbc3fd37f82 -->
# 从 C 到已检查的定理

本项目的定理说的是一个 Lean 程序，不是 C 的文本。本页展示这个程序由什么构成，让读者能够判断内核不检查的两个联系：运行时表示了 C 的操作，翻译与选定的 C 源码一致。[可信基础](../trusted-base.md)列出所有依靠审查的东西。

## 各层

```mermaid
flowchart TD
    C["固定版本的 zlib 源码 + 按顺序应用的补丁"] --> T["逐语句翻译"]
    R["运行时：对象、指针、算术、故障、循环"] --> T
    T --> P["执行证明：无故障、终止、帧性质、所有权"]
    T --> F["细化证明"]
    M["不涉及堆的算法模型和 API 模型"] --> F
    S["独立的格式规格"] --> M
    S --> F
    P --> A["公开调用与合法的调用序列"]
    F --> A
```

| 层 | 它的职责 | 它的依据 |
| --- | --- | --- |
| 选定的 C | 确定被验证的是哪个程序 | 固定版本的 `zlib/` 子模块，加上按文件名顺序应用的 `patches/*.patch` |
| 运行时 | 给翻译后的操作以可执行的语义 | 审查和语义回归测试 |
| 翻译 | 保留 C 的语句及其顺序 | 源码审查和差分测试；测试是证据，不是证明 |
| 模型与规格 | 陈述程序做什么，而不限定它的实现方式 | 审查各个定义、定义域，以及它们与 `zlib.h` 和数据格式的关系 |
| 证明 | 把计算与这些陈述联系起来 | Lean 内核的检查和[验收检查](../checking/README.md) |

安全结果只需要经过*执行证明*的那条路径：无故障、终止、帧性质和所有权，并在调用序列上组合。经过*细化证明*的路径给出功能正确性。它不是安全结果所必需的；一个功能性事实，只要有计划内的安全证明依赖它，就在范围内，已经证明的细化结果保留（[范围](../progress.md#scope)）。

## 用几个定义看模型

每个翻译后的函数都由下面这些定义搭成。它们引自 `ZlibF/Runtime/Monad.lean` 和 `ZlibF/Runtime/Space.lean`，略去了 `deriving` 行。

```lean
/-- Why a C computation did not produce a value. -/
inductive Fault where
  /-- undefined behaviour, with a short reason -/
  | ub (what : String)
  /-- a loop used up its fuel (a termination theorem rules this out) -/
  | outOfFuel

/-- A C computation: the heap in, a value and the heap out, or a fault. -/
def M (α : Type) : Type := Heap → Except Fault (α × Heap)

/-- Loop fuel. Large enough that no zlib loop over in-memory data can exhaust it. -/
def fuel : Nat := 2 ^ 64

/-- `while (cond) body` over the loop-carried locals `σ`. The condition may update them (`while (len--)`):
its update happens on every evaluation, including the last, false one, as in C. -/
def cwhile {σ : Type} (cond : σ → M (Bool × σ)) (body : σ → M σ) (s : σ) : M σ :=
  go fuel s
where
  go : Nat → σ → M σ
    | 0, _ => fun _ => .error .outOfFuel
    | n + 1, s => do
      let (c, s) ← cond s
      if c then go n (← body s) else pure s
```

怎样读这些定义：

- 返回类型为 `T` 的 C 函数，翻译后的 Lean 类型是 `M T`：给它一个堆，它返回 `.ok (value, new heap)` 或 `.error fault`。没有别的结果。
- `Fault.ub` 是模型里的未定义行为。凡是 C 操作未定义的地方，运行时的对应操作就返回它：读到对象之外、有符号溢出、重复释放。
- `Fault.outOfFuel` 不是 C 的行为。`cwhile` 至多检验条件 `2^64` 次；如果最后一次检验时条件仍为真，这次运行以 `Fault.outOfFuel` 结束。循环绝不会因为燃料用完而悄悄退出。终止证明表明这个故障不会发生。`cdoWhile` 对 `do … while` 也是这样。
- 安全定理的形状是：“对每个满足前提的堆，这次运行是 `.ok`，并且新堆与旧堆的差别只限于所陈述的那些”。

指向数组内部的指针没有地址：

```lean
/-- A pointer into an array: null, or the array (`R` says where it lives: a heap block, an array inside a
struct, a static table) and an index. There is no address. One past the end is a valid pointer. -/
inductive Ptr (R : Type) where
  | null
  | ref (r : R) (off : Nat)
```

通过这种指针的读取是带检查的（`ZlibF/Runtime/Ptr.lean`；`Space.get h r` 是 `r` 在堆 `h` 中所指的数组，前提是它还存活）：

```lean
/-- `*p`. Faults if `p` is null, dangling, or outside its array (one past the end is not readable). -/
def Ptr.load (p : Ptr R) : M T := fun h =>
  match p with
  | .null => .error (.ub "null dereference")
  | .ref r off =>
    match Space.get h r with
    | none => .error (.ub "read through a dangling pointer")
    | some a => if hk : off < a.size then .ok (a[off], h) else .error (.ub "read outside its object")
```

所以越界读取、通过 `NULL` 的读取和 `free` 之后的读取，都是 `Fault.ub`。一个说“这次运行是 `.ok`”的定理把这三种情况都排除了。`Ptr.store`、`Ptr.add`（指针算术）、`Ptr.diff` 和 `Ptr.lt` 形式相同。字节指针是 `BPtr`；`load8`、`index8` 和 `store8` 是翻译中使用的字节版本。指向结构体的指针，要么是表示 `NULL` 的 `none`，要么是对该结构体的表中某一项的引用。

[翻译](translation.md)把一个 C 函数与它的 Lean 文本并排列出，并逐行解读。

## 选定的源码与模块布局

目标是默认的 x86_64 Linux 静态构建，使用 LP64 位宽和默认分配器。分配失败在范围内。其他构建配置和自定义分配器实现不在计划内；[偏离记录](../deviations.md)记有这一限制。源码子模块绝不改动。只有针对已确认的上游缺陷才允许打补丁，并须遵守仓库的 `AGENTS.md` 和 `patches/README.md` 中的规则。

| 位置 | 职责 |
| --- | --- |
| `ZlibF/Runtime/` | 堆、指针、故障、循环，以及建模的 C 库操作 |
| `ZlibF/Zlib/X.c.lean` | `zlib/X.c` 的翻译；其中没有证明。`deflate.c` 拆成 `deflate_base.c.lean`、`deflate_strategies.c.lean` 和 `deflate.c.lean` 三个文件 |
| `ZlibF/Zlib/X.h.lean` | `zlib/X.h` 的翻译 |
| `ZlibF/Zlib/gzfs.lean` | 供 gz 翻译使用的文件、`errno` 和格式化的模型（[外部 I/O](external-io.md)） |
| `ZlibF/Spec/Safety/` | 必需的安全目标 |
| `ZlibF/Spec/Functional/` | 功能目标，以及不涉及堆的格式模型和 API 模型；不是安全结果所必需的 |
| `ZlibF/Spec/Public/` | 两类目标共用的定义：调用、历史、帧、参数；gz 和 `inflateBack` 的目标也在这里（[规格的布局](safety-functional-split.md)） |
| `ZlibF/Spec/*.lean` | 关于内部函数的陈述。每一条都先对翻译后的函数证明，调用者才使用它（[见下文](#composing-calls-without-assuming-their-answers)） |
| `ZlibF/Proof/X.c.<topic>.lean` | 关于 `zlib/X.c` 的证明 |
| `ZlibF/Proof/public-<name>.lean` | 公开目标的证明 |
| `ZlibF/Math/` | 各证明共用的、不涉及堆的事实 |
| `tests/` | 差分证据、回归和验收检查 |

函数名就是 C 的名字。函数的文档字符串以它的 C 签名开头。

## 可信语义在哪里

本节中的一切都是被信任的：这里的错误内核发现不了。

| `ZlibF/Runtime/` 中的文件 | 内容 |
| --- | --- |
| `Space.lean` | 堆的各张表、指针类型 `Ptr`、函数指针、未初始化整数的值 |
| `Monad.lean` | `Fault`、`M`、`fuel`、`cwhile`、`cdoWhile` |
| `Ptr.lean` | 指针算术、读取、写入、相减、比较 |
| `Address.lean` | 字节指针地址的低三位，CRC 的对齐检验要读它 |
| `Libc.lean`、`LibcStrings.lean` | `malloc`、`free`、`memcpy`、`memmove`、`memset`、`strlen`、字符串字面量、`strerror` 的文本 |
| `Schema.lean`（生成） | 每个结构体的记录、引用类型、静态表、堆 |
| `Tables.lean`、`LibcTables.lean`（生成） | 每种结构体的读取、写入、`malloc`、`free` 和整记录 `memcpy` |
| `Alloc.lean` | `Libc.lean` 的再导出；没有内容 |

生成的文件由 `scripts/gen_schema.py` 根据 C 头文件写出。[运行时结构](../runtime-schema.md)列出每个字段。

有些语义辅助定义不在 `ZlibF/Runtime/` 里。它们定义在使用它们的翻译文件中，被信任的方式相同：

| 辅助定义 | 位置 | 它建模什么 |
| --- | --- | --- |
| 带检查的有符号算术：`chkI32`、`chkI64`；`chk32`、`chk64`、`iadd`、`isub`、`ineg`、`ishl`；`ck`、`shl1`；`i64chk`、`i64add`、`i64sub`、`i64neg` | `inflate.c.lean`；`deflate_base.c.lean`、`inftrees.c.lean`、`inffast.c.lean`；`trees.c.lean`；`gzguts.h.lean` | 有符号结果超出其类型就是 `Fault.ub` |
| 带检查的移位：`shl32`、`shr32`、`shl64`、`shr64`、`shl1i32`、`shlUs`、`shrUs` | `inflate.c.lean`、`inftrees.c.lean`、`inffast.c.lean`、`crc32.c.lean`、`trees.c.lean` | 移位计数超出操作数位宽就是 `Fault.ub` |
| 模式单子 `X` 及其循环 `xwhileBrk`、`xwhile`、`xdoWhile`、`xloopBrk` | `inflate.c.lean`（`infback.c.lean` 也使用） | `inflate` 的大 `switch` 内部的 `break`、`goto inf_leave` 和 `return`；建立在 `cwhile` 之上 |
| `gwhile`、`gdoWhile` | `gzfs.lean` | 供同时携带文件系统世界的计算使用的 `cwhile` 和 `cdoWhile`；燃料相同 |
| 自动存储：`allocLocalB`、`allocLocal`、`allocLocalZ` | `inflate.c.lean`、`gzguts.h.lean`、`compress.c.lean`、`uncompr.c.lean` | 局部数组或局部 `z_stream`：一个新分配的对象，不消耗分配失败预言的一次调用 |
| 外部世界：`Fs`、`open`、`read`、`write`、`lseek`、`close`、`snprintf`、`vsnprintf`、`strerror` | `gzfs.lean` | [外部 I/O](external-io.md) |

每个翻译文件都在文件头注释里写明它的预处理选择和建模决定。

## 为什么用对象堆

C 的结构体用 Lean 的记录表示。一个堆（`Schema.lean` 中的 `Heap`）包含：

- 一张字节块的表（`unsigned char` 数组：缓冲区、窗口、字符串），以及一张记录它们只读标志的表；
- 一张 16 位字的块的表（`head`、`prev`）；
- 每种结构体各一张表：`z_stream`、`gz_header`、`deflate_state`、`inflate_state`、`gz_state`；
- 静态表；
- 分配状态：下一个未用的块编号、到目前为止的分配调用次数、失败预言（`allocOk n` 说明第 `n` 次调用是否成功）和新分配的内存的内容（`garbage`）。

其他数组是记录的字段或静态表。一个指针指明一个堆块、一个记录内的数组或一个静态数组，再加上元素下标。

```mermaid
flowchart LR
    P["指针：null，或引用 + 下标"] --> B["堆上的字节块/字块"]
    P --> E["嵌在记录里的数组"]
    P --> S["静态数组"]
    H["堆"] --> B
    H --> K["记录表：流、inflate 状态、deflate 状态……"]
    K --> E
    H --> O["分配预言、新块计数器、垃圾值"]
```

这样，字段更新和帧性质都很直接。记录的字段是一个投影；改它就是一次记录更新。一次字节写入改不了另一张表里的记录。复制整个记录也复制它内嵌的数组。

这种表示没有 ABI 字节偏移。所以它给不出结构体的字节视图，也表示不了标量单元与缓冲区之间的每一种别名。记录类型不强制数组字段的长度：`WellFormed`、`Heap.RecordsWellFormed` 和 `Statics.WellFormed` 陈述这些长度，证明要么带着它们，要么从自己的表示不变量推出它们。

## 执行与故障

| 操作 | 表示出来的行为 |
| --- | --- |
| 指针算术 | 留在同一个存活数组之内，包括它的末尾后一位；解引用末尾后一位会发生故障 |
| 读取和写入 | 检查存活性和边界；写入还检查只读状态 |
| 指针相减和比较大小 | 要求同一个存活数组和有效的偏移；差值必须能放进 `ptrdiff_t` |
| 指针相等 | 结构相等；不同的引用构造子比较结果为不相等 |
| 无符号算术 | 按 C 的位宽回绕 |
| 有符号算术和移位 | 由上表中的辅助定义检查，它们在翻译文件里 |
| 复制和填充 | 检查范围和可写性；`memcpy` 还检查不重叠 |
| 分配 | `malloc` 询问失败预言，并拒绝 `2^63` 字节或更大的请求；成功时给出一个新的块编号。在不满足 `Fresh` 的堆上它发生故障 |
| 释放 | 接受 NULL；否则要求是一个存活可写块的起始位置 |
| 循环 | 至多检验条件 `2^64` 次；耗尽是故障，绝不是普通的退出 |

[安全的定义](../spec/safety.md)说明定理对这些结果陈述了什么。

## 模型与 C 不同的地方

这些是模型的限制，不是对 C 额外的断言。权威的细节在[可信基础](../trusted-base.md)和[偏离记录](../deviations.md)里。

| 差别 | 对证明的后果 |
| --- | --- |
| 新分配的整数单元取任意值 | 定理对每个 `garbage` 函数量化；绝不假设它为零 |
| 每个新分配的单元在一次运行中始终保持同一个值 | 证明不依赖重复的未初始化读取结果一致 |
| 新分配的指针字段是 NULL | 证明表明指针字段在被读之前已被写过；单凭一次与 NULL 的比较表明不了这一点 |
| `NULL + 0` 成功；一般的 `NULL - NULL` 发生故障 | 唯一允许 `NULL - NULL` 的那处翻译单独审查（[缓冲区](../proof/buffers.md)） |
| 相等比较没有相邻对象地址的情形 | 没有哪个 C 分支是靠来自不同对象的指针相等来论证的 |
| 没有一般的地址、对齐或类型标签 | 类型转换和对地址敏感的路径逐一明确审查；结构体没有一般的字节视图 |
| CRC 观察地址的低位 | 堆字节块的起点是对齐的；静态字节数组和内嵌字节数组的起点余数任意但稳定。一般的 ABI 布局，以及按严格别名规则对那处字转换的解读，都在模型之外 |
| 只读状态覆盖字节块和静态对象 | 堆记录或字块在模型里从不只读 |
| 块编号从不重用 | 做分配的代码带着 `Fresh`；初始堆中各对象的身份互不相同 |
| 库的复制操作按元素计数 | C 的字节数要换算；整记录的 `memcpy` 使用检查重叠的记录复制 |

自动存储保持它的 C 生命周期，不消耗分配失败的序号。地址被传给某次调用的局部对象是一个表示出来的对象，在每个返回处被释放。没有哪个证明靠悄悄收窄公开定义域来弥补表示上的缺口。

## 设计决定

较早的笔记把这些决定称为 D1 到 D6。下表给出每个决定及其后果。

| | 决定 | 后果 |
| --- | --- | --- |
| 1 | 对象堆，每种记录一张表 | 表示出来的操作依靠审查；记录与字节缓冲区之间的别名无法表达 |
| 2 | 证明自动化是局部的 | 每个生成的证明项都由内核检查；没有哪个被假定正确的验证条件生成器来代替证明 |
| 3 | C 由人工逐语句翻译 | 对应关系依靠审查；差分测试是证据 |
| 4 | 压缩器中相互重叠的待输出存储和符号存储按 C 的方式建模 | 它的生命周期和不被覆盖的条件，对每个允许的内存级别都作了证明（[trees](../proof/trees.md)） |
| 5 | 新分配的整数单元取任意值，新分配的指针是 NULL | 定理对整数垃圾值量化；证明表明指针在被读之前已被写过 |
| 6 | 记录没有 ABI 字节布局 | 记录的字节视图，以及标量与缓冲区之间的别名，都在模型之外 |

## 组合调用而不假设其结果

辅助函数的定理说的是翻译后的辅助函数本身。它的调用者先证明该辅助函数的前置条件，再使用这条定理。没有哪个辅助函数的契约是用来代替执行的假设。[内部义务](../spec/internal-contracts.md)列出调用者要建立的条件。

每种状态记录有一个表示不变量，它带着边界、所有权和后续调用需要的历史。初始化函数建立它，后续调用保持它，结束函数释放所拥有的存储。因为初始化函数建立了它，这个不变量是能够成立的。序列定理把这些函数定理组合起来，包括拒绝和分配失败的情形。方法见[证明指南](../proof/README.md)，已检查、已登记和已验收这三个级别见[检查](../checking/README.md)。

[设计](README.md) · [文档首页](../README.md)

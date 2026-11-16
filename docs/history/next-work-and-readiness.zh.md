<!-- source-sha256: 64516110a58e5eafaa9febd692b650f4434c4b40ea6730e82c555dbd7d676c2b -->
# 早先的工作顺序与准备情况说明（历史）

本页保存[进度](../progress.zh.md)“剩余工作”“按顺序的下一步工作”和“公开 API 的证明准备情况”三节早先的文字，以及“核心证明骨架”的引言，内容是必需目标在 `bde170e9` 上通过验收之后的原文，除相对链接外未作改动。
这是历史记录：其中的状态（如 open、checked、“未完成”“已检查”）、工时、数字和日期反映各条目写作时的情况，不是当前状态。
当前状态和剩余工作只在[进度](../progress.zh.md)中。

## 剩余工作

红色边框表示已经记录了阻碍证明的问题，下文给出证据和下一步。证明尝试耗时很长，本身不构成这种阻碍。灰色目标可以开始推进；它们缺少的内部引理和调用序列不变量并没有全部画在图中。

### 核心证明骨架

2026-11-11 的范围变更：只有安全在计划内（见[范围](../progress.zh.md#scope)）。仍未完成的功能性行标为"不在计划内"，不计工时；已检查的行保持不变。

### 按顺序的下一步工作

每个必需目标都已登记（63 个必需目标，没有未完成的；2026-11-14）。计划内的第 9 至 12 行中，现已登记的目标是 `deflateInit2_`、`deflate_initialisation_domain`、`inflateCopy`、`deflateCopy`、`inflate`、`deflate`，以及所列其他调用的安全目标（`inflate_sequence_safety`、`deflate_sequence_safety`、`inflateSync_safety`、`deflateParams_safety`、`uncompress*_safe`、`compress*_safety`、`inflate_back_sequence_safety`）。其中剩下的都是功能性的，不在计划内：`inflate_sequence`、`deflate_sequence`、`uncompress*`、`compress*`、`inflateBack`、`inflate_back_sequence` 以及各功能性自身目标。第 1 至 5 行和第 13 行属于 gzip 文件接口：它们的安全在计划内（第 5 项），按 [gz 骨架](skeleton-gz.zh.md#gz) 进行，而不按本表；它们的功能契约不在计划内。第 6 至 8 行和第 10 行只在某个 sequence 目标需要时才做。

按顺序排列。“前提”是必须先证明的内容，绝不是假设的契约。“负责 PR”是承载该工作的拉取请求（如已存在）。

| # | 目标 | 前提 | 负责 PR |
| ---: | --- | --- | --- |
| 1 | `gzopen`、`gzopen64`、`gz_initialisation_domain` | 功能契约，不在计划内；`gz_initialisation_domain` 不是必需目标（见[范围](../progress.zh.md#scope)）。陈述已修正（见 [gzip 打开路径长度](specification-review.zh.md#gzip-open-path-length)）。接下来是 `gz_open` 的路径打开（`fd = -1`）分支：`fsOpen` 的结果以及追加/读取定位，复用 `gzdopen` 的组合 | — |
| 2 | `gztell`、`gztell64` | 从每个允许的 gz 调用历史（打开、读、写、定位、回退）推出 `PosInv` | — |
| 3 | `gzclose_r` | 读端缓冲区在调用历史上的归属，然后是已初始化读端上的 `inflateEnd` | — |
| 4 | `gzseek`、`gzseek64` | 第 2 项的 `PosInv` 和缓冲区不变式；透明路径与缓冲路径 | — |
| 5 | `gzread`、`gzfread`、`gzgetc`、`gzgetc_`、`gzgets`、`gzungetc`、`gzdirect`、`gzwrite`、`gzfwrite`、`gzputc`、`gzputs`、`gzprintf`、`gzvprintf`、`gzflush`、`gzsetparams` 的透明路径 | 延迟初始化与缓冲区不变式；压缩路径等待第 12–13 项 | — |
| 6 | `deflatePrime` | 在 `DGood` 下的待输出字节压缩与位插入 | — |
| 7 | `deflateBound`、`deflateBound_z` | 执行公式与饱和上界的对应，包括头部字符串 | — |
| 8 | `deflateSetDictionary` | 在 `DGood` 下的窗口填充、散列插入与输入恢复 | — |
| 9 | `deflateInit2_`、`deflate_initialisation_domain` | 已登记。原为：参数规范化、五次分配、清理，以及对每组参数建立 `DGood` | — |
| 10 | `inflateCopy`、`deflateCopy` | 已登记。原为：分配失败、缓冲区复制、指针重定位、独立归属 | — |
| 11 | `inflate` → `inflate_sequence` → `inflateSync`、`uncompress*`、`inflateBack`、`inflate_back_sequence` | 由实际 `inflate_table` 得到的表含义；覆盖所有模式的单一调度循环不变式 | — |
| 12 | `deflate` → `deflate_sequence` → `deflateParams`、`compress*` | `fill_window` 与滑动；以级别、`memLevel`、`windowBits` 为参数的单一策略循环不变式；块输出 | — |
| 13 | 压缩 gz 路径、`gzclose_w`、`gzclose`、`gz_sequence` | 第 11 和 12 项 | — |

当陈述修正会改变需要证明的内容时，先做修正。尚未解决：依赖 `detectLag = 8` 的 `Api.Goal.inflate_rejects_invalid`（已检查的反例表明该常数有误；[API 模型](../design/api-model.md)）。下文的 gzip 打开路径长度问题已修正。`inflateInit2_` 与 `Api.Goal.gz_seek_read` 已修正并通过检查，等待登记。

早先的叙述性检查点（关于 inflate、deflate、树、CRC、差分框架和集成的分领域说明）保存在[进度检查点](progress-checkpoints.zh.md)中，属于历史记录，其中的数字不是当前数字。

### 公开 API 的证明准备情况

**灰色表示尚未证明，不表示无法推进。可以立即开展独立工作。** 被调用函数呈绿色，并不意味着调用者自身的前置条件、循环、返回结果和内存效果已经建立。一个能直接调用的 API，仍可能存在错误的契约或已确认的源码缺陷；只有这类证据才足以给目标加上阻碍边框。不能只凭图中缺少箭头判断证明准备情况。

[证据索引](../progress.md)区分证明引用、C 调用和规格引用。下面列出需要组合的证明义务，这些义务与精确目标的连接尚未完成。它们不会引入新的公开调用假设，也不会赋予目标任何已检查的输入覆盖范围。

#### 打开、查询与关闭操作的前提

证明打开文件不需要先完成整个引擎。主要工作在公共辅助函数 `gz_open`：模式解析循环、真实分配、字符串复制、文件描述符效果，以及初始化不变量。位置查询尚缺的基础，是覆盖所有允许调用序列的位置不变量。关闭操作尚缺的基础，是覆盖这些调用序列的所有权事实，其中也包括分配失败。

目前本地执行证明已覆盖：

- [打开入口](../../ZlibF/Proof/gzlib.c.open.lean)：NULL 参数、负文件描述符和第一次分配失败。结论给出未改变的文件系统和精确堆状态，也包括分配尝试计数器。
- [读模式关闭](../../ZlibF/Proof/gzread.c.close.lean)：NULL、模式不匹配，以及在 `GzGood` 条件下完整的未缓冲执行。范围包含文件描述符错误，释放消息、路径和句柄，以及无关分配保持不变的框架性质。
- [位预置入口](../../ZlibF/Proof/deflate.c.prime.lean)：在压紧待输出字节之前，拒绝流状态和非法位数的分支。

这些是具有明确内部范围的结果，并不是完整公开目标的证明。特别是，仍须从允许的公开调用序列推出 `GzGood`。不能凭一个分支的结果，就把灰色公开节点改成绿色。

#### 每个未完成公开目标的下一步

“开始”表示无需等待完整引擎定理就能开展的工作。“组合”列出完整收束目标所需的前提；其他独立分支仍可推进。表中任何一行都不授予已检查状态，也不把被调用函数的规格当作假设。

<!-- proof-readiness:start -->
| 公开目标 | 图中所示证明工作 | 下一步与缺少的前提 |
| --- | --- | --- |
| `gzopen`, `gzopen64`, `gz_initialisation_domain` | 开始：打开与清理 | <a id="readiness-gzopen"></a> **陈述已修正：**见 [gzip 打开路径长度](specification-review.zh.md#gzip-open-path-length)。**开始：**`gz_open` 的路径打开分支（`fsOpen` 结果、追加与读取定位），复用已登记的 `gzdopen` 模式循环、分配与 `OpenState` 组合。上文的入口与失败分支已经过本地检查。 |
| `gztell64`, `gztell` | 需要：位置约束 | <a id="readiness-gztell64"></a> **组合：**从读取、写入、定位和回退字节的调用序列推出位置不变量 `PosInv`，再复用现有算术执行证明。 |
| `gzclose_r` | 需要：资源归属 | <a id="readiness-gzclose-r"></a> **开始：**已初始化缓冲区的清理，以及从调用序列建立其所有权的证明。未缓冲执行及框架性质已有本地检查；仅有 `inflateEnd` 还不够。 |
| `gzclose_w`, `gzclose` | 需要：交付与清理 | <a id="readiness-gzclose-w"></a> **组合：**实际补零、最终压缩和文件写入，全部清理与错误路径，再利用两个完整的关闭结果证明分派操作。 |
| `gzseek64`, `gzseek` | 需要：定位与状态序列 | <a id="readiness-gzseek64"></a> **开始：**位置与指针的状态序列不变量、缓冲和透明模式路径，以及精确的错误框架性质。负位置的可达性与溢出复核复核尚未完成。 |
| `gzdirect`, `gzread`, `gzfread`, `gzgetc`, `gzgetc_`, `gzgets`, `gzungetc` | 需要：读取路径证明 | <a id="readiness-gzdirect"></a> **开始：**公共延迟准备、透明模式读取，以及缓冲区与状态序列不变量。**组合：**压缩路径中的实际解码执行，再建立 EOF、计数、字节回退和错误条款。`gzdirect` 需要格式探测与初始化，不需要完整的数据解码循环。 |
| `gzwrite`, `gzfwrite`, `gzputc`, `gzputs`, `gzvprintf`, `gzprintf`, `gzflush`, `gzsetparams` | 需要：写入路径证明 | <a id="readiness-gzwrite"></a> **开始：**缓冲、格式化、透明模式写入及失败情况。**组合：**压缩输出与参数变更中的实际压缩器执行。 |
| `deflateInit2_`, `deflate_initialisation_domain` | 开始：初始化与分配 | <a id="readiness-deflateinit2"></a> **开始：**参数归一化、五次分配、全部失败清理、实际建立 `DGood` 和树状态，以及具体见证。重置证明要求不变量已经成立，并不会为新分配的存储建立它。 |
| `deflatePrime` | 开始：压紧与位操作 | <a id="readiness-deflateprime"></a> **开始：**待输出字节的压紧、带检查的移位、位插入与交付，以及不变量和框架性质的保持。拒绝分支已有本地检查；接受的位数范围仍未完成。 |
| `deflateBound_z`, `deflateBound` | 开始：上界与头部审查 | <a id="readiness-deflatebound-z"></a> **开始：**把现有执行公式连接到具有饱和语义的数学上界，包括头部字符串与额外字段长度。额外长度复核复核尚未完成，并不是新确认的阻碍。 |
| `deflateSetDictionary` | 开始：窗口与哈希 | <a id="readiness-deflatesetdictionary"></a> **开始：**填充窗口、插入哈希链、恢复保存的输入，再处理校验和以及精确的状态和框架效果。绿色校验和调用只覆盖其中的校验和部分。 |
| `inflateCopy`, `deflateCopy` | 开始：复制与重定位 | <a id="readiness-inflatecopy"></a> **开始：**分配失败、缓冲区复制、指针重定位及独立所有权。在声称覆盖完整定义域之前，解决已记录的复制与状态序列调查；不能悄悄增加前提。 |
| `deflateParams` | 需要：块交付与参数状态 | <a id="readiness-deflateparams"></a> **组合：**实际交付旧块、处理返回码，并更新规范的调参表行。在完整收束之前，检查拒绝路径精确保持了哪些状态。 |
| `inflateSync` | 需要：扫描与状态序列 | <a id="readiness-inflatesync"></a> **开始：**组合现有的首次扫描与恢复扫描、暂存位、标记搜索、重置，以及记账和框架结果。从调用序列推出窗口与重置前提。 |
| `compress2_z`, `compress2`, `compress_z`, `compress` | 需要：压缩器执行 | <a id="readiness-compress2-z"></a> **开始：**参数、标量长度和清理。**组合：**实际初始化、压缩和结束操作及精确输出，再处理外层封装。抽象的往返性质还不够。 |
| `uncompress2_z`, `uncompress2`, `uncompress_z`, `uncompress` | 需要：解码器执行 | <a id="readiness-uncompress2-z"></a> **开始：**标量结果、空间不足和清理。**组合：**实际初始化、解压和结束操作、精确消费量与输出，再处理外层封装。 |
| `inflate`, `deflate` | 需要：分派不变量 | <a id="readiness-inflate"></a> **组合：**解码表或哈希链的含义、分派不变量、循环终止，以及输出和记账。绿色校验和目标不能建立这些前提。 |
| `inflate_sequence`, `deflate_sequence`, `inflate_back_sequence`, `gz_sequence` | 需要：执行与格式 | <a id="readiness-inflate-sequence"></a> **组合：**每次实际调用的安全性、状态序列保持、向独立格式模型的精化，以及跨输入输出分块的完成性质。 |
| `inflateBack` | 需要：表、窗口与回调 | <a id="readiness-inflateback"></a> **组合：**压缩块的 TABLE/LEN 执行、窗口内部的输出、公开回调所有权、循环终止和精确的输入输出记账。现有 stored 块和入口路径仍可独立推进。 |
<!-- proof-readiness:end -->

近期顺序是：先推进独立的入口、清理和算术路径，再建立公共的打开、位置和所有权不变量，最后完成整函数组合。回调压缩块可以并行推进。如果某个前提尚不清楚，应在这里记录精确问题；不能凭空制造依赖，也不能把经过的时间当作存在阻碍的证据。

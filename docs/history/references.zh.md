<!-- source-sha256: 3ea8d5c4ff9bb576370eb189f1c479fee1fe479561278ea81b593c54b169ed8d -->
# 早期论证与参考来源（历史记录）

本页是历史记录。它说明一个早期开发中有哪些思路和论证族在本仓库中被借鉴。它不给出本仓库的任何结果。各表中“当前的源文件族”一列描述的是写下这份记录时各模块的样子：有若干单元格早于 gz 安全结果（[gzip 文件](../proof/gzip.md)），gzip 那张表尤其如此。

主要的源码快照是 [zlib-formal 的 `0f1428677ebf5b1614ff77f4702bbb382b2bf3c6`](https://github.com/cla7aye15I4nd/zlib-formal/tree/0f1428677ebf5b1614ff77f4702bbb382b2bf3c6)。参考审查阅读了它的源码和审计文档。审查没有重新构建这个快照，也没有在本仓库中建立它的结果。

[证明指南](../proof/README.md)列出本仓库的定理，[检查](../checking/README.md)定义验收。页末的观察是历史上的测试证据。它们不是证明，也没有针对当前的源码重做。

## 借鉴的思路

| 参考来源 | 这里的改编 | 边界 |
| --- | --- | --- |
| `Spec/Api/InflateApi.lean`：`Call`、`exec` | `ZlibF/Spec/Public/Calls.lean` 中封闭的公开调用字母表和直接分派 | 覆盖了入口，并不证明每个入口或某个序列 |
| `translation_map.py` | 清单检查公开名称、定义所在的文件和手册章节 | 这不是对预处理后语法的完整比较 |
| `check_imports.py` | 检查根模块的传递导入闭包和缺失的源文件 | 闭包中的源模块不一定证明了它的公开目标 |
| `final_check.sh` | 区分开发、规格就绪和最终验收 | 快速构建不是最终验收 |
| `Spec/crc32.lean`、`Spec/adler32.lean` | 独立的校验和规格：位／寄存器形式，以及模和形式 | 保留非规范的种子，以及 Adler 单字节情形的特殊行为 |
| `check_axioms.py` | 拒绝空的或重复的登记表；避免检查被优化禁用；检查已登记名称之外的声明 | 仅凭登记不能验证一条陈述的定义域或翻译的忠实度 |
| `Witness/`、`CONTRACT_AUDIT.md` | 在序列目标旁边设立初始化定义域目标和非空性要求 | 实际的初始化必须建立各调用所用的同一个不变量 |

表中使用相对于参考仓库 `lean/` 目录的路径。下一节之后的各表对应各函数族和改变了的表示。

## 不能照搬的部分

参考仓库的堆使用带类型（带标签）的单元和字节块。当前的堆使用对象记录和表。关于堆的陈述和证明项需要改编：堆层面的证明需要新的执行论证、帧论证和所有权论证。纯算术、位流关系、循环度量和分解，只有在比较过它们的定义和定义域之后，才能保留原来的含义。

参考仓库的序列定理 `Zlib.Api.seq_safe` 把 `ApiContract` 当作假设。它的契约审计记录了前置条件为假的实例和错误的策略契约。调用字母表和归纳结构是有用的。一条带条件的序列定理并不能在这里建立安全性：库内每个被调用的函数都需要一条关于其实际翻译的定理，而实际的初始化必须建立不变量。无关的见证提供不了这一联系。

参考仓库的 `ub.patch` 策略和启用的补丁与这里不同。它的构建配置和证明状态不能照搬。本仓库验证自己固定的上游版本加上经过审查的补丁，使用自己的公开定义域和验收规则。

```mermaid
flowchart LR
    R[固定版本的参考仓库] --> M[提取数学内容和论证结构]
    M --> T[针对当前的源码和堆重新陈述]
    T --> K[内核检查、审计和变异体]
    K --> C[只接受针对本仓库的证据]
```

下面各表指出可复用的论证族在哪里。[各组件的证明指南](../proof/README.md)解释本仓库的论证结构。参考链接和历史上报告过的测试，都不是一次新的验证运行。

## Deflate 引擎的来源

| 来源族 | 数学内容或操作内容 | 当前的源文件族 |
| --- | --- | --- |
| `EngineChains` | 滚动哈希在三次更新之后遗忘旧值；掩码后的键的界；键与前两个字节一致时第三个字节也一致 | `deflate.c.engine.hash` |
| `EngineChains`、`Spec/deflate/Engine` | 环形槽位的算术；链的可达性；插入和滑动对它的保持；链上位置递减 | `deflate.c.engine.chains` |
| `EngineFillSlide`、`EngineFill` | 滑动阈值、读取计数、插入计数、`high_water`，以及滑动复制的范围互不相交 | `deflate.c.engine.window` |
| `EngineMatch`、`matchChain_spec`、`innerLoop_spec` | 第一处不匹配、每轮八次比较、最大长度 258 和结果的钳制 | `deflate.c.engine.match`、`.lminner`、`.lmcond`、`.lmbody`、`.lmmain` |
| `PendingPut`、`DeflatePut`、`Hash`、`LmInit` | 待输出字节的顺序、哈希更新、插入时的存储和清零 | `deflate.c.engine.macros` |
| `EngineSlide` | 每个哈希表项变为 `m >= w_size ? m - w_size : 0`；精确的帧 | `deflate.c.engine.slide` |
| `EngineReadBuf` | 复制 `min(avail_in, size)` 个字节，推进输入计数器，并更新所选的校验和 | `deflate.c.engine.readbuf` |
| `PendingFlush` | 冲刷树的位，复制待输出字节，推进输出计数器，并在待输出区为空时重置其指针 | 待输出字节的复制，以及树的位缓冲区证明 |

## Deflate 生命周期的来源

| 早期来源 | 保留的内容 | 当前的源文件族 |
| --- | --- | --- |
| `Inv`、`Inv7`、`Heap` | 回指指针、缓冲区分离、范围、存储对它们的保持，以及帧 | `deflate.c.base` |
| `StateCheckQuick`、`End` | 对空流和无效流的拒绝；状态检查的精确结果 | 基础检查引理 |
| `TuneQuick`、`HeaderQuick`、`UsedQuick`、`PendingQuick`、`Simple` | 四次调优存储；仅限 gzip 的头部存储；可选的输出存储；待输出计数的溢出 | `deflate.c.life.check` |
| `Bound` | 包装长度、`extra_len` 的低 16 位、带结尾符的字符串和上界的算术 | `deflate.c.life.bound`，包括 `boundTail` 和 `WrapLen` |
| `InitParams`、`Init*` | 参数规范化、二的幂、缓冲区大小和配置表的范围 | 支撑初始化和基础不变量的算术 |
| `End` | 依赖状态的精确结果、五次释放，以及清空流的状态指针 | `deflate.c.life.end` |
| `LmInit`、`Reset*`、`ResetTr` | 哈希清零、调优表、计数器、包装状态和树的重置 | `deflate.c.life.reset` |
| `InitFail*`、`InitOk*`、`InitMem`、`InitFresh` | 每一次失败的分配及其清理；成功时的精确状态 | 初始化的论证结构 |
| `Prime*`、`PrimeArith` | 移动待输出字节；保持它们的位值；追加所请求的低位 | priming 的算术和执行分解 |
| `Copy*` | 拒绝、失败清理、互相独立的缓冲区和重定基址的树指针 | 复制的论证结构 |
| `DictGet`、`GetDictQuick` | 从窗口末尾返回 `min(strstart + lookahead, w_size)` 个字节 | `deflate.c.life.getdict` |

## Inflate 的来源

| 早期论证族 | 内容 | 当前的源文件族 |
| --- | --- | --- |
| `natBits`、`bytesBits`，移位和掩码引理 | 低位列表、字节追加、丢弃位和格式的位序 | `inflate.c.main.bits` |
| `InflateBits` | `PULLBYTE`、`NEEDBITS`、`BITS`、`DROPBITS`、`BYTEBITS`、`INITBITS`；保持“持有的位后接未读字节”；补充和消耗位而不改变所表示的流 | `inflate.c.main.macros` |
| `InflateTopLoop`、`InflateLoop` | 递减的度量和每一个循环出口 | `inflate.c.main.xloop` |
| `SpecStored`、`SpecStoredCopy`、`Copy*` | 存储块的长度／补码检查，以及复制的字节不变 | `inflate.c.main.stored`、`.stored2` |
| `InflateHead`、`InflateHdr*`、`InflateName` | 头部检查、字段长度、可选的头部写入和 CRC | 各模式的论证和头部算术 |
| `InflateTable`、`InflateTables`（约 1,161 行）、`InflateCodeLens*` | 动态块的计数、码长顺序、重复和表的安装。`LENLENS` 读取 `min(ncode - have, available_bits / 3)` 组；顺序置换、`lensRead`、`lensZero`、`Good3`；读取循环和补零循环 | `inflate.c.main.table` 到 `.table6` |
| `InflateLen*`、`InflateDist*`、`InflateMatch*` | 慢速查表、子表、距离检查，以及窗口／输出的复制 | 符号、查表和复制的论证结构 |
| `InflateCheck`、`InflateCheckStep` | 输出总数、校验和更新和尾部比较，包括字节交换后的 zlib 比较 | `inflate.c.main.check0`、`.check` |
| `InflateCases1`、`InflateUpd`、`InflateFixed` | 简单模式、分派、拒绝和固定表的选择 | 简单模式／类型模块和固定表定理 |
| `infLeave_ok`、`leaveTail_ok`、`updatewindow_frame` | 寄存器写回、窗口更新、计数器和返回码规则 | 收尾部分的组合论证 |

## 回调的来源

| 早期论证族 | 可复用的内容 | 当前的源文件族 |
| --- | --- | --- |
| 初始化检查与分配 | 对版本、大小和参数的拒绝；内存失败；成功时存入的精确字段 | `infback.c.init` |
| 结束与入口处的退出 | 对无效流／状态的拒绝；释放状态并清空指针 | `infback.c.end`、`.back` |
| 第一次输入耗尽 | `in` 没有给出字节、缓冲区错误、输入字段被恢复、没有输出回调 | `infback.c.back` |
| 回调契约与见证 | 自有的块集合和局部不变量；一个具体的已初始化例子 | `infback.c.callbacks` |
| 输入宏 | 补充／消耗位、回调转移和剩余输入的度量 | `infback.c.pull`、`.macros` 以及共用的 inflate 位引理 |
| 输出空间与窗口写入 | 把写满的窗口冲刷到 `out`，保持先前的输出，并延伸输出视图 | `infback.c.room`、`.stored` |
| `TYPE`、固定表和错误模式 | 末块判定、块类型、固定表字段和错误消息 | `infback.c.inv` 和 `inflate_fixed_ok` |
| 存储块与码长顺序 | 对齐、补码检查、有界的分段复制；顺序置换 | `infback.c.pure`、`.stored` |
| 动态表与慢速查表 | 计数、重复、构造函数调用，以及规范的根表／子表的一致 | 早期的论证结构，需要针对当前的表语义重新陈述 |
| 分派与离开 | 下降的循环度量；最后一次输出回调；精确的结果和输入写回 | 当前的循环规则和组合论证 |

## Gzip 的来源

| 早期论证族 | 可复用的内容 | 当前的源文件族或边界 |
| --- | --- | --- |
| `Basic` | 字段布局和标签 | 被记录访问和流引用取代 |
| `Simple` | 缓冲区设置、EOF、tell、错误查询和整数界限 | `gzlib.c.simple` |
| `Error`、`ErrorMsg` | 释放旧消息；存入代码；分配并格式化 `path: text`；分配失败 | `gzlib.c.error` 覆盖空消息路径；格式化的消息需要精确的格式化语义 |
| `Reset`、`Rewind` | 重置字段和错误、拒绝规则、文件定位和按输入调整的偏移量 | `gzlib.c.error`、`.rewind` |
| `SeekParts`、`SeekRaw`、`SeekFwd`、`SeekBack`、`SeekTail`、`SeekMain`、`SeekCor` | 目标位置的算术，以及原始、向前和向后三个分支 | `gzlib.c.seek` |
| `SeekNeg`、`SeekNegUb`、`SeekFault`、`SeekWitness` | 负的位置和有符号溢出路径 | 带条件的精确故障引理，不是公开的安全定理 |
| `OpenMode`、`OpenParts`、`OpenRest` | 对模式字符的折叠，以及遇到 `+` 时的清理 | `gzlib.c.open-mode` 和打开操作的论证结构 |
| `OpenPath`、`OpenDesc`、`OpenFinish`、`OpenEff*`、`GzopenEff*`、`Dopen*` | 路径复制、描述符标志、追加／截断的效果和失败清理 | 精确的格式化、文件效果和所有权必须能够组合 |
| `Close`、`Dispatch` | 读端／写端的分派和存活块的核算 | `gzclose.c`；读端／写端实际的清理属于它们各自的文件 |

## 历史上的短距离检查

早期的记录报告了一次实验，针对的是一个候选问题：快速路径之前漏掉了对 `whave` 的更新。实验用的是原始的固定 Huffman 流：一到三个字面量，后接一个长度为三、距离为一到四的匹配。测试矩阵包括：至少有六个输入字节和 258 字节输出空间的快速调用，每次只给一个字节的拆分输入，以及使用新输出缓冲区的两次调用解码。记录报告说各路径结果一致，得到了预期的“invalid distance too far back”错误，sanitizer 也没有发现问题。

那次实验只在这些普通 `inflate` 的情形上否定了这个候选问题。它没有覆盖长距离、写满或回绕的窗口、其他窗口大小，也没有覆盖回调解码器。它是历史上的测试证据，不是内核证明，也不是一次新近重做的验证运行。

## 证据的边界

早期的审查记录了 8000 次随机的压缩器会话，带 sanitizer，并做往返比较。它变动了压缩级别、策略、内存级别、包装格式、小到一个输出字节的分块大小、冲刷模式、参数更改和复制。它报告说这些会话中没有不一致，也没有 sanitizer 诊断。字典设置、priming 和自定义 gzip 头不在那次运行之内。窗口为一个字节的存储块路径也被排除在外。

这些观察不证明安全性。对所有输入、每一种初始化历史和 overlay 容量的安全性，是[流压缩](../proof/deflate.md)一页上各序列定理的内容。有针对性的、可复现的证据应当和它的回归测试放在一起。验收规则在[检查](../checking/README.md)中。

## 历史上的 gzip 定位观察

早期的记录报告说：先读五个字节直到 EOF，然后相对于当前位置定位五个字节。seek 返回十，而 tell 仍然是五。它的解释是向前定位保留了 `past`；而一个更早的抽象关系要求的是目标位置和一个已清除的标志。这没有针对本修订版重新运行。对源码的这种解释仍然**尚未由证明确认**，这一观察也不建立操作层面的细化或新的发现。功能性的 gz 模型描述了同样的行为（[API 模型，各函数族的细节](../design/api-model-details.md)）；没有定理依赖这一观察。

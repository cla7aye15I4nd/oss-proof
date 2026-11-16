<!-- source-sha256: 689fbce98bbbbac1073921103a011f31ef11fdb9dee30c8e1ee53bbad9c5d7c0 -->
# inflate 证明骨架（历史）

本页保存[进度](../progress.zh.md)“核心证明骨架”一节中的 inflate 部分，内容是必需目标在 `bde170e9` 上通过验收之后的原文，除相对链接外未作改动。
这是历史记录：其中的状态（如 open、checked、“未完成”“已检查”）、工时、数字和日期反映各条目写作时的情况，不是当前状态。
当前状态和剩余工作只在[进度](../progress.zh.md)中。

#### inflate

inflate 系列的安全性（所有者 2026-11-11 的决定）：在每个可达历史上，无未定义行为、无内存错误、无泄漏，并且会终止。终止是每一行的一部分：每个定理都断言调用返回 `.ok`，这排除了 `Fault.outOfFuel`（`docs/spec/safety.md`）。“已检查”指定理在 `dev` 上且快速门禁为绿；“已验收”还需要验收套件。估计以专注工作的小时数计，不确定度约为数值的一半，包含共享构建主机上的构建时间。格式含义的 `meaning_*` 各行不在计划内，已不再列出；它们已证明的部分仍保留在 `dev` 上。

解码器不变量 `InflateInv`（`inflate.c.invariant`）：它把 `DefaultOriginState` 推广到 raw、zlib、gzip 与自动检测、windowBits 为 0，以及已附加的 gzip 头记录。`DecoderHeldBits`（在 `BAD`、`MEM` 与 `SYNC` 之外，至多持有 32 位）在每个可达历史上与它一起携带。

| 引理 | 含义 | 状态 | 小时 |
| --- | --- | --- | ---: |
| `inflate_public`（`public-inflate`） | 类型为 `Goal.inflate` 的定理：从每个可达流、每种配置（包括 gzip 头记录）出发的一次调用。首次在 `dev` 上无 sorry 是 `8b12ff6a`；快速门禁在 `2dab2f5e` 上为绿。 | checked | 0 |
| `inflate_reachable_invariant`（`inflate.c.reachable`） | 每个可达历史上的 `InflateInv` 与 `DecoderHeldBits`：初始化、重设缓冲区、每个流操作、`inflateCopy`。 | checked | 0 |
| `inflate_call_held`（`inflate.c.held-history`） | 一次 `inflate` 调用保持 `DecoderHeldBits`。这是安全性所需的功能事实：位缓冲区 `hold` 宽 32 位，所以解码器绝不能持有更多位。 | checked | 0 |
| `Goal.inflate` 的进展子句 | `rc = Z_OK → used ≠ 0 ∨ out ≠ []`。这是 `uncompress*` 循环的终止所需的功能事实；属于 `inflate_public`。 | checked | 0 |
| `inflate_call_safe`、`operation_safe`（`inflate.c.sequence-safety`） | 从可达历史出发的每个流操作只写流记录、它自己的块、头记录以及 `StreamWriteRegions` 中的调用者区域，并且恰好按它自己的账目改变活动块。`inflate` 经由 `InflateCall.safe`；`inflateSync` 经由 `inflateSync_call_safe`（包括重新同步时释放的窗口）；其余 12 个经由 `inflate.c.call-safety`。 | checked | 0 |
| `inflateEnd_invariant`（`inflate.c.call-safety`） | 对可达流调用 `inflateEnd` 返回 `Z_OK`，清除状态并释放流所拥有的每个块。 | checked | 0 |
| `inflate_sequence_safety_public`（`public-inflate-sequence-safety`） | 类型为 `Goal.inflate_sequence_safety` 的定理（= `StreamSequenceSafety .inflate`，即 `Goal.inflate_sequence` 的安全性一半）。 | checked | 0 |
| `inflateInit_`、`inflateInit2_`（`public-inflate-init`、`public-inflate-init2`） | 每个 windowBits 与每种分配结果，按源码中的错误顺序；无效宽度会释放其状态。`inflate_init2_public` 已证明；它还需要登记。 | checked | 0 |
| 各种重置、`inflateEnd`、`inflateGetDictionary`、`inflateSetDictionary`、`inflateGetHeader`、`inflatePrime`、`inflateSyncPoint`、`inflateMark`、`inflateCodesUsed`、`inflateUndermine`、`inflateValidate` | 生命周期与查询目标，包括空流与无效流。 | 已登记 | 0 |
| `inflateSync` | 每个可达历史上的安全性：`inflateSync_call_safe`，属于序列定理。`Goal.inflateSync` 的其余部分是精确的标记搜索（`Api.syncSearch`），这是任何安全证明都不需要的功能子句。 | checked (safety) | 0 |
| `inflate_copy_public`（`public-inflate-copy`、`inflate.c.copy-public`） | 类型为 `Goal.inflateCopy` 的定理：空参数被拒绝；从每个可达源出发，两种分配失败都释放已分配的内容并清除 `dest->state`，成功则给出重定位后的状态、窗口前缀，以及账目中恰好新增的块。由 `inflate.c.copy-*` 的六个执行引理组合而成。 | checked | 0 |
| 验收批次 | `inflate_public`、`inflate_init2_public`、`inflate_sequence_safety_public` 与 `inflate_copy_public` 已登记在 `tests/audit/theorems.txt`，`Goal.inflate_sequence_safety` 已登记在 `tests/audit/goals.txt`；`tests/proof-mutants/public-streams.tsv` 中有针对 `inflate`、`inflateCopy` 与 `inflateInit2_` 的九个函数体证明变异，每个都经本地运行在其所列模块中被杀死。验收套件尚未在某个指名的提交上运行。 | prepared | 0 |
| 清理 | 删除没有任何已登记定理使用的快速路径与固定配置证明。 | open | 4 |
| `uncompress*`（`public-uncompress*`） | 功能目标：四个都在 `dev` 上由 `DecoderFacts` 组合得到（`uncompress2_z_of_facts`、`uncompress2_of_facts`、`uncompress_z_of_facts`、`uncompress_of_facts`）。不计划：`DecoderFacts` 的格式事实不在范围内（只证安全）。 | 不在计划内 | 0 |
| `uncompress*_safe`（batch 3） | `Goal.uncompress2_z_safe`、`uncompress2_safe`、`uncompress_z_safe`、`uncompress_safe`（`Spec/Public/Utilities`）：无未定义行为，会终止，只写输出缓冲区（不超过容量）与长度单元，每条返回路径都释放全部分配，返回文档规定的返回码，只在分配失败后返回 `Z_MEM_ERROR`。已在 `public-uncompress-safe` 中无前提证明（`uncompress2_z_safe`、`uncompress2_safe`、`uncompress_z_safe`、`uncompress_safe`）：每次 `inflate` 调用用 `inflate_public`，每个可达流都有解码器（`reachable_invariant_kind`）；不用格式事实，也不用功能事实。功能证明共用这段运行（`SafeState`、`SafeFinal`），另加它的格式事实（`NoOver`）。终止：循环的度量（未读源字节加未填空间）低于循环燃料，并在每次 `Z_OK` 调用后下降，依据 `Goal.inflate` 的进展子句（`rc = Z_OK → used ≠ 0 ∨ out ≠ []`），这是安全事实。陈述测试 `tests/goals/uncompress-safety`（ASan、UBSan、泄漏计数、分配失败；9000 次运行无子句被违反）。验收批次：四个定理和目标已登记（`tests/audit/theorems.txt`、`goals.txt`）；`uncompress2_z` 的四个翻译变异（`tests/proof-mutants/api-boundary.tsv`：去掉 `inflateEnd`、`destLen` 计数错误、补充量差一、初始化出错路径泄漏）都在 `public-uncompress-safe` 中被杀死，位置是运行与安全事实相遇之处。证明不再复述程序（删除了 `program`、`program_eq`）：它运行翻译本身，循环体由 `BodyOK` 描述，补充量写成最小值。 | checked | 0 |
| **剩余合计** | | | **4** |

批次 3 的陈述更正与公开目标的定义域。每一项只改变 `DecoderFacts` 的内部事实；没有公开目标（`Goal.inflate_completes`/`InflateCompletes`、四个 `uncompress*` 目标、格式目标）失去其定义域的任何部分，因此不需要 `docs/deviations.md` 条目。
- `d23ce2d5` `NeedDictionaryCall` 增加 `log.singleDictionary = true` 与 `ByteObjectsFit h`；`InflateCompletes` 与 uncompress 循环已经假设二者。
- `61995719` `TraceEvidence` 排除配置窗口大于头部窗口的 zlib 字典。其唯一用途 uncompress 循环不使用字典。被排除的情形是 C 解码了 RFC 1950（`Zlib.Decodes`）不允许的流，但这不是新发现：它是 zlib 在未定义 `INFLATE_STRICT` 时的默认行为，已由 `Api.Layer.InflateAccepted` 建模，并记录于 `tests/regression/inflate-configured-window`。
- `0c56ca53` `ConsumesWithinStream` 第二个子句要求流有尾部，或有输出空间且 flush 不是 `Z_BLOCK`/`Z_TREES`。`InflateCompletes` 提供空间与这样的 flush；uncompress 解码 zlib。被排除的情形（原始数据、无空间）是 C 的正确行为，不是发现。
- `ConsumesWithinStream` 第二个子句的结论由 `Z_STREAM_END ∨ Z_MEM_ERROR` 改为 `rc ≠ Z_OK ∧ rc ≠ Z_BUF_ERROR`：流结束后被拒绝的调用（`next_out` 为 NULL）在整个流已被消费时返回 `Z_STREAM_ERROR`。所有用途只排除 `Z_OK` 与 `Z_BUF_ERROR`。这是 C 的正确行为，不是发现。
- `a974ea43` `ConsumesWithinStream` 与 `StopsWhenBlocked` 增加 `ByteObjectsFit h`；协议历史在每次调用前都记录它。
- `ParseMeaning` 的请求子句由等价改为从令牌到 `havedict = 0` 的 `needDict` 阶段的蕴含：返回 `Z_NEED_DICT` 之后，一次 `next_out` 为 NULL 的调用被拒绝并返回 `Z_STREAM_ERROR`，令牌变为假而解码器仍在等待（`tests/verification/regressions/inflate-refused-dictionary-request.lean`）。所有使用处都只用蕴含方向。属内部修正；是正确的 C 行为，不是发现。

对象大小上限：`StreamReachable` 在每次 inflate 调用之前和每次调用者编辑之后假设 LP64 的 `PTRDIFF_MAX` 上限，`StreamSequenceSafety` 在每次调用之前假设该上限（`408c1f04`）。

##### inflate 第 1 批：格式含义的解码侧

一次调用内 deflate 流的块体：块头、固定表与动态表的安装、码长表、慢速符号解码、存储块复制、整个
`inflate_fast` 调用、从输出与窗口的匹配复制，以及 `inf_leave` 处的窗口更新。文件为
`inflate.c.meaning-<topic>`。每个引理覆盖 8 到 15 的所有窗口宽度和所有封装，不固定配置。陈述测试：
`tests/goals/inflate-meaning-body`（真实解码器在块体模式下的状态字段与解析位置对照：按下述修正后，
3,200 个会话约 56,000 个状态无子句被违反）。

与 inflate 负责人商定的接口修正（2026-11-10）。每一项都使 `meaning_step` 为假或无法证明；证据来自真实解码器或反例状态。

- P1（`0696a247`）：zlib 对某些动态块头只在读完整一部分后才拒绝，因此 `dynamicBits` 去掉可补全前提（`tests/goals/inflate-meaning/late-rejection.c`：三个单次调用会话以 `Z_OK` 停在 `LENLENS` 或 `CODELENS`）。
- P2（`0696a247`）：动态块头的 `BodyMatches` 增加 `DynamicMatches`（计数、码长码及其表、已读码长）。
- P3（`0696a247`）：没有窗口时 `WindowMeaning` 要求历史为空。
- P4（`0696a247`）：增加 `storedPad`，因为 `STORED` 在等待 `LEN` 之前先丢弃填充位；真实解码器：raw -15，块头结束于第 32805 位时，一次调用停在 `STORED` 且已消费 32808 位（回归测试 `tests/verification/regressions/inflate-stored-pad.lean`）。
- P5（`0696a247`）：`TableMeaning` 包含 `StableQuery`，在保留位少于 15 时拒绝无效码需要它。
- P6（`d9fa89d1`）：存储块不保留位，因此 `COPY` 跟随输入。
- P7（`69b25ebe`）：每个等待位置都限定保留位数，使块边界处少于 8 位成为归纳性质；真实解码器：1,800 个会话约 32,000 个块体状态中数值上界无违反。
- P8（`03c98f14`）：块体阶段中 `out - left` 等于本次调用的输出，`MATCH` 依赖于此。
- P9（`03c98f14`）：`partialCopy` 携带记号的距离（`0 < dist ≤ |dict ++ out|`，`dist ≤ 32768`）。
- P11：`BodyMatches` 在 `.storedHeader` 处保留少于 32 位。`STORED` 的补码检查会读到 32 位以上的位，没有这个上界 `stored_step` 为假：raw -15，输入 `01 01 00 FE FF 01`（一个合法的单字节最终存储块）全部读入，`STORED` 中保留 45 位，检查进入 `BAD`。zlib 在 `TYPEDO` 之后保留少于 8 位，在 `STORED` 中等待之后少于 32 位。
- P12（`123722bb`）：`PendingParsed` 在 `.copy` 处接受一个尚未写出任何字节、没有历史界的完整匹配。`MATCH` 在检查距离之前就因没有输出空间而离开，因此过远的距离可以停在那里，而调用返回 `Z_OK`；真实解码器：raw -15，输入 `03 02`、没有输出空间时停在 `MATCH`，返回 `Z_OK`，offset 为 1，窗口为空，下一次调用报告 `invalid distance too far back`（`tests/goals/inflate-meaning-body/far-match.c`，回归测试 `tests/verification/regressions/inflate-unchecked-match.lean`）。
- P13（`f88873e0`）：`.none` 与 `.distance` 处的保留位上界只排除去掉最后一个字节后的保留位中的有效符号（不超过 285、不超过 29）。`TableMeaning` 没有说明保留符号的表项消耗多少位（`fixedDistLens` 中的 30 和 31，`fixedLitLens` 中的 286 和 287），因此在因缺少输入而离开的查找处，对任意符号的上界无法证明；保留符号会导向 `BAD`。
- P14：`DynamicMatches` 的 `CODELENS` 子句另含 `Trace` 的逆向：从零个码长开始对头部位的每个解析都经过已存的码长。仅有 `Trace` 不能确定头部各项在何处结束，因此 `codelens_step` 在重复错误处为假。反例状态：`HLIT = 0`、`HDIST = 3`（261 个码长）；码长码使符号 2、16、17、18 长度为 2（`00`、`01`、`10`、`11`）；`A = [2,2,2] ++ 0^253 ++ [2]` 由各项 `R` 读出；头部位为 `R ++ 01`（16 的编码，其附加位未读）；已存码长 `A ++ [2,2]`。`Trace` 成立（唯一补全是两个字面量 2，而 `R ++ 01 00 00` 也给出 `A ++ 2^4`）。源 `R ++ 01 10 ...` 有效（16 带附加值 1 给出 `A ++ 2^4`，字面量/长度码完整且含块结束，距离码完整），但解码器把 `10` 读作 17 并进入 `BAD`。
- P15：`TableMeaning` 另含 `PrefixQuery`（适配的查询从其补零后的已消耗位选出同一表项）与 `QueryCompatible`（快速叶标志）。在 `BAD` 处，`inflate_fast` 只丢弃被拒记号的位，然后退还未用的整字节，因此已读输入可能止于查表看过的位之内；`Inv` 与 `StableQuery` 不确定被拒表项需要多少位。反例：一个固定块，其字面量/长度表对 286 和 287 的编码读到 `{op 64, bits 6}`，仍满足 `Inv`、`StableQuery` 与 `QueryCompatible`，快速调用读到 `110001` 为止，而 284 的编码（`11000100`）可有效地接续它。作为一张更小的、经内核检查的表保留：它满足 `Inv` 与 `StableQuery` 但不满足 `PrefixQuery`（`tests/verification/regressions/inflate-prefix-query.lean`）。构造函数建立该性质（`constructor_establishes_prefix_query`，后续构造保持它：`prefix_query_of_prefix`），固定表也满足（`lenfix_prefix`、`distfix_prefix`）。
- 共用块（目标变更）。快速解码器的 `Env` 曾要求输入与输出位于不同的块（`hsep : ib ≠ ob`）。这过窄：输入与输出可以是同一块中互不重叠的范围，这是有定义的 C（[复现](../../tests/regression/inflate-shared-block/README.md)）。`Env.hsep` 现为 `ib ≠ ob ∨ (ib = ob ∧ 输入范围 [i0, i0 + avail_in) 与输出范围 [o0, o0 + avail_out) 不相交)`。窗口块仍不同于输出块。循环中输出数组 `A` 任意的片段现在还假设 `Env.InputFrame A i`：块共用时，`A` 从游标 `i` 到输入末尾保留原输入。类型改变的已登记目标：所有基于 `Env` 的目标都容许共用块（`step_safe`、`fast_safe`、`actual_body_preserves_origin`、`actual_body_refines_token`、`actual_fast_preserves_origin`、`actual_distance_block_preserves_origin`、`actual_distance_refines_lz77`、`distance_lookup_matches_format`、`length_lookup_matches_format`、`actual_body_retains_selected_length`、`actual_copy_match_refines_lz77` 以及各 `Origin` 目标）。`StepPre`（因而 `step_safe`、各 `actual_body_*` 目标与 `actual_body_retains_selected_length`）新增字段 `inputFrame`；`actual_pull_preserves_origin`、`actual_rollback_preserves_origin`、`actual_distance_block_preserves_origin` 与 `actual_distance_refines_lz77` 新增前提 `InputFrame`。块不同时新前提空真，因此每个新类型都蕴含旧类型。整次调用的目标 `fast_safe` 与 `actual_fast_preserves_origin` 不带新前提：循环由分离性消去 `InputFrame`，因为解码器只在输出范围内写入（`Env.inputFrame_of_frame`、`Env.InputFrame.write`）。

块体模式的子句由 `tests/goals/inflate-meaning-body` 在真实解码器上检查（3,200 个会话约 56,000 个状态，无违反）。

| 引理 | 含义 | 状态 | 小时 |
| --- | --- | --- | ---: |
| `meaning_interface_body` | P1 到 P4、`DynamicMatches` 以及 `TableMeaning` 中的后缀稳定性（`inflate.c.meaning`，`0696a247`）。 | checked | 0 |
| `LoopMatches`（`meaning-loop`、`meaning-write`、`meaning-frame`） | 一次调用内模式步之间的关系：寄存器、本次调用已消费输入、保留位、阶段、调用基点以来的输出、调用前输出的窗口与校验值。与第 2 批共用。已与第 2 批商定；含输出写入与框架引理。 | checked | 0 |
| `lenfix_inv`、`distfix_inv`、`lenfix_stable`、`distfix_stable`（`meaning-fixed-tables`） | 静态固定表满足 `DecodeTableInvariant.Inv`，码长为固定码长，包括短查询，查询对后续输入稳定、只读其已消耗的位（`lenfix_prefix`、`distfix_prefix`），且叶标志相容。 | checked | 0 |
| `lookup_meaning`（`meaning-lookup`、`meaning-length`、`meaning-distance`） | 带补充输入的慢速 `lookup1`/`lookup2` 作用于满足 `Inv` 的表：选中的叶子是保留位的符号（可用位少于 15 也成立），或输入没有有效符号。已并入各步引理（`fitted_leaf_meaning`、`lookupLoop_fail`、`lookup1_len_fail`、`lookup2_len_fail`）。 | checked | 0 |
| `codes_lookup_meaning`（`meaning-codelens-items`） | 码长表（`CodeLengthMeaning`）的同一性质，包括空码长码（`cl_iter`）。 | checked | 0 |
| `table_step`（`meaning-dynamic-steps`） | `TABLE`：等待、计数拒绝（`BAD`，无有效续写），或以 `LoopMatches` 进入 `LENLENS`。除流记录外无其他假设。 | checked | 0 |
| `lenlens_step`（`meaning-dynamic-steps`） | `LENLENS`：跨调用读取码长码的码长；拒绝且无法补全，或带 `CodeLengthMeaning`、空码的表项和少于 8 个保留位进入 `CODELENS`。除流记录外的假设：`WellFormed`（数组大小）。 | checked | 0 |
| `codelens_step`（`meaning-dynamic-steps`、`meaning-codelens-items`、`meaning-dynamic-tables`） | `CODELENS`：跨调用读取码长；重复（经解析的逆向得出 `BAD`）；块结束与编码检查（`BAD`：不存在 `DynamicHeader` 补全）；以 `Inv`、`StableQuery`、`PrefixQuery` 与 `QueryCompatible` 安装两张表；因 `Z_TREES` 离开或落入 `LEN_`。除流记录外的假设：`WellFormed`、`CodeLengthInvariant`、已安装表的内容分类。 | checked | 0 |
| `typedo_step`、`type_step`（`meaning-block`） | 最后一块之前的 `TYPE`、`TYPEDO`：存储块、固定块（用 `lenfix_inv`）、动态块、类型 3（`BAD`，格式中没有类型 3 的块体）。静态表来自 `LibraryGlobals`。 | checked | 0 |
| `stored_step`（`meaning-block`、`meaning-copy`） | `STORED`、`COPY_`、`COPY`：填充位、长度检查与跨调用的字节复制。除 `LoopMatches`、流记录与窗口界之外没有其他前提；保留位上界来自 `BodyMatches`（P11）。 | checked | 0 |
| `len_slow_step`（`meaning-length`） | `LEN_`、慢速 `LEN`：字面量、块结束（保留位少于 8）、长度、无效码（`len_slow_step`、`len__step`，接入 `lenext_step`）。`match_step` 之外的前提：快速分支条件的否定与 `DataTablesSafe`。 | checked | 0 |
| `distance_steps`（`meaning-distance`） | `LENEXT`、`DIST`、`DISTEXT`：额外位、距离符号、无效距离（`lenext_step`、`dist_step`、`distext_step`，接入 `match_step`）。`match_step` 之外的前提：`DataTablesSafe` 与 back 计数器上界（`DataPendingInvariant`）。 | checked | 0 |
| `lit_step`（`meaning-lit`） | `LIT`：写出待写字面量。 | checked | 0 |
| `match_step`（`meaning-match`） | `MATCH`：从输出和窗口复制、重叠、距离过远。 | checked | 0 |
| `fast_call_meaning`（`meaning-fast-token`、`meaning-fast-loop`、`meaning-fast`、`inffast.c.body-token-reject`） | 从 `LEN` 进入的整个 `inflate_fast` 调用，标准步骤形状：块内更多记号或块结束给出 `LoopMatches`；被拒记号给出 `BAD` 与 `LoopDoomed`（P15：记号在其自身的位上被拒，`actual_body_rejects_prefix`；对已存窗口过远的距离，在完整窗口下对整个历史也过远，`Token.Rejected.rebase`）。输入与输出可以是 `DispatchBuffers` 容许的任何调用方字节视图，也包括同一块中互不重叠的范围（`inflate_fast_entry`，见上面的共用块目标变更）。窗口块不同于输出块由调用方输出范围得出（`callerRange_slow_output`），而非前提。`match_step` 之外的假设：`Good`、`DataTablesSafe`、`DataPendingInvariant`、`DispatchBuffers`、`ByteObjectsFit`。 | checked | 0 |
| `leave_window_meaning`（`meaning-leave-window`） | `inf_leave` 处的 `updatewindow` 给出调用后输出的 `WindowMeaning`，包括首次分配窗口；分配失败时状态不变，旧的 `WindowMeaning` 保持。假设：`Good`、默认分配器、输出字节、输出缓冲区不是窗口块。 | checked | 0 |
| 清理 | 已删除 33 个 `inflate.c.fast*` 模块：没有已登记定理、公开目标、含义模块或其他模块导入它们（早期的语义切片及建于其上的视图框架）。其余 `inflate.c.fast*` 模块由含义证明的快速路径导入。 | 已检查 | 0 |
| **第 1 批剩余** | | | **0** |

供第 3 批使用：ConsumesWithinStream 的界。

| 名称 | 含义 | 状态 | 小时 |
| --- | --- | --- | --- |
| `HeldWithin`（`heldWithin`，`meaning-held-within`） | 处于语法阶段的解码器状态，不持有超出与其位可比较的有效流末尾的位；没有阶段位于完整流之后。即第 3 批的陈述加一个前提 `(consumed ++ held).length % 8 = 0`，在使用处成立。没有其他前提。 | checked | 0 |
| 批次 1 步骤引理中的 `LeaveShort`、`LoopRefuted`（`meaning-leave-short`） | 主体步骤每次因缺少输入（`have = 0`）离开时，所持有的位不足以构成其模式等待的字段（`LeaveShort`：少于 `NEEDBITS` 的位数，`COPY` 仍有剩余字节，在已安装表的任一含义下都没有完整的有效符号或码长项）。每次拒绝（`BAD`）时，已读输入不与任何满窗口有效流可比较（`LoopRefuted`，强于 `LoopDoomed`：有效流也不在已读位之内结束）。步骤：`TYPE`/`TYPEDO`、`STORED`、`COPY_`/`COPY`、`TABLE`、`LENLENS`、`CODELENS`、`LEN_`/`LEN`、`LENEXT`、`DIST`、`DISTEXT`、`MATCH`、`inflate_fast`。两者都先在真实解码器上检验（`tests/goals/inflate-meaning-body`：约 75,000 次缺输入离开，约 490 次损坏源上的数据错误，无违反）。`LoopBad`（批次 2）仍带 `LoopDoomed`（`LoopRefuted.doomed`）。 | checked | 0 |
| `StopShort` | 恰好消耗整个有效流的调用不返回 `Z_OK` 或 `Z_BUF_ERROR`（raw：除非输出空间不足，或 flush 为 `Z_BLOCK`/`Z_TREES`）。单次调用部分已检查：缺少字段（`LeaveShort`）的循环趟次没有读完整个有效流（`LoopMatches.starved_not_end`，`meaning-stop-short`）。剩余：整次调用的组合（`loop_meaning`，批次 3），以及因空间不足或 `Z_BLOCK`/`Z_TREES` 的停止（`BlockedLeave`、`wrapParsed_due`）。 | 不在计划内 | — |
| `FailWithin` | 停在 `BAD` 或 `MEM` 的调用，没有读过此前输入所开始的有效流的末尾。单次调用部分已检查：拒绝排除每个可比较的有效流（`LoopRefuted.not_comparable`，`meaning-stop-short`）；每个循环趟次中已读输入都是每个可比较有效流的开头（`LoopMatches.within`，`meaning-held-within`，用于 `MEM` 离开）。剩余：整次调用的组合（`loop_meaning`，批次 3）。 | 不在计划内 | — |

##### inflate，第 2 批：格式含义的流侧

包装头、字典请求与安装、尾部、结束、把模式步组装成一次调用以及把调用组装成历史，以及 `meaning_init`、`meaning_rebuffer`、`meaning_dictionary`、`meaning_accepted`、`meaning_prefix`。文件为 `inflate.c.meaning-<topic>` 与 `ZlibF/Math/inflate-meaning-*`。每个引理覆盖 raw、zlib、gzip 与自动检测，以及每个被接受的 windowBits（含 0）。协议轨迹中不会挂接头记录（`inflateGetHeader` 不是轨迹步骤），所以不会发生头捕获；头模式在 `head = NULL` 下证明。陈述测试：`tests/goals/inflate-meaning`（真实解码器的状态字段对照解析位置；6000 个会话中没有事实被违反）。

接口修正已与 inflate 负责人商定并在 `dev` 上（`bd0831d3`）：头阶段接纳首次调用前的 raw 数据；`ConfigMatches` 把解码器配置与轨迹联系起来；`needDict` 接纳任意 `DICTID`；块边界处持有少于 8 位（由第 1 批证明）；`MEM` 状态保留 `meaning_accepted` 与 `meaning_prefix` 的结论；`WrapMatches` 记录流侧的阶段字段（`inflate.c.meaning-stream`）。

| 引理 | 含义 | 状态 | 小时 |
| --- | --- | --- | ---: |
| `ConfigMatches`、`WrapMatches` | 配置字段，以及头、`needDict`、尾部与结束阶段的逐阶段字段（`bd0831d3`）。 | defined | 0 |
| `LoopMatches` | 第 1 批的行；第 2 批提供了草案并基于它组装。 | checked | 0 |
| `wrap_header_grammar`（`Math/inflate-meaning-wrap`、`meaning-wrap-steps`） | zlib 与 gzip 头的字节步保持可补全的头前缀；解码器等待处不是完整的头；补全到主体或 `needDict`；`HEAD`、`FLAGS`、`HCRC` 的每种拒绝都没有补全。 | checked | 0 |
| `wrap_trailer_grammar`（`meaning-wrap-steps`、`meaning-accept`） | 主体结束到尾部再到完成；尾部不匹配没有补全。 | checked | 0 |
| `meaning_init`（`inflate.c.meaning-init`） | 每个被接受的 windowBits 下 `inflateInit2_` 给出无输入的头阶段。 | checked | 0 |
| `meaning_rebuffer`（`meaning-rebuffer`） | 调用方换缓冲区保持状态、窗口与表；每个阶段的帧引理。 | checked | 0 |
| `head_step` | `HEAD`：raw 进入 `TYPEDO`，zlib 头（宽度 0 时由头设定宽度），gzip 魔数，每种拒绝。 | 不在计划内 | — |
| `dictid_step`、`dict_step`（`meaning-dictid`） | `DICTID` 保存标识并请求字典（`dictid_step`，已检查；`NeedDictExit`）；`DICT` 再次请求或进入主体（未完成；需要 P16，即 `needDict` 条款中的 `last = total = 0`，已向第 1 批提出）。 | 不在计划内 | — |
| `gzip_fixed_steps` | `FLAGS`、`TIME`、`OS`、`EXLEN`，含头 CRC 累加器。 | 不在计划内 | — |
| `gzip_field_steps` | `EXTRA`、`NAME`、`COMMENT`：跨调用的字节序列，对输入字节做 CRC。 | 不在计划内 | — |
| `hcrc_step` | `HCRC`：头 CRC 检查并进入主体。 | 不在计划内 | — |
| 共用循环引理（`meaning-bits`、`meaning-stuck`、`meaning-outcome`、`meaning-fields`） | `LoopMatches.needbits`；`LoopDoomed.of_stuck`；`LoopBad`、`TripOutcome`、`bad_trip`；持有位作为小端字节。 | checked | 0 |
| `trailer_steps`（`meaning-trailer`、`meaning-check`） | `DONE` 与 gzip `LENGTH`（已检查）；zlib 与 gzip 的 `CHECK` 用本次调用输出更新 Adler-32 或 CRC-32，随后进入长度字段或结束（`check_step`，已检查）；raw `CHECK` 需要 P10（raw 数据在 `CHECK` 时处于结束阶段，已向第 1 批提议）。 | 不在计划内 | — |
| `leave_meaning`（第 3 批，`meaning-leave`） | `inf_leave`：用本次调用输出更新计数与校验值；窗口更新用第 1 批的引理；`Z_MEM_ERROR`。带 `LoopMatches` 的循环出口由 `leave_meaning` 给出（`LeaveMeaning`），`BAD` 出口由 `leave_meaning_bad` 给出（`LeaveBad`），二者基于 `inflate_leave_values` 与 `checkMeaning_leave`。 | checked | 0 |
| `loop_meaning`（第 3 批，`meaning-run`） | 一次调用的模式循环以 `LoopMatches` 进入，以 `LoopExit` 结束：带 `LoopMatches` 的离开、`Z_STREAM_END`、带 `LoopBad` 的 `Z_DATA_ERROR`，或字典请求。前提：`TripMeaning`（第 1、2 批逐模式的步）与 `SideKept`（各步所需的安全事实，每一趟都保持）。 | checked | 0 |
| `meaning_step` 组装（第 3 批） | 入口、拒绝、运行与离开给出调用后的 `ParseMeaning`，含请求令牌。 | 不在计划内 | — |
| `meaning_dictionary`（`meaning-dictionary`） | `inflateSetDictionary`：拒绝、标识不匹配、`Z_MEM_ERROR`、raw 安装、zlib 在 `DICT` 中安装。 | checked | 0 |
| `deflate_prefix_order`（`meaning-prefix-order`、`meaning-accept`） | 有效流前缀上的解析位置位于它的解析上（输出前缀、精确结束），完成的解析就是规格解析，配置的 zlib 窗口与头声明的窗口解码相同，阶段的头就是流的头。 | checked | 0 |
| `meaning_accepted`（`meaning-format`） | 完成的单字典阶段消费的是被接受的流。 | checked | 0 |
| `meaning_prefix`（`meaning-format`） | 前缀、无数据错误、精确结束，`Z_MEM_ERROR` 之后亦然。 | checked | 0 |
| 清理 | 推广或删除默认配置下的头、字典与包装模块。 | 不在计划内 | — |
| **第 2 批剩余** | | | **0** |

第 2 批，为 `inflate_call_gzip` 准备的 gzip 头模式。已在 `dev` 上检查：`inflate_dispatch_gzip_header_rank`（`inflate.c.gzip-header-dispatch`），与 inflate 负责人的接口陈述完全一致。从 `FLAGS` .. `HCRC` 出发的一次分派，对任意允许 gzip 的包装、有无挂接的头记录，都无故障地运行，并保持表示不变式、调用方数据包、头记录与足迹。有两个前提比 zlib.h 更窄（`docs/deviations.md`）：头记录的 `extra` 缓冲区与未读输入分离；在 `EXTRA` 中头记录的 `extra_len` 不小于剩余长度。两者都来自 EXTRA 的 `zmemcpy` 在真实 C 上的未定义行为（`tests/regression/inflate-gzip-extra`）。`Goal.inflate` 是否把它们作为调用方定义域条款保留，由负责人决定。name 与 comment 缓冲区可以与输入重叠。

骨架条款`flags 字保持不变或是 16 位字`（skeleton/inflate 5d6f00e8）按原陈述为假：解码器在 `FLAGS` 中等待时，`inflatePrime` 可以在位缓冲区中留下 32 位，真实 C 随后写入 `flags = 65544`（`tests/regression/inflate-gzip-flags-prime`）。已证明的形式加上了入口位缓冲区的条件。`InflatePhase.flags` 对所有历史作出同样的 16 位断言；如何更正由负责人决定。

| 引理 | 含义 | 状态 | 小时 |
| --- | --- | --- | ---: |
| `HeaderFoot`（`inflate.c.gzip-header-frame`） | 相对入口堆的逐点足迹；给出 `BufferFrame` 与 `LiveChange`。 | checked | 0 |
| `GzInv`（`inflate.c.gzip-header-state`） | 步骤不变式：状态、流与头记录写入，`hbuf` 与区域存储，`NEEDBITS`，输入消耗。 | checked | 0 |
| `gz_FLAGS` .. `gz_HCRC`（`inflate.c.gzip-header-modes`） | 每个模式运行到头模式中的离开、`TYPE` 或 `BAD`；`NAME`/`COMMENT` 字节循环；`CRC2`、`CRC4`；`EXTRA` 的复制。 | checked | 0 |
| `inflate_dispatch_gzip_header_rank`（`inflate.c.gzip-header-dispatch`） | 接口定理。 | checked | 0 |
| `inflate_dispatch_gzip_header_flags_leave_word`（`inflate.c.gzip-header-dispatch`） | 离开时没有剩余输入；flags 字保持不变，或在入口位缓冲区为 0、8 或 16 位时是 16 位字。 | checked | 0 |
| **gzip 头模式** | | | **0** |

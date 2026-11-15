<!-- source-sha256: ad8f6416359e12a8542617a737e11eba5c035e5afc40f69d267593281ed8811e -->
# 回调解码器证明骨架（历史）

本页保存[进度](../progress.zh.md)“公开 API 的证明准备情况”一节中的 inflateBack 部分，内容是必需目标在 `bde170e9` 上通过验收之后的原文，除相对链接外未作改动。
这是历史记录：其中的状态（如 open、checked、“未完成”“已检查”）、工时、数字和日期反映各条目写作时的情况，不是当前状态。
当前状态和剩余工作只在[进度](../progress.zh.md)中。

#### inflateBack

回调解码器的安全（所有者 2026-11-12 的要求）：`Goal.inflate_back_sequence_safety`（`ZlibF/Spec/Public/Sequences.lean`），与未改动的 `Goal.inflate_back_sequence` 并列陈述。回调就是目标中的 `CallbackProtocol`：任意会返回的调用者代码，只修改自己的块和必须保持的窗口切片，交出位于窗口之外的可读输入，并提供有限的总输入（`inputBound`）。目标另加 `inputBound < 2^48`（循环额度；`docs/deviations.md`）。陈述测试：`tests/goals/infback-callbacks`（ASan/UBSan，30000 个用例，无报告）。骨架：分支 `skeleton/inflate-back`，`ZlibF/Proof/infback.c.safety-skeleton.lean`（类型检查通过；引理证明待完成）。早先的内部约定 `CbContract` 比协议窄，因此回调引理在 `PInv` 上重新陈述，其位代数可复用。
问题（不在计划内的功能目标）：`Goal.inflateBack` 对 `inputBound` 没有上限，因此输入超过循环额度的协议在模型中使它为假。
所需不变量：`inflate_fast` 假定入口处 `state->bits < 8`。`inflate.c` 在快速路径前检查它（上游 e7bb978）；`infback.c` 不检查，因此证明要说明每轮以 `TYPE`、`TABLE` 或 `LEN` 开始时持有的位少于 8（`BitsShort` 行）。若持有 8 位或更多，`inflate_fast` 可能把 `next` 退回到 `in` 给出的数据块之前。证据：`tests/goals/infback-callbacks/bits8.sh`（60000 个用例，未触发陷阱）。
目标修正（46ce3a0a、200f80e1）：历史为 `BackSafeReachable`。窗口是一个堆字节块的切片；在每次调用所在的堆上以及每个回调步骤之后，每个字节对象都小于 `2^63` 字节（`BackPlatform`）；每个输入块都位于一个堆字节块中（`BackFirstChunk`、`BackPlatform`）；两次调用之间的调用者修改保持存活块的只读标志。偏差行："回调解码器窗口"、"回调解码器输入块"、平台行与"回调"。候选推广（现在不做）：让两个解码器 `inflate` 与 `inflateBack` 一起接受位于任意字节引用的输入块（调用者结构体字段、静态数据）；两者都依赖 `inflate_fast`，其入口要求原始字节块。
组合：`inflate_back_sequence_safety`（c7169b54）用 `lenFast_of_blk`（窗口位于堆字节块时的快速路径）组合下列引理，没有未证前提；每个历史的窗口都在这样的块中（`back_reach_window`）。较早的组合 `inflate_back_sequence_safety_of` 以前提 `FastOk`（每个窗口上的快速路径）为条件，已删除；`docs/proof/callbacks.md` 说明该前提为何没有证明。已登记，带证明变异（`tests/proof-mutants/infback-sequence.tsv`）。

| 引理 | 含义 | 状态 | 小时 |
| --- | --- | --- | ---: |
| `PInv` 框架 | 调用者协议上的循环不变量：`CallbackFrame` 与存活集合在回调调用和库写入之间可组合；状态或寄存器写入保持 `PInv` | 已检查（dd5f9e1e） | 0 |
| `PULL_p` | `PULL()`：只在当前块为空时调用 `in`；由协议的 `inStep` 得到数据块和日志项；返回 0 时为 `Z_BUF_ERROR` | 已检查（dd5f9e1e） | 0 |
| `PULLBYTE_p`、`NEEDBITS_p` | 向 `hold` 读入一个字节，以及 `k ≤ 32` 的 `NEEDBITS(k)`（`inflate.c.main.macros` 的位代数） | 已检查（52ae3999） | 0 |
| `ROOM_p` | `ROOM()`：对满窗口调用 `out`（`outStep`），`whave = wsize`，从窗口开头重新写；拒绝时为 `Z_BUF_ERROR` | 已检查（7971d171） | 0 |
| `TYPE_p` | `case TYPE`：最后块标志与块类型，最后一块之后进入 `DONE` | 已检查（472c8a15） | 0 |
| `STORED_p` | `case STORED`：长度检查以及经 `PULL` 和 `ROOM` 的复制；数据块可与窗口同属一个块 | 已检查（eec477cd） | 0 |
| `TABLE_p` | `case TABLE`：头部、码长码、解码出的码长、三次 `inflate_table` 调用，表已安装（`TablesOk`，含解码不变量与查询稳定性），以及转入 `LEN` | 已检查（650c8931） | 0 |
| `BitsShort` | 每轮以 `TYPE`、`TABLE`、`LEN` 开始时持有的位少于 8（`Round` 中的 `Short`）：带读入见证的查表、由 `StableQuery` 与 `PrefixQuery` 得到的 `consumed_gt`、依据 `CodeLengthContents` 的 `TABLE` 码长解码 | 已检查（57c7fabd、9e93b576） | 0 |
| `LEN_slow_p` | 不走快速路径的 `case LEN`：字面量、块结束、带距离检查并经 `ROOM` 复制的长度/距离对、无效码 | 已检查（06e4a17d） | 0 |
| `fast_env` | 在 `RESTORE` 之后由 `LEN` 处的 `PInv` 得到 `start = wsize` 的 `EnvG true`；窗口与自身的别名由 c51943af 覆盖（`EnvG true`、`inflate_fast_safe_progress`）。负责人：batch C | 已检查（c7169b54） | 0 |
| `fast_consumes` | 在长度表满足 `LenLeavesPositive` 的 `EnvG α` 上，`inflate_fast` 严格消耗位：除非结束于 `TYPE` 或 `BAD`，有 `bits' + 8·avail_in' < bits + 8·avail_in`（路线 (a) 的度量）。负责人：batch C | 已检查（02e8c222） | 0 |
| `LEN_fast_p` | 走快速路径的 `case LEN`：`RESTORE`、在 `fast_env` 上调用 `inflate_fast`、`LOAD`；之后的 `PInv`、度量（由 `fast_consumes`）与 `Short`。负责人：batch C | 已检查（c7169b54） | 0 |
| `dispatch_p` | 调度的一轮：`PInv` 可达的每种模式；度量下降，或调用以三种结果之一离开；在 `LEN_fast_p` 之前快速路径是前提 `LenFast` | 已检查（650c8931） | 0 |
| `loop_p` | 调度循环在额度内结束（由 `inputBound < 2^48` 得 `backMeasure < 2^64`） | 已检查（650c8931） | 0 |
| `back_call` | 一次调用：入口、`loop_p`、出口（把最后的部分窗口交给 `out`，写 `next_in`、`avail_in`）：`back_call_partial`（返回的调用，任意输入）与 `back_call_total`（输入少于 `2^48`） | 已检查（3a2a8753、f91f401d） | 0 |
| `back_null`、`back_end_blk` | 空流；可达历史上的 `inflateBackEnd`（`back_end_public`） | 已检查（6f9575e7、c7169b54） | 0 |
| `back_reach_valid_blk` | 每个可达历史都在调用者窗口上留下有效状态（初始化、换缓冲区、使用无度量循环规则的 `back_call_partial`） | 已检查（6f9575e7、c7169b54） | 0 |
| **合计** | | | **0** |

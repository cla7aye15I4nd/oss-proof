<!-- source-sha256: 90f5c875667f1e2c4d76985a61d4212f3d7407962e89314cb99c3877373e9293 -->
# gzip 文件接口证明骨架（历史）

本页保存[进度](../progress.zh.md)“核心证明骨架”一节中的 gz 部分，内容是必需目标在 `bde170e9` 上通过验收之后的原文，除相对链接外未作改动。
这是历史记录：其中的状态（如 open、checked、“未完成”“已检查”）、工时、数字和日期反映各条目写作时的情况，不是当前状态。
当前状态和剩余工作只在[进度](../progress.zh.md)中。

#### gz

gzip 文件接口的安全（第 5 项结论，所有者 2026-11-12 的决定）：在一个句柄的每条调用历史上，没有未定义行为、没有内存错误、不泄漏内存块或描述符，并且一定终止。目标 `Goal.gz_sequence_safety` 及其定义（`GzHistory`、`GzCloseSafe`、`GzOpenSafe`、`GzDopenSafe`）在 `dev` 的 `ZlibF/Spec/Public/GzSafety.lean` 中（`61fc2678`），建立在 `gz.inv-model` 的 `GzInv` 与 `GzCallSafe` 之上。组装已在 `dev` 上：`gz_sequence_safety_of`（`gz.sequence-safety`）的结论是 `Goal.gz_sequence_safety`，只有一个前提 `GzReadLeaves`：六个读取叶子 `gzread_step`、`gzfread_step`、`gzgetc_step`、`gzungetc_step`、`gzgets_step`、`gzdirect_step`，每个都取骨架中的原样陈述。六个都已在 `dev` 上无前提地检查，所以 `Goal.gz_sequence_safety` 已检查：`gz_sequence_safety_public`（`public-gz-sequence-safety`）。它已登记在 `tests/audit/theorems.txt` 中，带证明变异（`gz-sequence.tsv`、`gz-read.tsv`）；`Goal.gz_sequence_nonvacuity`（`gz_sequence_nonvacuity_public`）与 `Goal.gz_refusal`（`gz_refusal`）随之登记。审读 A1 把 `zlib.h` 的 `gzgetc()` 宏的内联路径加入了 `GzHistory`（`getcMacro`）和目标（一个合取项）；`GzMacro.gzgetc_macro_safe` 证明了它。目标更正（3c5292f7）：该步骤与合取项只覆盖 `x.have ≠ 0`，所以目标从不运行宏的 `have = 0` 分支（证明变异 `macro-have-guard-dropped` 存活）。现在两者覆盖每一次宏调用；`x.have = 0` 时宏即对 `gzgetc` 的调用，在 `ReadsFinite` 下返回（回归 `tests/verification/regressions/gz-macro-have-zero.lean`）。其余每个叶子都直接使用 `dev` 上的定理；没有使用循环规则。骨架在分支 `skeleton/gz` 的提交 `17770416` 上（合并 `dev` 之后），文件为 `gz.skeleton-model.lean`（只有两条循环规则）、`gz.skeleton-read.lean`（未完成的读取叶子）和 `gz.skeleton.lean`（把 `gz_sequence_safety_of` 应用于读取叶子）。它能通过类型检查：`Goal.gz_sequence_safety` 在其中由下列未完成引理证明。`dev` 以完全相同的陈述证明了的骨架叶子，从骨架中删除（或由 `dev` 定理关闭），并列为已检查。该目标涵盖每一种打开（`gzopen`、`gzopen64`、`gzdopen`）、`GzOperation` 的每个公开调用、每次关闭、句柄之外的调用者修改，以及两次调用之间文件系统世界的变化，对操作系统调用预言的每个取值都成立。

只要 `dev` 的定理与骨架陈述不同，读取叶子就是未完成的。“差异”一栏写出不同之处，以便读取侧对齐陈述（带证据地更正骨架陈述），或添加一个适配引理。

`GzInv` 相对于骨架文本的陈述更正。两者都削弱了一个子句，因为骨架原来的子句不成立；每项都有一个已检查的回归。目标的无故障子句和帧子句不变。
- `GzCommon.next` 只在有缓冲输出时（`x.have ≠ 0`）约束 `x.next`（`7c32d275`；回归 `tests/verification/regressions/gz-next-caller.c`，带补丁 0005）。
- `GzReadInv.copyDirect` 在 `how = COPY` 下允许 `direct = 0 ∨ direct = 1`（`a351cd66`；回归 `tests/verification/regressions/gz-copy-direct.c`）。

| 引理 | 含义 | 状态 | 小时 | 负责人 |
| --- | --- | --- | ---: | --- |
| `GzInv.caller`、`GzInv.gz_error`、`GzInv.gz_reset`、`GzInv.put_scalars` | `GzInv` 的接口引理。 | 已检查：`gz.inv-frame`、`gzlib.c.error-inv-premises`、`gz.inv-reset`、`gz.inv-put-scalars` | 0 | batch 1、deflate 负责人 |
| `gwhile_partial`、`gdoWhile_partial` | 部分正确性的循环规则（`gz.skeleton-model`）；目前没有证明使用它们。 | 未完成 | 2 | 未分配 |
| `gzopen_safe` | `gzopen` 返回；NULL 不留下任何东西；句柄满足 `GzInv`，且只有它的描述符是新的。 | 已检查：`gzopen_safe`（`gz.inv-open-fresh`，`5252a412`） | 0 | batch C |
| `gzopen64_safe` | `gzopen64` 即 `gzopen`。 | 已检查：`gzopen64_safe`（`gz.inv-open-fresh`，`5252a412`） | 0 | batch C |
| `gzdopen_safe` | 同 `gzopen_safe`，不打开也不关闭任何描述符。 | 已检查：`gzdopen_safe`（`gz.inv-open`，`8c2bba51`） | 0 | batch C |
| `gzclose_dispatch_inv` | `gzclose` 按模式即 `gzclose_r` 或 `gzclose_w`。 | 已检查：`gzclose_dispatch_inv`（`gz.inv-queries`） | 0 | batch 1 |
| `gzclose_step` | 由分派和两个关闭步骤得出 `gzclose`。 | 已检查：`gzclose_step`（`gz.inv-close`，`fdb8c613`） | 0 | batch C |
| `gzseek64_step`、`gzseek_step` | 在 `GzInv` 上定位是安全的。 | 已检查：`gzseek64_step`、`gzseek_step`（`gz.inv-seek`） | 0 | batch 1 |
| `gztell64_step`、`gztell_step`、`gzeof_step`、`gzbuffer_step` | 位置查询、eof 和缓冲区设置；以及 `post_unchanged`、`safe_of_unchanged`。 | 已检查：同名（`gz.inv-queries`） | 0 | batch 1 |
| `gzerror_step` | `gzerror` 把错误码存入调用者的单元。 | 已检查：`gzerror_step`（`gz.inv-frame`） | 0 | batch 1 |
| `gzerror_string` | 调用之后，`gzerror` 返回的指针是一个 C 字符串（审读 C1 加入的目标合取项）。 | 已检查：`gzerror_string`（`gz.inv-frame`） | 0 | batch C |
| `gzclearerr_step` | 经由 `gz_error` 的 `gzclearerr`。 | 已检查：`gzclearerr_step`（`gz.inv-clearerr`） | 0 | batch 1 |
| `gzoffset64_step`、`gzoffset_step` | 一次 `lseek`（M3）；其他都不变。 | 已检查：同名（`gz.inv-offset-rewind`，`646b1ab6`） | 0 | batch C |
| `gzrewind_step` | `lseek`（M3）与 `gz_reset`。 | 已检查：`gzrewind_step`（`gz.inv-offset-rewind`，`646b1ab6`） | 0 | batch C |
| `history_inv`、`operation_safe`、`close_safe`、`gz_sequence_safety` | 组装，在 `dev` 的 `GzInv` 与 `GzSafety` 下重新检查。 | 已检查：`gz_sequence_safety_of`（`gz.sequence-safety`），前提 `GzReadLeaves`，六个字段都已证明（`gz_read_leaves`）；`Goal.gz_sequence_safety` 已无前提地检查为 `gz_sequence_safety_public`（`public-gz-sequence-safety`）；已登记在 `theorems.txt` 中 | 0 | batch C |
| `gz_init_safe`、`gz_comp_safe`、`gz_zero_safe`、`gz_write_safe`、`gz_vacate_safe` | 写入侧的辅助函数。 | 已检查：同名（`gzwrite.c.safety`） | 0 | batch C |
| `gzwrite_step`、`gzfwrite_step`、`gzputc_step`、`gzputs_step`、`gzvprintf_step`、`gzprintf_step`、`gzflush_step`、`gzsetparams_step` | 写入侧的公开调用。 | 已检查：同名（`gzwrite.c.safety`） | 0 | batch C |
| `gzclose_w_step` | 收尾、`deflateEnd`、释放、交还描述符。 | 已检查：`gzclose_w_step`（`gzwrite.c.safety`，以 `GzCloseSafe` 陈述） | 0 | batch C |
| `deflate_quiet` | 没有输入的 `deflate` 会停下（`DeflateQuiet`）。`dev` 上的写入证明直接使用它；骨架中不再有对应叶子。 | 已检查：`Zlib.Deflate.Universal.Quiet.deflate_quiet_holds` | 0 | batch 3 |
| `gzclose_r_step` | `inflateEnd`、释放、交还描述符。 | 已检查：`GzRead.gzclose_r_step_safe`（`gz.read-close`），陈述完整写出；`GzRead.Close.Released` 按 `rfl` 即 `GzReleased` | 0 | 读取侧（deflate 负责人） |
| `gz_skip_have_safe` | skip 消耗缓冲的字节。 | 已检查：`gz_skip_have_safe`（`gzread.c.skip-have`） | 0 | 读取侧（deflate 负责人） |
| `gz_load_safe` | `read` 循环（M1）。差异：`GzRead.gz_load_safe`（`gz.read-load-error`）多出假设 `hm`（`mode = GZ_READ`）、`hsz`（`size ≠ 0`）、`hroot`（缓冲区是数据缓冲块或不属于句柄）和 `heofin`（`eof ≠ 0 → avail_in = 0`），结论更强。 | 未完成（对齐） | 1 | 读取侧（deflate 负责人） |
| `gz_avail_safe` | 重新填充 `in`。差异：`GzRead.gz_avail_safe`（`gz.read-avail`）多出假设 `hm`（`mode = GZ_READ`），结论更强。 | 未完成（对齐） | 0.5 | 读取侧（deflate 负责人） |
| `gz_look_safe` | 延迟分配的缓冲区、`inflateInit2`、COPY。差异：`GzRead.gz_look_safe : GzLookSpec` 取 `GzInvUpToOutput`（比 `GzInv` 弱）和前提 `how = LOOK` 与 `MsgLit s`；后置条件建立在 `GzInvOut` 而不是 `GzInv` 上。 | 未完成（对齐） | 2 | 读取侧（deflate 负责人） |
| `gz_decomp_safe` | inflate 步骤。差异：`gz_decomp_safe_of` 需要一个前提 `InflateStuckNoOutput`（从 `BAD` 或 `MEM` 的一次调用返回错误，不产生输出，也不消耗输入），已由 batch 3 证明（`inflateStuckNoOutput_holds`，`inflate.c.stuck-no-output`）；HEAD 事实已证明（`inflateHeadUsesInputR_holds`，`inflate.c.head-uses-input`）；`GzDecompSpec` 加上前提 `MsgLit s` 和 `out.length ≠ 0`，替换了分离前提（`out` 不属于句柄，或 `out = s.out`），并在 `ReadsFinite` 下终止，而不是无条件终止。 | 未完成（对齐，一个前提） | 3 | 读取侧（deflate 负责人） |
| `gz_fetch_safe` | 分派函数。差异：`gz_fetch_safe_of` 需要 `GzLookSpec` 和 `GzDecompSpec`；`GzFetchSafe` 取 `GzInvUpToOutput` 和前提 `err ≠ Z_STREAM_END`、`how = COPY → avail_in = 0`、`MsgLit s`；后置条件建立在 `GzInvOut` 上；在 `ReadsFinite` 下终止。其后置条件带有 `gz_read` 与 `gz_skip` 的燃料上界所需的进展条款（`fetchRank`：一次取数填满缓冲区，除非失败、输入结束、到达 `GZ_OFF_MAX`，或秩下降 2；严重错误保持；`Stuck` 的流不产生输出）。 | 未完成（对齐，被调用者前提） | 2 | 读取侧（deflate 负责人） |
| `gz_skip_safe` | skip 循环。差异：`gz_skip_safe_of` 需要 `GzFetchSpec`、`GzFetchProgress`（以及已证明的 `GzErrorSpec`、`GzErrorOwn`）；它取 `GzInvUpToSkip`（比 `GzInv` 弱）。 | 未完成（被调用者前提） | 1 | 读取侧（deflate 负责人） |
| `gz_read_safe` | 三条路径、调用者范围、`x.pos`（F-1）。已检查为 `gz_read_safe_of (skip : GzSkipRead) (fetch : GzFetchSafe) (decomp : GzDecompSpec) : GzReadSafe`（`gz.read-read`）。`GzReadSafe` 是骨架陈述加上前提 `err ≠ Z_STREAM_END`、`how = COPY → avail_in = 0` 和 `MsgLit s`（`GzReadInv` 的条款），这些在后置条件中保持。终止：度量 `min(len, GZ_OFF_MAX - pos)/8 + fetchRank + 阶段项` 在 `ReadsFinite` 下保持小于 `2^64`。`GzSkipRead` 即 `gzSkipRead_holds`（`gzread.c.skip-fetch`）。已无前提地关闭为 `gz_read_safe : GzReadSafe`（`gz.read-assembly`）。 | 已检查 | 0 | 读取侧（deflate 负责人） |
| `gzread_step`、`gzfread_step` | `gz_read` 的包装函数。已作为 `gzread_step_of_read`（`gz.read-gzread`）与 `gzfread_step_of_read`（`gzread.c.fread`）从 `GzReadSafe` 检查，并无前提地关闭为 `gzread_step` 和 `gzfread_step`（`gz.read-assembly`）：即骨架叶子。 | 已检查 | 0 | 读取侧（deflate 负责人） |
| `gzgetc_step`（`gzgetc__step` 由它得出） | 一个字节。 | 已检查：`GzRead.gzgetc_step`（`gz.read-getc-step`），无前提 | 0 | batch C |
| `gzungetc_step` | 在 `out` 内回退。 | 已检查：`GzRead.gzungetc_step`（`gz.read-getc-step`），无前提：`GzSkipTerminates` 即 `gzSkipTerminates_holds`（`gzread.c.skip-terminates`） | 0 | batch C |
| `gzgets_step` | 有界的 `memchr`、复制、NUL。 | 已检查：`GzRead.gzgets_step`（`gz.read-gets-step`），无前提 | 0 | batch C |
| `gzdirect_step` | 一次 `gz_look` 和 `gz_skip_have`。 | 已检查：`GzRead.gzdirect_step`（`gz.read-direct-step`），无前提 | 0 | batch C |
| `gzgetc_macro_safe` | 对 `zlib.h` 中 `gzgetc()` 宏（`Zlib.ZlibH.gzgetc`）的一次调用保持 `GzInv`：内联路径（`x.have ≠ 0`）无前提地返回，`x.have = 0` 时宏即函数，经由 `gzgetc_step`；即历史步骤 `GzHistory.getcMacro` 和审读 A1 加入的目标合取项，在 3c5292f7 中更正。 | 已检查：`GzMacro.gzgetc_macro_safe`（`zlib.h.gzgetc-macro`），用于 `history_inv` 与 `gz_sequence_safety_of` | 0 | batch C |
| 合并 `deflate.c.quiet-*` 中重新陈述的副本 | 清理，不在关键路径上。 | 未完成 | 4 | 以后 |
| **剩余总计** | batch C 0；读取侧 9.5（内部辅助陈述与骨架文本的对齐；目标已不再需要它们）；未分配 2；以后 4 | | **15.5** | |

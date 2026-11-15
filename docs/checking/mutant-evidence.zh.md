<!-- source-sha256: b901a7625a0489b29c9b73abc42cec55346f009247f147660d2f5ee7ed1a4bca -->

# 变异体证据记录

> **带日期的记录。**写于 2026-11-12 至 2026-11-14，即登记这里所说各目标的那几次运行之时。它说明各组目标的证据由哪些变异体行承担，这些行在哪里被杀死。时间、内存峰值和数目都是那几次运行的数据。一个目标需要哪些行，以各列表和 `tests/audit/public-mutants.json` 为准；术语和规则见[证明变异体](proof-mutants.md)。验收套件运行这里所说的列表；它在提交 `bde170e9` 上全部通过。

本记录为每组目标各设一节。“结构性”“重述”“脚本行”“键”和“语义列表”的定义见[证明变异体的“术语”一节](proof-mutants.md#terms)。

## `Goal.deflate`

`Goal.deflate` 的带键行（`tests/proof-mutants/public-deflate.tsv`）是对 `deflate` 函数体的单文件修改。每一行都先在 `deflate_phases` 处被拒绝；这是把 `deflate` 拆成各阶段的那条 `rfl` 等式，对函数体的任何修改都会在那里失败。所以这些行说明已登记的证明与翻译绑定在一起，不说明它依赖被变异的那个检查。它们之所以可以用于精确重放，只是因为语义上的杀死由每个变异体分片都运行的脚本行列表承担：`deflate-header.tsv`（头部的各阶段和 `_tr_flush_block`）、`deflate-strategies.tsv`（`fill_window`、`longest_match` 和各策略）以及 `deflate-ops.tsv`（流操作）。每个脚本行在翻译和证明对它的每一处重述中做同样的修改，并在它的语义引理中被杀死。

## `Goal.deflateCopy` 和拒绝目标

`Goal.deflateCopy` 在 `tests/proof-mutants/public-streams.tsv` 中的五行都是结构性的：
- 目的流为 `NULL` 时返回 `Z_OK`；
- 状态分配失败时返回 `Z_OK`；
- 缓冲区分配失败的路径保留 `dest->state`；
- 缓冲区分配失败的路径跳过对 `pending_buf` 的释放；
- 副本的回指指针被设为源流。

每一行都被重放拒绝；`deflate_copy_public`（`ZlibF/Proof/public-deflate-copy.lean`）的重放峰值约为 10.4 GB。拒绝目标 `Goal.inflate_refusal` 和 `Goal.deflate_refusal` 没有键。它们的行在 `tests/proof-mutants/stream-refusal.tsv` 中，由变异体分片用重新繁释检查：每一行把一次拒绝改成 `Z_OK`。

## 各函数的安全目标

对大多数函数，安全目标的行就是功能目标的行：流调用的安全证明是序列定理（`inflate_sequence_safety_public`、`deflate_sequence_safety`；一次调用用第 2 个子句，`End` 用第 3 个子句）的推论，初始化、复制和无状态函数的安全证明是它们的功能证明的推论，所以同样的翻译修改会让它们失败。没有这类行的函数，它们的行在 `tests/proof-mutants/public-safety.tsv` 中，都是结构性的：
- `compress`、`compress_z`、`compress2`：不把长度指针传下去（改传 `NULL`）。`api-boundary.tsv` 中让 `compress2` 在 `destLen` 为 `NULL` 时直接返回的那一行，不是 `Goal.compress2_safety` 的变异体：C 先读取 `*destLen`，所以这个目标排除了 `NULL` 长度（`CompressorSafety` 取 `nullableLength = false`），重放接受这一行；
- `uncompress2`：目的长度从 `sourceLen` 读取；去掉对一个局部单元的释放；
- `uncompress_z`、`uncompress`：把源长度单元当作目的长度传下去；去掉对局部单元的释放；
- `deflateBound`：丢弃结果；`deflateBound_z`：去掉状态检查；
- `deflatePrime`：去掉 `bits > 16` 的测试；去掉待输出空间的测试；
- `inflateSync`：局部缓冲区是三个字节，而不是四个。

`deflateParams` 和 `deflateSetDictionary` 使用 `stream-refusal.tsv` 中它们的拒绝行。去掉 `deflateEnd` 或 `inflateEnd` 调用的行，属于发出这个调用的函数 `compress2_z` 和 `uncompress2_z`。`Goal.deflate_initialisation_domain` 没有键：它陈述的是 `deflateInit2_` 成功的运行，`deflateInit2_` 的四行就是它的变异体：对 `deflate_initialisation_domain_public` 的内核重放拒绝全部四行（峰值约 3.4 GB）。

## `Goal.inflate_back_sequence_safety`

它的十一行在 `tests/proof-mutants/infback-sequence.tsv` 中：`inflateBack` 四行，`inflateBackInit_` 四行，`inflateBackEnd` 三行，都是结构性的：
- `inflateBack`：流为 `NULL` 时返回 `Z_OK`；模式没有重置为 `TYPE`；输出从 `NULL` 而不是从窗口开始；结束之后最后一个窗口被拒绝时返回 `Z_OK`；
- `inflateBackInit_`：状态没有存入流；窗口没有存入；分配失败时返回 `Z_OK`；`sane` 被清零；
- `inflateBackEnd`：跳过对状态的释放；保留 `strm->state`；返回 `Z_STREAM_ERROR`。

收尾部分的那一行是脚本行（`infback-sequence.py`），它在重述 `backTail` 中做同样的修改，于是失败的是语义引理，而不是 `inflateBack_eq` 的 `rfl`。变异体分片用重新繁释检查这些行。用每一行的翻译修改对 `inflate_back_sequence_safety` 做内核重放，也拒绝全部十一行；原证明的重放峰值约为 9.8 GB。

## gz 目标

gz 目标没有键；它们的行在三个语义列表中。
- `tests/proof-mutants/gz-refusal.tsv`，对应 `Goal.gz_refusal`：十九行，每一行是在 `NULL` 句柄上返回另一个值，或去掉一次 `NULL` 测试，涉及除 `gzread` 和 `gzfread`（在 `gz-read.tsv` 中）以及 `gzbuffer`、`gzeof` 和 `gzoffset64`（在 `public-streams.tsv` 中）之外的每个 gz 函数。这个目标的各子句靠求值成立，所以每一行都在 `public-gz-refusal` 中失败。
- `tests/proof-mutants/gz-sequence.tsv`，对应 `Goal.gz_sequence_safety`：写入调用（`gzwrite`、`gzfwrite`、`gzputc`、`gzputs`、`gzvprintf` 以及由它实现的 `gzprintf`、`gzflush`、`gzsetparams`），关闭（`gzclose_w`、`gzclose_r`、`gzclose` 的分派），打开（`gz_open`、`gzdopen`），`gzseek64` 和 `gztell64`，`gz_error`（跳过一次释放；为 `Z_MEM_ERROR` 分配消息），`gzgetc()` 宏的两个分支（`zlib.h.lean`：去掉 `have` 测试；`pos` 不前进），读取一侧的 `gzgetc`、`gzungetc`、`gzgets` 和 `gzdirect`，以及补丁 0002 到 0005 的每个补丁块各一行，去掉这个补丁块（也就是未打补丁的 C）。大多数行是脚本行（`gz-sequence.py`），它们在代码的每一处 `rfl` 重述（`gzwrite_eq`、`putcSlow`、`closeTail`、`pfFmt`、`gTail`、`seekTail`、`openAfterMode`、`fetchBody`、`restK`、`getsRest`，以及 `gz_error` 的几份私有副本）中做同样的修改，于是失败的是语义引理，而不是重述。
- `tests/proof-mutants/gz-read.tsv`（连同 `gz-read.py`），来自读取一侧：`gzread` 和 `gzfread`，`gzgetc` 与 `gzungetc` 的拒绝情形，以及 `gzclose_r`。其中 `gzungetc` 的两行 `gzungetc-mode-check` 和 `gzungetc-skip-dropped` 还指定了步骤引理所在的模块 `gz.read-getc-step`：只指定 `gzread.c.getc-ungetc` 时，`gzungetc_step` 的证明不会被构建，两行都能构建通过；加上它之后，两行都在那里被杀死。

**第一个错误落在哪里。**每一行都在被变异函数的某个证明中被杀死：它的步骤引理，它的函数体的精确运行，或者（对被调用函数）那个被调用函数的证明。有五行指定了步骤引理之外的模块，它们都是被变异函数的证明：
- `gz_open` 的三行在 `gz_open` 的精确运行中失败（`gzlib.c.open-init` 中的 `gz_open_empty_mode`，`gzlib.c.open-io` 中的 `openAfterPath_writer`：后者是 `gz_open` 的 I/O 尾部，它释放路径并调用 `gz_reset`）；
- `gzdopen` 的一行在 `gzdopen` 的运行中失败（`gzdopen_writer_regular_run`，`gzlib.c.dopen-entry`）；
- `gztell64` 的一行在 `gztell64` 的运行中失败（`gztell64_run`，`gzlib.c.simple`）。

`gzclose_w` 的各行在 `closeTail_ok`（`gzwrite.c.close`）中失败，这是 `gzclose_w` 的释放证明；`gzclose` 的分派行在 `gzclose_dispatch` 中失败。有一行是被心跳超时杀死的，不是被类型错误杀死的：`patch0004-fetch-copy-room-removed`，在 `fetch_look`（`gz.read-fetch`）中，这是同一个函数 `gz_fetch` 的证明。

**发现目标有误的一行。**行 `macro-have-guard-dropped` 起初存活了下来：目标只在 `x.have ≠ 0` 时运行这个宏，所以它的 `have = 0` 分支从未被运行。目标已经更正（3c5292f7；回归测试 `tests/verification/regressions/gz-macro-have-zero.lean`），这一行在 `zlib.h.gzgetc-macro` 中被杀死。

**gz 各列表的内核重放。**变异体分片用重新繁释检查这三个列表。对 `gz_refusal` 的内核重放拒绝全部十九个拒绝行（每次重放在两秒内结束）。另一次内核重放针对 `gz_sequence_safety_public`，使用每个结构性行的翻译修改。位于循环体内或涉及机器算术的行没有交给它：`patch0003-*`，`gz_fetch` 和 `gz_read` 的三个 `patch0004` 行，`patch0004-gets-room-removed`，`gzgets-left-whole-length` 和 `gztell64-adds-max`。重放接受原证明（51615 个依赖，峰值约 10.7 GB）。交给它的 36 行中，它拒绝了 29 行，多数是在被变异函数的重述处（`gzwrite_eq`、`gzclose_w_eq`、`gzgetc_macro_eq` 等），峰值为 10.7 GB。有七行在得出判定之前达到了 12 GiB 的预算：`gzvprintf-length-check-dropped`、`gz_open-open-failure-path-leak`、`gz_open-reset-skipped`、`gzseek64-have-not-consumed`、`gzseek64-skip-wrong`、`patch0005-seek-next-unconditional` 和 `patch0004-printf-position-check-removed`。它们所在的函数（`gzvprintf`、`gz_open`、`gzseek64`）含有循环，函数体不同时内核会展开这个循环；对这些行，证据是重新繁释时的杀死。

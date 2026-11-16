<!-- source-sha256: 0d6c83cd0bfeb3493157f4aeedc90b99440c8c4f348d7d289604c748f1dc23b0 -->
# 覆盖情况：审查记录

本页是历史资料。它原样保存 `docs/progress.md` 中“zlib.h 函数的无故障覆盖”一节在表格移到[按函数查覆盖情况](../coverage.md)之前的内容。各行最后一次与 `dev` 核对是在 `6a097d3b`，2026-11-14。其中的状态和层级描述的是当时的情况：例如它把已登记的拒绝目标写成 `(checked)`，并在安全定理一栏里写了 `inflate` 的功能定理。现行的表格改正了这两处。

文中的标签指的是当时的审查轮次和工作批次：`audit A1`、`A2`、`B1` 和 `B3` 是 2026-11-14 对 gz 安全目标所作的一次对抗性审读得出的发现；`batch C` 是证明 `gzgetc`、`gzungetc`、`gzgets` 和 `gzdirect` 各步骤的那一批工作。


zlib.h 文档化的每个函数占一行。每行给出表明该调用不会出错的已检查定理，以及所走的路线：它自己的目标、序列目标（该调用是一个 `StreamOperation`）、`StreamSequenceSafety` 的 End 子句，或 open。各行最后一次核对的是 `dev` 的 `6a097d3b`（2026-11-14）。“已登记”指列入 `tests/audit/theorems.txt`。验收套件在其后的提交 `bde170e9` 上全部通过（见[范围](../progress.md#scope)）。定理或目标变化时，需重新核对对应行。

每条流路线或工具函数路线共有的模型级前提，不在每行重复：默认分配器（`DefaultOrNull`/`DefAlloc`/`zfree = zcfree`；已声明的目标限制）、堆良构性（`Fresh`、`Uniq`、`LibraryGlobals`），以及对 inflate、工具函数和 inflateBack 而言的 `ByteObjectsFit`（`docs/deviations.md` 中的平台行）。

缩写：
- **SeqI** = `Goal.inflate_sequence_safety`：`Zlib.Inflate.Proofs.inflate_sequence_safety_public`（`public-inflate-sequence-safety.lean`，已登记）。
- **SeqD** = `Goal.deflate_sequence_safety`：`Zlib.Deflate.Universal.deflate_sequence_safety`（`public-deflate-goals.lean`，已登记）。
- 两者都只覆盖 `p = some r` 且 `StreamReachable r`（以及 `StreamArguments`）的情形。两者都不覆盖 NULL 流或不一致的流（zalloc/zfree 为 NULL、state 为 NULL，或检查拒绝的 state）。zlib.h 把这些情形文档化为 `Z_STREAM_ERROR` 拒绝，`docs/spec/safety.md` 的 A1 把文档化的空指针拒绝保留在范围内。“refusal”一列说明是否有定理覆盖该情形。

## 流：deflate

| 函数 | 路线 | 定理（Lean 名称，文件） | 已登记？ | 定义域缺口或备注 |
| --- | --- | --- | --- | --- |
| deflateInit_（宏 deflateInit） | 自身目标 | `ZlibF.Spec.Public.Proofs.DeflateInit.deflateInit_proof`，`public-deflate-init.lean` | 是 | 完整：错误版本（`VersionValue`，NULL 或可读的首字节）、错误的 `stream_size`（任意 `p`）、NULL strm、每个 level、分配失败。 |
| deflateInit2_（宏 deflateInit2） | 自身目标 | `ZlibF.Spec.Public.Proofs.DeflateInit2.deflateInit2_proof`，`public-deflate-init2.lean` | 是 | 完整，同 deflateInit_，另加每个 method/windowBits/memLevel/strategy。`Goal.deflate_initialisation_domain`（非空性）已登记（`DeflateInitDomain.deflate_initialisation_domain_public`）。 |
| deflate | 自身目标 + SeqD | `Zlib.Deflate.Universal.deflate_safety`，`public-deflate-goals.lean` | 是 | 可达 + `DGood` + `StreamBuffers` + `ActiveHeader`（分离行）。Refusal：`Goal.deflate_refusal`（checked）覆盖 NULL 与不一致的流。 |
| deflateEnd | 自身目标 + SeqD 的 End 子句 | `ZlibF.Spec.Public.DeflateEndProof.deflate_end_public`，`public-deflate-end.lean`；SeqD 的第 3 子句 | 是 | 自身目标需要 `DGood`。Refusal：`Zlib.Deflate.Proofs.deflateEnd_reject`（`deflate.c.life.end.lean`，已登记）覆盖 NULL、zalloc/zfree 为 NULL、state 为 NULL，以及被拒绝的活动 state。因此已覆盖：从未初始化（模型指针为 NULL）、NULL、state 为 NULL，以及复制失败之后。它不是类型为目标的定理。 |
| deflateSetDictionary | 安全目标 + SeqD | `Goal.deflateSetDictionary_safety`（已登记）；SeqD | 是 | 自身的功能目标 `Goal.deflateSetDictionary`（不在计划内）：无定理。Refusal：`Goal.deflate_refusal`（checked）覆盖 NULL 与不一致的流。 |
| deflateGetDictionary | 自身目标 + SeqD | `ZlibF.Spec.Public.DeflateDictionaryProof.deflate_getdict_public`，`public-deflate-getdict.lean` | 是 | 自身目标需要 `DGood`，且目标缓冲区与窗口分离。Refusal：`Zlib.Deflate.Proofs.deflateGetDictionary_reject`（`deflate.c.life.getdict.lean`）已登记。 |
| deflateCopy | 自身目标 | `Zlib.Deflate.Universal.deflate_copy_public` / `deflate_copy_safety`，`public-deflate-copy.lean` | 是 | 不是 `StreamOperation`；`StreamReachable.deflateCopy` 只为 SeqD 的第 1 子句提供输入。缺口：`source ≠ dest`（偏差行）。不一致的源由 `Goal.deflate_refusal`（checked）覆盖。 |
| deflateReset | 自身目标 + SeqD | `ZlibF.Spec.Public.DeflateResetProof.deflate_reset_public`，`public-deflate-reset.lean` | 是 | Refusal：`Zlib.Deflate.Proofs.deflateReset_reject`（已登记）。 |
| deflateParams | 安全目标 + SeqD | `Goal.deflateParams_safety`（已登记）；SeqD | 是 | 自身的功能目标 `Goal.deflateParams`（不在计划内）：无定理。Refusal：`Goal.deflate_refusal`（checked）覆盖 NULL 与不一致的流。 |
| deflateTune | 自身目标 + SeqD | `ZlibF.Spec.Public.DeflateQueryProof.tune_public`，`public-deflate-small-queries.lean` | 是 | 完整（`CheckedDeflate` 包含各 refusal）。 |
| deflateBound | 安全目标 + SeqD | `Goal.deflateBound_safety`（已登记）；SeqD | 是 | 自身的功能目标 `Goal.deflateBound`（不在计划内）：无定理。SeqD 需要 `ActiveHeader ∧ DeflateHeaderLive`。Refusal：`deflateBound_nostate`（已登记）。 |
| deflateBound_z | 安全目标 + SeqD | `Goal.deflateBound_z_safety`（已登记）；SeqD | 是 | 同 deflateBound（`deflateBound_z_nostate`，已登记）。 |
| deflatePending | 自身目标 + SeqD | `ZlibF.Spec.Public.DeflateQueryProof.pending_public` | 是 | 完整。 |
| deflateUsed | 自身目标 + SeqD | `ZlibF.Spec.Public.DeflateQueryProof.used_public` | 是 | 完整。 |
| deflatePrime | 安全目标 + SeqD | `Goal.deflatePrime_safety`（已登记）；SeqD | 是 | 自身的功能目标 `Goal.deflatePrime`（不在计划内）：无定理。SeqD 需要 `DeflateNotStarted`，这是 zlib.h 自己的次序规则。Refusal：`deflatePrime_refused`（已登记）。 |
| deflateSetHeader | 自身目标 + SeqD | `ZlibF.Spec.Public.DeflateQueryProof.header_public` | 是 | 完整。SeqD 需要 `DeflateNotStarted`（zlib.h 的次序）。 |

## 流：inflate

| 函数 | 路线 | 定理（Lean 名称，文件） | 已登记？ | 定义域缺口或备注 |
| --- | --- | --- | --- | --- |
| inflateInit_（宏 inflateInit） | 自身目标 | `ZlibF.Spec.Public.Proofs.InflateInit.init15_public`，`public-inflate-init.lean` | 是 | 完整：错误版本或大小、NULL strm、分配失败。 |
| inflateInit2_（宏 inflateInit2） | 自身目标 | `ZlibF.Spec.Public.Proofs.InflateInit.inflate_init2_public`，`public-inflate-init2.lean` | 是 | 完整，每个 `windowBits`。 |
| inflate | 自身目标 + SeqI | `Zlib.Inflate.Proofs.inflate_public`，`public-inflate.lean` | 是 | 可达 + `Good` + `ByteObjectsFit` + `StreamBuffers` + `ActiveHeader`。Refusal：`Goal.inflate_refusal`（checked）覆盖 NULL 与不一致的流。 |
| inflateEnd | 自身目标 + SeqI 的 End 子句 | `ZlibF.Spec.Public.InflateEndProof.inflate_end_public`，`public-inflate-end.lean`；SeqI 的第 3 子句 | 是 | 自身目标需要 `Good`。Refusal：`Goal.inflate_refusal`（checked）覆盖 NULL 与不一致的流。 |
| inflateSetDictionary | 自身目标 + SeqI | `ZlibF.Spec.Public.Proofs.inflateSetDictionary_public`，`public-inflate-setdict.lean` | 是 | 自身目标需要 `Good`、`zalloc = zcalloc`，以及与窗口分离的字典（偏差行）。Refusal：`Goal.inflate_refusal`（checked）覆盖 NULL 与不一致的流。 |
| inflateGetDictionary | 自身目标 + SeqI | `ZlibF.Spec.Public.InflateDictionaryProof.inflate_getdict_public` | 是 | 自身目标需要 `Good`，且目标缓冲区与窗口分离。Refusal：`Goal.inflate_refusal`（checked）覆盖 NULL 与不一致的流。 |
| inflateSync | 安全目标 + SeqI | `Goal.inflateSync_safety`（已登记）；SeqI | 是 | 自身的功能目标 `Goal.inflateSync`（不在计划内）：无定理。Refusal：`inflateSync_check`（已登记）。 |
| inflateCopy | 自身目标 | `Zlib.Inflate.Proofs.inflate_copy_public`，`public-inflate-copy.lean` | 是 | 不是 `StreamOperation`。缺口：`source ≠ dest`（偏差行）。不一致的源由 `Goal.inflate_refusal`（checked）覆盖。 |
| inflateReset | 自身目标 + SeqI | `ZlibF.Spec.Public.InflateResetProof.reset_public` | 是 | 自身目标需要 `InflateView`。Refusal：`Goal.inflate_refusal`（checked）覆盖 NULL 与不一致的流。 |
| inflateReset2 | 自身目标 + SeqI | `ZlibF.Spec.Public.InflateReset2Proof.reset2_public` | 是 | 每个 `windowBits`。Refusal：`Goal.inflate_refusal`（checked）覆盖 NULL 与不一致的流。 |
| inflatePrime | 自身目标 + SeqI | `ZlibF.Spec.Public.InflatePrimeProof.prime_public` | 是 | 完整（`CheckedInflate`）。接受分支需要 `s.bits ≤ 39`，这是不变量的一个事实。 |
| inflateMark | 自身目标 + SeqI | `ZlibF.Spec.Public.InflateMarkProof.mark_public` | 是 | 完整。 |
| inflateGetHeader | 自身目标 + SeqI | `ZlibF.Spec.Public.InflateHeaderProof.getheader_public` | 是 | 在 `InflateView` 上完整。支持 gzip 的流需要 `head ≠ NULL`：C 会解引用它，而 zlib.h 不提供 NULL。SeqI 还需要 `p ≠ none`。Refusal：`inflateGetHeader_check`（已登记）。 |

## 回调解码器

这三个函数还没有各自的安全目标：它们的安全由序列目标承担（见[按顺序的下一步工作](../progress.md#ordered-next-work)）。

| 函数 | 路线 | 定理（Lean 名称，文件） | 已登记？ | 定义域缺口或备注 |
| --- | --- | --- | --- | --- |
| inflateBackInit_（宏 inflateBackInit） | 自身目标 | `ZlibF.Spec.Public.InflateBackInitProof.back_init_public`，`public-infback-init.lean` | 是 | 完整：错误版本或大小、NULL strm、NULL 窗口、错误的 `windowBits`、分配失败。成功分支需要一个可写的 `2^wb` 字节窗口（zlib.h 自己的规则）。 |
| inflateBack | 序列（`Goal.inflate_back_sequence_safety`） | `Zlib.Infback.Safety.inflate_back_sequence_safety`，`infback.c.safety-fast.lean`（已检查，c7169b54） | 是 | 已登记，带 `inflateBack`、`inflateBackInit_` 与 `inflateBackEnd` 的十一个结构性证明变异（`tests/proof-mutants/infback-sequence.tsv`），每个都被杀死，并被目标定理的内核重放拒绝。自身的 `Goal.inflateBack`（功能性）不在计划内。NULL strm 和 state 为 NULL 已覆盖（`inflateBack_nullstream`、`inflateBack_nostate`，已登记）。该目标还有收窄：`inputBound < 2^48`，窗口是堆字节块的一个切片，每个输入块都位于堆字节块内（偏差行）。 |
| inflateBackEnd | 自身目标 | `ZlibF.Spec.Public.InflateBackEndProof.back_end_public`，`public-infback-end.lean` | 是 | 完整：NULL、state 为 NULL 或 zfree 为 NULL，以及 `BackValid`。inflateBack 序列目标的第 4 子句在 `inflate_back_sequence_safety` 中得到证明（`back_end_blk`）。 |

## 校验和

| 函数 | 路线 | 定理 | 已登记？ | 定义域缺口或备注 |
| --- | --- | --- | --- | --- |
| adler32 | 自身目标 | `ZlibF.Spec.Public.AdlerUpdateProof.adler_public`，`public-adler-update.lean` | 是 | **更窄**：NULL `buf` 只在 `len = 0` 时允许（`AdlerBufferBytes`，偏差行）。`len = 1` 时 C 会读 `buf[0]`，这是真实的错误（上游 PR #1364 已关闭，并宣布了 zlib.h 的限制）。`len ≥ 2` 的 NULL 在 C 中安全，但未证明。 |
| adler32_z | 自身目标 | `...AdlerUpdateProof.adler_z_public` | 是 | 同 adler32。 |
| adler32_combine / _combine64 | 自身目标 | `...AdlerCombineProof.combine_public` / `combine64_public` | 是 | 完整。 |
| crc32 / crc32_z | 自身目标 | `ZlibF.Spec.Public.Proofs.crc32` / `crc32_z`，`public-crc-updates.lean` | 是 | 完整（`BufferBytes` 包含任意长度的 NULL）。`CrcGlobals` 是模型静态数据的前提。 |
| crc32_combine / _combine64 | 自身目标 | `...CrcCombineProof.combine` / `combine64` | 是 | 完整。 |
| crc32_combine_gen / _gen64 | 自身目标 | `...CrcCombineProof.gen` / `gen64` | 是 | 完整。 |
| crc32_combine_op | 自身目标 | `...CrcCombineProof.op` | 是 | `op` 必须来自 `crc32_combine_gen`（与 zlib.h 一致）。 |
| get_crc_table | 自身目标 | `ZlibF.Spec.Public.Proofs.get_crc_table` | 是 | zlib.h 中未文档化（不是必需的）。 |

## 工具函数

| 函数 | 路线 | 定理 | 已登记？ | 定义域缺口或备注 |
| --- | --- | --- | --- | --- |
| compress / compress_z / compress2 / compress2_z | 安全目标 `Goal.compress*_safety` | `ZlibF.Spec.Public.Proofs.Compress.compress_safety`、`compress_z_safety`、`compress2_safety`、`compress2_z_safety`，`public-compress-safe-mid.lean` | 是 | 源与目标缓冲区分离（偏差行）。长度单元建模为 `Option` 标量，所以长度单元与数据别名在模型之外（偏差行）。每个 level。功能性的 `Goal.compress*`（不在计划内）没有定理。 |
| uncompress / uncompress_z / uncompress2 / uncompress2_z | 安全目标 `Goal.uncompress*_safe` | `ZlibF.Spec.Public.Proofs.Uncompress.uncompress_safe` 等，`public-uncompress-safe.lean` | 是 | `UtilitySeparation`：数据单元与长度单元两两分离（偏差行）。功能性的 `Goal.uncompress*`（不在计划内）没有定理。 |
| compressBound / compressBound_z | 自身目标 | `ZlibF.Spec.Public.Proofs.compressBound` / `compressBound_z` | 是 | 完整。 |
| zlibVersion | 自身目标 | `ZlibF.Spec.Public.Proofs.zlibVersion` | 是 | 完整。 |
| zlibCompileFlags | 自身目标 | `ZlibF.Spec.Public.Proofs.zlibCompileFlags` | 是 | 完整。 |
| zError | 自身目标 | `ZlibF.Spec.Public.Proofs.zError` | 是 | 未文档化（不是必需的）。 |

## Gzip 文件接口

gz 函数还没有各自的安全目标：它们的安全由序列目标承担（见[按顺序的下一步工作](../progress.md#ordered-next-work)）。

`Goal.gz_sequence_safety`（`ZlibF/Spec/Public/GzSafety.lean`）是 gzip 接口的安全目标。它已登记在 `goals.txt`
和 `safety_goals` 中，已无前提地检查（`gz_sequence_safety_public`，`public-gz-sequence-safety.lean`），并已登记在 `theorems.txt` 中，带每组 gz 函数以及补丁 0002 到 0005 每个补丁块的证明变异（`gz-sequence.tsv`、`gz-read.tsv`、`docs/checking/proof-mutants.md`）。它的非空性目标 `Goal.gz_sequence_nonvacuity`（`gz_sequence_nonvacuity_public`）也已登记。`gz_sequence_safety_of (L : GzReadLeaves)`（`gz.sequence-safety.lean`）从六个读取叶子证明它，六个都已证明。
其他调用都直接证明：打开、关闭、写入和查询。`gzread_step` 与 `gzfread_step` 随读取侧的 `gz.read-assembly` 关闭。
`gzgetc_step`、`gzungetc_step`、`gzgets_step` 与 `gzdirect_step` 属于 batch C。目标的定义域是单个句柄的每条历史（`GzHistory`）在每个 OS 世界中（`GzWorldStep`）。
一次对抗性审读（2026-11-14）未发现错误的子句，发现三个缺口：`gzgetc` 宏的内联路径、`NULL` 句柄，以及一条未列出的 fd 规则（见下表）。三个都已关闭：宏步骤在目标中（A1），`NULL` 句柄有 `Goal.gz_refusal`（A2），fd 规则已从目标中删除（B1）。

| 函数 | 途径 | 定理 | 已登记？ | 定义域缺口或说明 |
| --- | --- | --- | --- | --- |
| gzopen、gzopen64 | 打开叶子 | `gzopen_safe`（`gz.inv-open-fresh`）、`gzopen64_safe` | 经由 `gz_sequence_safety_public` | 每个路径、模式与世界。 |
| gzdopen | 打开叶子 + 自身目标 | `gzdopen_safe`（`gz.inv-open`）；`gzdopen_complete`（`Goal.gzdopen`） | 是（自身目标） | 每个 `fd`。 |
| gzbuffer、gzeof、gzerror、gzclearerr、gztell、gztell64、gzoffset、gzoffset64、gzrewind、gzseek、gzseek64 | 序列叶子 | `gzbuffer_step`、`gzeof_step`、`gzerror_step`、`gzclearerr_step`、`gztell*_step`、`gzoffset*_step`、`gzrewind_step`、`gzseek*_step`（`gz.inv-*`） | 经由 `gz_sequence_safety_public` | gzbuffer、gzeof、gzerror、gzclearerr、gzoffset 与 gzrewind 的自身功能目标另行登记。 |
| gzwrite、gzfwrite、gzputc、gzputs、gzprintf、gzvprintf、gzflush、gzsetparams | 序列叶子 | `gzwrite.c.safety`（`gzwrite_step` …） | 经由 `gz_sequence_safety_public` | `gzprintf`/`gzvprintf`：`GzArguments` 在每次调用时都要求可表示的格式，读取者也不例外（审读 B3）。 |
| gzclose、gzclose_w、gzclose_r | 关闭叶子 | `gzclose_step`、`gzclose_w_step`、`gzclose_r_step_safe` | 经由 `gz_sequence_safety_public` | |
| gzread、gzfread | 读取叶子 | `GzRead.gzread_step`、`GzRead.gzfread_step`（`gz.read-assembly`） | 经由 `gz_sequence_safety_public` | |
| gzgetc、gzgetc_、gzungetc、gzgets、gzdirect | 读取叶子 | `GzRead.gzgetc_step`、`GzRead.gzungetc_step`（`gz.read-getc-step`）、`GzRead.gzgets_step`、`GzRead.gzdirect_step` | 经由 `gz_sequence_safety_public` | |
| zlib.h 的 `gzgetc()` 宏 | 历史步骤 + 目标合取项 | `GzMacro.gzgetc_macro_safe`（`zlib.h.gzgetc-macro`） | 经由 `gz_sequence_safety_public` | 已关闭（审读 A1；在证明变异 `macro-have-guard-dropped` 存活后于 3c5292f7 更正）：每一次宏调用都是 `GzHistory.getcMacro`；有缓冲输出时是内联路径，`x.have = 0` 时是对函数的调用，经由 `gzgetc_step` 在 `ReadsFinite` 下覆盖。差分测试：`tests/gen/gz.py` 的操作 `getcm`（也在 `x.have = 0` 时：刚打开之后、写入句柄上、空文件上）。 |
| `NULL` 句柄上的所有 gz 函数 | 自身安全目标 | `ZlibF.Spec.Public.GzRefusalProof.gz_refusal`（`Goal.gz_refusal`，`public-gz-refusal.lean`） | 是，带证明变异（`gz-refusal.tsv`） | 已关闭（审读 A2）：29 个函数中的每一个都返回其文档化的值，堆和世界不变。C 测试 `tests/goals/gz-refusal`：204 次调用，无违例。`gzgetc` 宏用于 `NULL` 在 C 中是未定义行为；目标陈述的是函数。 |
| 同一 fd 上的第二个句柄 | 世界步骤 | `GzHistory.world` | 否 | 已覆盖（审读 B1，已更正）：`GzWorldStep` 是任意良构的世界，另一方可以关闭或重用句柄的 fd（[回归](../../tests/verification/regressions/gz-world-closes-fd.lean)）。 |

## 误计与未完成项

zlib.h 文档化的每个函数都有已登记的无故障定理，定义域如各行所述。尚未完成或定义域较窄之处：

1. **逐函数的安全目标**：gz 函数以及 `inflateBackInit_`、`inflateBack`、`inflateBackEnd` 的逐函数安全目标尚未陈述。它们的安全由 `Goal.gz_sequence_safety` 和 `Goal.inflate_back_sequence_safety` 承担。
2. **比 zlib.h 更窄的定义域**，每一项在[偏差](../deviations.zh.md)中都有一行：`inflateBack`（`inputBound < 2^48`；窗口和每个输入块都位于堆字节块内）；`inflateCopy` 和 `deflateCopy`（`source ≠ dest`）；`adler32` 和 `adler32_z`（`buf` 为 NULL 时只允许 `len = 0`：`len = 1` 在 C 中确实出错，`len ≥ 2` 时 NULL 在 C 中是安全的，但尚未证明）。
3. **自身的功能目标**：`deflateParams`、`deflateSetDictionary`、`deflatePrime`、`deflateBound`、`deflateBound_z` 和 `inflateSync` 的功能目标没有定理，也不在计划内。它们的安全目标已登记。

早先的编号列表（包括此后已关闭的各项）见[无故障覆盖：早先的未完成项](coverage-open-items.zh.md)。


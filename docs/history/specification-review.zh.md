<!-- source-sha256: ad4c04e95edeb242d4aa73b10470fba0f7597125422107929b339b2cfea0faf5 -->
# 规格审查记录（历史）

本页保存[进度](../progress.zh.md)“规格审查”一节中六条已结束的记录，内容是必需目标在 `bde170e9` 上通过验收之后的原文，除相对链接外未作改动。
这是历史记录：其中的状态（如 open、checked、“未完成”“已检查”）、工时、数字和日期反映各条目写作时的情况，不是当前状态。
当前状态和剩余工作只在[进度](../progress.zh.md)中。

### 规格审查

#### Gzip 定位模式

已修正。原先的 `GzSeek` 允许成功的定位返回另一种模式的句柄，因此抽象目标 `gz_seek_read` 不成立。现在该关系保持模式不变。该目标已有[本地检查的证明](../../ZlibF/Proof/Api/GzSeekRead.lean)，原反例已改为[回归检查](../../tests/verification/regressions/gz-seek-mode.lean)。登记和指定提交上的 CI 尚未完成。这是模型问题，不是 zlib 问题。

#### Inflate 初始化清理

已修正。窗口参数非法时，原 `inflateInit2_` 目标要求状态表在结构上完全不变，但分配后再释放会使该表变长。现在该分支逐项比较每个对象表（`SameObjectsUpToTableShape`）；没有任何 C 操作能观察到表的长度。该目标已有[本地检查的证明](../../ZlibF/Proof/public-inflate-init2.lean)，原反例已改为[回归检查](../../tests/verification/regressions/inflate-init2-table-shape.lean)。登记和指定提交上的 CI 尚未完成。这是契约问题，不是 zlib 问题。

#### 解压工具函数的清理

已修正。`UncompressCounted` 和 `UncompressSingle` 用 `SameObjects` 比较调用后的堆，它要求对象表相等，包括表的物理长度。`uncompress2_z` 在检查参数之前分配一个局部 `z_stream` 和一个 8 字节局部块，并在每条路径上释放二者；释放后的表项作为空项留在表中。因此连空参数拒绝路径也使四个解压目标不成立。现在它们逐项比较对象表（`SameObjectsUpToTableShape`，移到 `Spec/Public/Memory.lean`），与 `inflateInit2_` 的契约相同。反例保留为[回归](../../tests/verification/regressions/uncompress-table-shape.lean)。这是契约问题，不是 zlib 问题。`CompressorContract` 曾有相同的模式（`compress2_z` 也释放一个局部 `z_stream`）。

这四个契约还缺少堆的表示条件 `Uniq`（`nextBlk` 以下每个块标识只对应一个对象）。[可信基础](../trusted-base.md)要求每个初始堆满足它，每个公开流历史也已假设它（`InitDomain`、`StreamReachable`）。现在它是前提。它不缩小 C 的定义域：每个 C 状态都有这样的表示。

压缩函数的契约也已修正。`CompressorContract` 和 `CompressorSafety` 有这两个缺陷。`compress2_z` 在参数检查之后的每条路径上都释放局部 `z_stream`，它留下的空表项使目标不成立，即使 `deflateInit` 在分配之前就拒绝了压缩级别（公开调用者见证上的级别 10：[回归](../../tests/verification/regressions/compress-table-shape.lean)）。现在它们用 `SameObjectsUpToTableShape`。它们也缺少 `Uniq`，而 `deflateInit` 的契约和 `deflate` 流历史（`StreamReachable.deflateInit`）都假设它；现在它是前提。`CompressorSafety` 的陈述测试：`tests/goals/compress-safety`（ASan、UBSan、泄漏计数、分配失败、无效级别；9000 次运行无违反）。

独立审查已经修正的共享关系 `Uncompress2`。延迟距离处理和精确释放的修正，都有独立反例和经过检查的回归证明；实现精化仍未完成。原先在内存失败时要求输出为空的条款，以及在缓冲区错误时要求扩展输出的条款，已依据现有成对反例移除。在把较早的抽象 gz 和字典模型当作完整操作精化之前，还须完成它们；具体公开目标不会假设被调用函数的契约成立。

#### Gzip 打开路径长度

已于 2026-11-13 修正。`gz_open` 用 `malloc(len + 1)` 和 `snprintf(state->path, len + 1, "%s", path)` 复制调用者路径。分两部分：

- `snprintf` 超过 `INT_MAX`：模型 `snprintf` 在此返回 -1，与 glibc 相同（[可信基础](../trusted-base.zh.md)，格式化）。不出错，陈述不变。
- `malloc` 超过 `PTRDIFF_MAX`：运行时分配器现在拒绝 `2^63` 字节及以上的请求，与 glibc 2.43 相同（[可信基础](../trusted-base.zh.md)，分配大小）。于是长度为 `2^63 − 1` 字节的路径使 `gzopen` 在没有预言失败、也没有调用 `open` 的情况下返回 NULL。`OpenContract` 原来的第二条款接受该路径，并要求模式无效、预言失败或 `open` 失败三者之一，因此它对修正后的模型为假。经过检查的反例是该[回归](../../tests/verification/regressions/gzopen-path-ptrdiff.lean)（`old_open_clause_false`）。`Goal.gz_initialisation_domain` 对同一路径也为假：它在 `NoAllocationFailure h` 下承诺返回句柄。复核：运行时修改（`6db5fca9`）、陈述更正（`b35b5523`）和字符串字面量 "position overflow"（`110d11cf`）已对照设计说明进行第二次阅读，没有异议。未完成：`malloc <n>` 差分测试行的 C 端尚未运行。

修正在单独的提交中。`OpenContract`（`Goal.gzopen`、`Goal.gzopen64`）第二条款：原前提为 `Fresh h → Uniq h → LibraryGlobals h → FileSystem fs → CString h path name → CString h mode flags`；新前提在 `FileSystem fs` 之后加入 `ZlibF.PlatformMemory.ByteObjectsFit h`。`Goal.gz_initialisation_domain` 第一条款：原前提为 `... FileSystem fs → NoAllocationFailure h → CString h path name → ...`；新前提在 `NoAllocationFailure h` 之后加入 `ByteObjectsFit h`。有了它，路径及其 NUL 位于同一个小于 `2^63` 字节的对象中，因此复制不会因大小被拒绝，`len + 1` 也不会回绕。见证条款和 `Goal.gzdopen`（19 字节路径）不变。这三个目标都尚未证明或登记。该前提就是已接受的平台范围（[偏差](../deviations.zh.md)，“平台字节对象范围”一行）。

#### 带本地修复的 gzip 库发现

2026-11-12 的库报告，在所有者决定 F-1 和 W7 是否作为已确认的发现移入 `README.md` 之前记录在这里。每一项都有本地补丁，经所有者于 2026-11-12 批准，尚未提交上游（[补丁](../../patches/README.md)）。

- F-1，[gzread 位置溢出](../findings/gzread-pos-overflow/README.md)：在 Linux 的 `/dev/zero` 上透明 `gzseek` 到 `INT64_MAX` 之后，`gzread` 使有符号的 `x.pos` 溢出。在 x86_64 Linux 上由 UBSan 确认。补丁 0004。
- W7，[gzwrite 位置溢出](../findings/gzwrite-pos-overflow/README.md)：`/dev/null` 上的透明写入者定位到 `INT64_MAX - 10` 后，`gzwrite` 使 `x.pos` 溢出（在 `INT64_MAX` 处的 `gzputc` 也是）。在 x86_64 Linux 上用真实设备由 UBSan 确认。补丁 0004。
- [gz look COPY 越过上限](../findings/gz-position-copy-overflow.md)：`gz_look` 的 COPY 分支缓冲了全部待处理输入而没有空间上限，因此在一个 gzip 成员、尾随数据和 `gzclearerr` 之后、接近 `GZ_OFF_MAX` 的读取者返回时 `x.pos + x.have` 越过该上限。已在模型中确认（`gz.position-copy-overflow-regression`）并通过阅读 C 确认；实际上无法复现（约 2^63 个解码字节）。补丁 0004，于 2026-11-13 扩展。随之的陈述变化：`GzLookSpec` 的 COPY 析取项现为 `how = COPY ∧ avail_in = 0 ∧ (x.have ≠ 0 ∨ x.pos = GZ_OFF_MAX) ∧ x.pos + x.have ≤ GZ_OFF_MAX`（原为 `how = COPY ∧ x.have ≠ 0`）；`gz_fetch` 的 `BodyPost` 允许循环在 `avail_in = 0` 的 COPY 中继续，其度量把 COPY 记为 0。
- R-3，[x.next 从未写入](../findings/gz-reset-next-uninitialised/README.md)：`gzopen` 之后立即调用的 `gzseek` 和 `gzdirect` 把从未写入的 `x.next` 前进零。按 C 标准的字面规定未定义；没有 sanitizer 报告。补丁 0005。
- R-4，[直接读取之后 x.next 悬空](../findings/gz-next-dangling-after-direct-read/README.md)：大块 `gzread` 读入调用者随后释放的缓冲区之后，`gzseek` 和 `gzdirect` 在已释放的缓冲区内把 `x.next` 前进零。按 C 标准的字面规定未定义；没有 sanitizer 报告。补丁 0005。

`gzread.c`、`gzwrite.c` 和 `gzlib.c` 的翻译跟上了两个补丁。只有 0005 有差分测试行（直接读入已释放的缓冲区，然后 `gzdirect` 和 `gzseek`）；0004 需要设备，文件模型无法表达。`tests/audit/theorems.txt` 仍列出已不存在的 `seekTail_dangling_ub` 和 `gzseek64_dangling_next_ub`；删除它们需由人来做。

#### OS 调用预言下的 Gzip 偏移与回绕

在 `caad9db4` 中经所有者授权修正；证据记录于此。OS 调用预言允许 `lseek` 返回 `[0, 2^63 - 1]` 中的任意值而不移动描述符（M3），某些 Linux 设备即如此。三个已登记目标陈述了 `lseek` 之后的描述符位置：

- `Goal.gzoffset64` 与 `Goal.gzoffset`（`OffsetContract`，`Spec/Public/GzControl.lean`）。旧陈述：对每个可达且满足 `GzValid` 的句柄、每个满足 `FileSystem fs` 的世界，调用返回，堆不变，世界只有 `errno` 改变（`{ fs' with errno := fs.errno } = fs`），结果为描述符位置减去读取者已缓冲的输入（描述符无效时为 -1）。新陈述：相同，但增加前提 `RegularOs fs`，且世界只有 `errno` 与调用计数改变（`{ fs' with errno := fs.errno, nos := fs.nos } = fs`）。
- `Goal.gzrewind`。旧陈述：对每个可达且满足 `GzValid` 的句柄，调用返回 -1 且堆不变，或返回 0、状态被重置且描述符位于保存的起点；写入者或严重错误返回 -1 且世界不变。新陈述：相同，但增加前提 `RegularOs fs`。

原因。每次预言调用都使调用计数 `nos` 前进，因此偏移契约旧的世界子句对每个句柄都为假（由 `fsLseek` 的定义）。预言的 `lseek` 返回与描述符无关的值，因此结果值子句只在之后每次调用都是普通调用时成立：`RegularOs fs`（`Spec/Public/GzState.lean`）。经检查的反例：[回归](../../tests/verification/regressions/gz-offset-regular-world.lean)。在一个 `FileSystem` 接受、其 `lseek` 返回 77 而不移动的世界中，`gzdopen(3, "r")` 记录起点 77；随后 `gzoffset64` 与 `gzoffset` 返回 77 而描述符位于 0，`gzrewind` 返回 0 而描述符仍位于 0。三条旧陈述为假，去掉 `RegularOs` 的修正后偏移契约也为假。这是模型变更，不是 zlib 问题。

这三个目标现在是普通文件实例上的功能契约。它们在每个世界（每个预言）上的安全属于 `Goal.gz_sequence_safety`（`GzSafety.lean`），已在分支 `skeleton/gz` 上证明。其调用分派（`gz.skeleton.lean` 中的 `operation_safe`）经由 `gzoffset64_step`、`gzoffset_step` 和 `gzrewind_step` 把 `gzoffset64`、`gzoffset` 与 `gzrewind` 作为下一次调用。每个都是对每个 `fs` 的 `GzCallSafe`，无 `RegularOs`，也无读取额度：不出错，有结果，打开的描述符保持，`GzInv` 保持，只改变句柄自己的块。这三个步骤引理在骨架上尚未完成，`gzrewind_step` 还依赖 R-3 的本地补丁。在它们被检查之前，这些调用在非普通世界上的安全尚未证明。它们不能直接复用已登记的证明，因为那些证明现在假设 `RegularOs`。

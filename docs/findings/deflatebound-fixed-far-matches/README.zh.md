<!-- source-sha256: 48bfbbf3047d9e4690ad90592568d896beba1a7bf94b002b9c67aef17ce9abe4 -->
# 级别 1 到 3 下，Z_FIXED 的 deflateBound 偏小

状态：已在本地打补丁。本地补丁 0006（`patches/0006-deflatebound-fixed-conservative.patch`）没有提交上游。在不带该补丁的真实 C 上已复现（上游 `develop` 757f052；补丁 0001 到 0005 不涉及 `deflate.c` 和 `trees.c`），带和不带 AddressSanitizer 与 UndefinedBehaviorSanitizer 都复现，在系统自带的 zlib 1.2.12 上也复现。尚未向上游报告；上游是否已经知道，尚未向上游核实。这是接口承诺不成立，不是内存错误：sanitizer 没有任何报告。

zlib.h 关于 `deflateBound` 写道：“`If that first deflate() call is provided the sourceLen input bytes, an output buffer allocated to the size returned by deflateBound(), and the flush value Z_FINISH, then deflate() is guaranteed to return Z_STREAM_END.`”（如果第一次 deflate() 调用得到全部 sourceLen 个输入字节、一个大小为 deflateBound() 返回值的输出缓冲区，以及刷新值 Z_FINISH，那么 deflate() 保证返回 Z_STREAM_END。）

`windowBits` 为 15、`memLevel` 为 8 时，`deflateBound` 返回紧的界 `n + (n >> 12) + (n >> 14) + (n >> 25) + 7 + wraplen`。这个界依赖于每个块都能退回成存储块：每个至多 16383 个符号的块大约多 5 个字节。有两个事实使它不成立：

1. `block_start` 为负时，也就是块内发生过一次窗口滑动时，`FLUSH_BLOCK_ONLY` 传给 `_tr_flush_block` 的是 `buf = NULL`。这时无法生成存储块。
2. `deflate_fast`（级别 1 到 3）接受任意距离上长度为 3 的匹配（只有 `deflate_slow` 有 `TOO_FAR` 判断）。使用固定码时，距离大于 16384 的长度 3 匹配要 7 + 5 + 13 = 25 位，多于它所代表的 24 位。`Z_FIXED` 强制使用固定码。

由距离在 (16384, 32000] 内的 3 字节复制构成的输入，会产生由 16383 个这样的匹配组成的块，每块约 49 KB。它们跨过一次滑动，无法退回成存储块，体积增加 1/24。

复现：`repro.c`（不用时钟，不读输入）。在不带补丁 0006 的 C 源码上带 sanitizer 运行的输出见 `report.txt`。n = 1,000,000 时界为 1,000,318；级别 1、2、3 下，按这个大小给出输出空间的一次 `deflate(Z_FINISH)` 返回 `Z_OK`，而流需要 1,007,343、1,008,565 和 1,008,570 个字节。级别 4 到 9 能结束。

旧版本失败的范围更大。在系统自带的 zlib 1.2.12 上，同一输入在级别 1 到 9 全部失败（n = 1,000,000 时流最多需要 1,031,475 个字节）。那时 `Z_FIXED` 即使在存储块更小时也强制使用固定块。上游提交 7fabcb5（“`Fix bug in block type selection when Z_FIXED used`”，zlib 1.2.13）让更小的存储块重新胜出。剩下的只有无法退回存储块的块（`buf == NULL`），而只有 `deflate_fast` 会采用远距离的 3 字节匹配。到 1.3.2.1 为止，`ChangeLog` 中没有条目处理这种情况（已检查每个涉及 `deflateBound` 和 `Z_FIXED` 的条目）；网络搜索没有找到上游的问题报告。上游是否已经知道，尚未向上游核实。

范围，来自一次定向搜索（`tests/goals/deflate-bound`，覆盖 `windowBits` 9 到 15、`memLevel` 1 到 9、级别 1 到 9、默认策略与 `Z_FIXED`、复制长度 3 到 5、字面量比例 0 到 50%）：只有 `windowBits` 15 且 `memLevel` 8（紧的界）、`Z_FIXED`、级别 1 到 3。其他参数组合使用保守的界，允许每字节 9 位。默认策略在这些测试中不受影响：动态码会给远距离的 3 字节匹配分配短码。`compress`、`compress2` 和 `compressBound` 使用默认策略，不受影响。

## 修复：补丁 0006

修复是本地补丁，而不是定理的前提。`deflateBound_z` 在策略为 `Z_FIXED` 时也使用保守的界：级别 1 到 9 用 `fixedlen`，级别 0 用 `storelen`，与其他参数组合相同。固定码每字节至多 9 位，`fixedlen` 能覆盖。其他策略和其他参数组合都不变。

打补丁后的测量（C 源码加补丁 0001 到 0006）：

- `repro.c`，n = 1,000,000：界为 1,130,869；按这个大小给出输出空间的一次 `deflate(Z_FINISH)` 在级别 1 到 9 全部返回 `Z_STREAM_END`，带和不带 sanitizer 都是如此。流的大小不变（级别 1 到 3 为 1,007,343 到 1,008,570）。
- 远距离匹配搜索，即 `tests/goals/deflate-bound/bound.c` 的 `far` 模式：复制长度 3 到 5，字面量比例 0、10、25 和 50%，每个 `windowBits` 9 到 15、`memLevel` 1 到 9、级别 1 到 9 和每种策略，n = 200,000。不带补丁 0006 时有 6 种情形失败，全部是 `windowBits` 15、`memLevel` 8、`Z_FIXED`、级别 1 到 3、复制长度 3、字面量比例 0 和 10%。带补丁时没有失败。在 sanitizer 下（`windowBits` 15，n = 150,000）没有失败，sanitizer 也没有任何报告。
- 带补丁时 `tests/goals/deflate-bound/run.sh` 通过；它也运行远距离匹配搜索。

对证明的影响：带补丁后，`DeflateCompletes` 在这种情况下不需要前提。`deflateBound_z` 的翻译和数值规范（`deflateBoundValue`、`Api.DeflState.bound`）都跟随打补丁后的 C。

<!-- source-sha256: dbd489e6abcd9df663d6b3b67f65e6836d3112aafc0ed079797fd194c1f5ce2c -->
# 级别 1 到 3 下，Z_FIXED 的 deflateBound 偏小

状态：已在固定的 C 源码上复现（上游 `develop` 757f052，未打补丁；本地补丁不涉及 `deflate.c` 和 `trees.c`），带和不带 AddressSanitizer 与 UndefinedBehaviorSanitizer 都复现，在系统自带的 zlib 1.2.12 上也复现。尚未向上游报告；上游是否已知，**尚未由证明确认**。这是接口承诺不成立，不是内存错误：sanitizer 没有任何报告。

zlib.h 对 `deflateBound` 的承诺是：如果第一次 `deflate()` 调用得到全部 `sourceLen` 个输入字节、一个大小为 `deflateBound()` 返回值的输出缓冲区，以及 flush 值 `Z_FINISH`，那么 `deflate()` 保证返回 `Z_STREAM_END`。

`windowBits` 为 15、`memLevel` 为 8 时，`deflateBound` 返回紧的界 `n + (n >> 12) + (n >> 14) + (n >> 25) + 7 + wraplen`。这个界依赖于每个块都能退回成存储块：每个至多 16383 个符号的块大约多 5 个字节。有两个事实使它不成立：

1. `block_start` 为负时，也就是块内发生过一次窗口滑动时，`FLUSH_BLOCK_ONLY` 传给 `_tr_flush_block` 的是 `buf = NULL`。这时无法生成存储块。
2. `deflate_fast`（级别 1 到 3）接受任意距离上长度为 3 的匹配（只有 `deflate_slow` 有 `TOO_FAR` 判断）。使用固定码时，距离大于 16384 的长度 3 匹配要 7 + 5 + 13 = 25 位，多于它所代表的 24 位。`Z_FIXED` 强制使用固定码。

由距离在 (16384, 32000] 内的 3 字节复制构成的输入，会产生由 16383 个这样的匹配组成的块，每块约 49 KB。它们跨过一次滑动，无法退回成存储块，体积增加 1/24。

复现：`repro.c`（不用时钟，不读输入）。在固定的 C 源码上带 sanitizer 运行的输出见 `report.txt`。n = 1,000,000 时界为 1,000,318；级别 1、2、3 下，按这个大小给出输出空间的一次 `deflate(Z_FINISH)` 返回 `Z_OK`，而流需要 1,007,343、1,008,565 和 1,008,570 个字节。级别 4 到 9 能结束。

范围，来自陈述测试（`tests/goals/deflate-bound`，对 `windowBits` 9 到 15、`memLevel` 1 到 9、级别 1 到 9、默认策略与 `Z_FIXED`、复制长度 3 到 5、字面量比例 0 到 50% 的定向搜索）：只有 `windowBits` 15 且 `memLevel` 8（紧的界）、`Z_FIXED`、级别 1 到 3。其他参数组合使用保守的界，允许每字节 9 位。默认策略在这些测试中不受影响：动态码会给远距离的 3 字节匹配分配短码。`compress`、`compress2` 和 `compressBound` 使用默认策略，不受影响。

对证明的影响：`DeflateCompletes`（`ZlibF/Spec/Functional/Sequences.lean`）对每一种策略量化，所以按现在的陈述，它在这种情况下不成立。更正需要一个决定：加一个前提，排除使用紧的界时级别 1 到 3 的 `Z_FIXED`（列入 `docs/deviations.md`），或者打本地补丁。`deflateBound` 中最小的修复是对 `Z_FIXED` 使用保守的界（固定码每字节至多 9 位，`fixedlen` 界能覆盖）。

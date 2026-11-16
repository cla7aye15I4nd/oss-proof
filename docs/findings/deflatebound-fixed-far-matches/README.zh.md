<!-- source-sha256: 1ed935c74356588dbf5df933ee23a81ebcc93e733e06a933ff571a2e70b64d7e -->
# `Z_FIXED` 在级别 1 到 3 时 `deflateBound` 太小

`windowBits` 为 15、`memLevel` 为 8、策略为 `Z_FIXED`、级别为 1、2 或 3 时，不打补丁的 `deflateBound` 返回的界比 `deflate` 产生的流小。于是用这么多空间做一次 `deflate(Z_FINISH)` 调用会返回 `Z_OK`，违背了 `zlib.h` 的承诺。这是失信，不是内存错误：没有任何行为是未定义的，sanitizer 也没有任何报告。

`zlib.h` 对 `deflateBound` 的说明：`If that first deflate() call is provided the sourceLen input bytes, an output buffer allocated to the size returned by deflateBound(), and the flush value Z_FINISH, then deflate() is guaranteed to return Z_STREAM_END.`（如果第一次 deflate() 调用拿到 sourceLen 个输入字节、大小为 deflateBound() 返回值的输出缓冲区以及刷新值 Z_FINISH，那么 deflate() 保证返回 Z_STREAM_END。）

`windowBits` 为 15 且 `memLevel` 为 8 时，`deflateBound` 返回紧的界 `n + (n >> 12) + (n >> 14) + (n >> 25) + 7 + wraplen`。这个界指望每个块都能退回到存储块：每个最多 16383 个符号的块大约 5 字节。有两个事实打破了它：

1. 当 `block_start` 为负，也就是块内发生过窗口滑动时，`FLUSH_BLOCK_ONLY` 向 `_tr_flush_block` 传入 `buf = NULL`。这时不可能使用存储块。
2. `deflate_fast`（级别 1 到 3）接受任意距离上长度为 3 的匹配（只有 `deflate_slow` 有 `TOO_FAR` 检查）。用固定码时，距离大于 16384 的长度为 3 的匹配要花 7 + 5 + 13 = 25 位，多于它那三个字节的 24 位。`Z_FIXED` 强制使用固定码。

由距离在 (16384, 32000] 内的 3 字节复制构成的输入，会产生含 16383 个这种匹配的块，每块约 49 KB。它们跨越一次滑动，没有存储块可退，并且膨胀 1/24。

## 到达它的调用

```c
deflateInit2(&s, level, Z_DEFLATED, 15, 8, Z_FIXED);   /* 级别 1、2 或 3 */
bound = deflateBound(&s, n);
s.next_in = in;   s.avail_in = n;                      /* 来自远距离的 3 字节复制 */
s.next_out = out; s.avail_out = bound;
deflate(&s, Z_FINISH);                                 /* 返回 Z_OK，而不是 Z_STREAM_END */
```

只有 `windowBits` 15 配 `memLevel` 8（紧的界）、`Z_FIXED`、级别 1 到 3 受影响。其他参数组合使用保守的界，它们允许每字节 9 位。使用默认策略时，动态码会给远距离的 3 字节匹配分配短码。`compress`、`compress2` 和 `compressBound` 使用默认策略，不受影响。

## 证据

复现程序 [`repro.c`](repro.c)，在不带补丁 0006 的 C 上，分别在启用和不启用 AddressSanitizer 与 UndefinedBehaviorSanitizer 的情况下运行。摘自 [`report.txt`](report.txt)，n = 1,000,000：

```
level 1: deflateBound 1000318, deflate(Z_FINISH) with that room returns 0 (not Z_STREAM_END), stream needs 1007343
level 2: deflateBound 1000318, deflate(Z_FINISH) with that room returns 0 (not Z_STREAM_END), stream needs 1008565
level 3: deflateBound 1000318, deflate(Z_FINISH) with that room returns 0 (not Z_STREAM_END), stream needs 1008570
```

级别 4 到 9 以 `Z_STREAM_END` 结束。

范围来自在真实 C 上的一次搜索（`tests/goals/deflate-bound`），它遍历 `windowBits` 9 到 15、`memLevel` 1 到 9、级别 1 到 9、默认策略和 `Z_FIXED`、复制长度 3 到 5 以及字面量比例 0 到 50%。不带补丁 0006 时，它只在 `windowBits` 15、`memLevel` 8、`Z_FIXED`、级别 1 到 3、复制长度 3 的情形失败。带补丁时没有任何情形失败。

## 修复

[补丁 0006](../../../patches/README.md)：在 `deflateBound_z` 中，策略为 `Z_FIXED` 时也使用保守的界：级别 1 到 9 用 `fixedlen`，级别 0 用 `storelen`，与其他参数组合相同。固定码每字节最多花 9 位，`fixedlen` 覆盖了它。其他策略和其他参数组合都不变。

带补丁时，对 n = 1,000,000，界是 1,130,869，用这么多空间做一次 `deflate(Z_FINISH)` 在级别 1 到 9 都返回 `Z_STREAM_END`，无论是否启用 sanitizer。流的大小不变。

上游：该补丁是本地补丁，没有提交。

## 与证明的关系

没有安全目标依赖这个界的值。`deflateBound_z` 的翻译和它的值的规格遵循打过补丁的 C。没有这个补丁时，“对每一种策略，带 `Z_FINISH` 且有 `deflateBound` 个字节空间的 `deflate` 都会结束流”这一命题（`DeflateCompletes`）不成立。

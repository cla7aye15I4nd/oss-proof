<!-- source-sha256: 084df5b9e8a57838f5dd8984aaed22d19f408eff3f6275bf495008f03331aef6 -->
# 补丁

这些证明针对的是固定版本的 zlib 源码（上游 `develop` 的提交 `99623ef7`，zlib 1.4），加上本目录中按文件名顺序应用的六个补丁。本页说明每个补丁改了什么、为什么改，以及它在上游处于什么状态。

每个补丁修复 zlib 的一个问题：不修复它，某个安全命题就无法证明，或者 `zlib.h` 的某项承诺不成立。每个补丁都只做修复所需的最小改动。已提交上游的补丁与所提交的修复一致。标为**本地**的补丁尚未提交上游。上游分支包含了相应修复之后，补丁就不再需要。

| 补丁 | 修复什么 | 上游状态（截至 2026-11-15） |
| --- | --- | --- |
| 0001 | [`inflateCopy` 中对无关指针的关系比较](../docs/findings/inflate-copy-fixed/README.md) | 已提交：[拉取请求 #1369](https://github.com/madler/zlib/pull/1369)。维护者于 2026-11-06 答复“Applied”；修复尚未出现在 `develop` 上 |
| 0002 | [开头调用 `gzungetc` 之后 `gzseek64` 中的有符号溢出](../docs/findings/gzseek-pushback-overflow/README.md) | 已提交：[拉取请求 #1361](https://github.com/madler/zlib/pull/1361)，仍处于打开状态 |
| 0003 | [透明模式下部分读取后失败时过时的 `x.next`](../docs/findings/gzread-transparent-stale-next/README.md) | 已提交：[拉取请求 #1363](https://github.com/madler/zlib/pull/1363)，仍处于打开状态 |
| 0004 | gz 位置 `x.pos` 的有符号溢出，[读取](../docs/findings/gzread-pos-overflow/README.md)和[写入](../docs/findings/gzwrite-pos-overflow/README.md) | 本地：尚未提交 |
| 0005 | 对[未写入](../docs/findings/gz-reset-next-uninitialised/README.md)或[悬空](../docs/findings/gz-next-dangling-after-direct-read/README.md)的 `x.next` 的零前进 | 本地：尚未提交 |
| 0006 | [`Z_FIXED` 在级别 1 到 3 时 `deflateBound` 偏小](../docs/findings/deflatebound-fixed-far-matches/README.md) | 本地：尚未提交 |

每个链接的页面给出调用序列、运行命令、sanitizer 的判定、范围和修复。[发现](../docs/findings.md)把它们列在一张表里。补丁 0001 至 0004 修复的是 sanitizer 在真实 C 上报告的问题。补丁 0005 修复的行为仅按 C 标准的字面规定未定义。补丁 0006 修复的是 `zlib.h` 的一项没有兑现的承诺，不是未定义行为。

## 0001-inflate-copy-pointer-equality.patch

`inflateCopy` 不再对静态固定码表与状态内部码数组中的指针做关系比较。[复现材料](../docs/findings/inflate-copy-fixed/README.md)诊断了未打补丁的 C。没有这个补丁，就无法对每个流证明 `inflateCopy` 的安全性。

补丁与[上游拉取请求 #1369](https://github.com/madler/zlib/pull/1369) 中的提交 `300fea14353d2e2ca61210aca7c48861ded5788c` 完全一致。维护者于 2026 年 11 月 6 日答复“Applied”，该拉取请求已关闭。2026-11-15 时，公开可获取的 `develop` 和 `master` 分支的最新提交为 `99623ef7097352da7993ba614161fd6a311e046e`（“zlib 1.4”），也就是固定的提交。其中的 `inflate.c` 仍保留旧的指针比较，因此这个补丁仍然需要。

## 0002-gzseek-negative-position-overflow.patch

避免在开头调用 `gzungetc`（它把 `state->x.pos` 设为 -1）之后，`gzseek64` 中的有符号溢出：`SEEK_CUR` 的范围检查在 `pos` 为负时计算 `GZ_OFF_MAX - pos`，而接近 `GZ_OFF_MAX` 的 `SEEK_SET` 目标在 `pos - state->x.pos` 中溢出。UndefinedBehaviorSanitizer 在未打补丁的 C 上报告这两处。没有这个补丁，就无法证明 `gzseek64` 和 `gzseek` 的安全性。

补丁是[上游拉取请求 #1361](https://github.com/madler/zlib/pull/1361) 在其最新提交 `ce2248ee9750` 处 `gzlib.c` 的部分。该拉取请求中 `test/example.c` 的部分不属于被验证的源码。该拉取请求仍处于打开状态。[发现](../docs/findings/gzseek-pushback-overflow/README.md)给出复现：它在 sanitizer 下构建未打补丁的 C，并表明打补丁后报告消失。

## 0003-gzread-partial-copy-read-error.patch

在透明（`COPY`）模式下，于 `gz_load` 之前设置 `state->x.next = state->out`。如果 `read` 先提供一些字节后失败，`gz_load` 把部分计数留在 `x.have` 并返回 -1，而 `gz_fetch` 在给 `x.next` 赋值之前就返回了。随后读取函数通过过时的 `x.next` 消费这些字节：当先前的输出缓冲区已用完时，这是越界读。没有这个补丁，就无法证明 gz 读取调用的安全性。

补丁与[上游拉取请求 #1363](https://github.com/madler/zlib/pull/1363) 在其最新提交 `37627fd3bb47` 处的改动完全一致。该拉取请求仍处于打开状态。[发现](../docs/findings/gzread-transparent-stale-next/README.md)给出复现：它在 sanitizer 下构建未打补丁的 C，并表明打补丁后报告消失。

## 0004-gz-position-overflow.patch

本地：尚未提交上游。

使未压缩位置 `state->x.pos` 始终能用 `z_off64_t` 表示。读取：`gz_fetch` 只向输出缓冲区填入位置可表示的字节（至少一个，以便仍能发现输入结束），`gz_read` 和 `gzgets` 不交付超过 `GZ_OFF_MAX` 的字节；超出部分的数据给出 `Z_DATA_ERROR` "position overflow"。`gz_look` 的透明 COPY 分支也只缓冲剩余的空间，输入超出时记录同样的错误，因此每个读取调用返回时都有 `x.pos + x.have <= GZ_OFF_MAX`，这是 `gzgetc()` 宏所需要的（[gz-position-copy-overflow](../docs/findings/gz-position-copy-overflow.md)）。写入：`gz_write`、`gzputc` 的快速路径和 `gzprintf` 拒绝会使位置超过 `GZ_OFF_MAX` 的写入，给出同样的错误。发现：[gzread-pos-overflow](../docs/findings/gzread-pos-overflow/README.md) 和 [gzwrite-pos-overflow](../docs/findings/gzwrite-pos-overflow/README.md)。证据：在 x86_64 Linux 上用 `/dev/zero` 和真实的 `/dev/null`，UndefinedBehaviorSanitizer 对两者都报告有符号溢出。COPY 分支的界限所覆盖的、透明探测之后的溢出，已在模型中确认，也已通过对 C 的解读确认；它没有在 sanitizer 下复现。没有这个补丁，就无法证明 gz 读写函数的安全性。提交上游用的拉取请求草稿在读取一侧的发现中。

## 0005-gz-next-zero-advance.patch

本地：尚未提交上游。

在 `gzseek64` 和 `gz_skip_have` 中，只有当前进量 `n` 不为零时才移动 `state->x.next`。当 `n == 0` 时，该字段可能从未被写入（`gz_reset` 不设置它），也可能指向调用者在一次直接 `gzread` 之后已释放的缓冲区；对这两种值做指针运算在 C 中都是未定义的。任何结果和状态都不变。发现：[gz-reset-next-uninitialised](../docs/findings/gz-reset-next-uninitialised/README.md) 和 [gz-next-dangling-after-direct-read](../docs/findings/gz-next-dangling-after-direct-read/README.md)。证据：按 C 标准的字面规定未定义；没有任何 sanitizer 报告它们。复现中的探针显示了对从未写入的值和悬空值的零前进，以及打补丁后它们消失。模型在对悬空指针做运算时产生故障，证明又要求指针字段先写后读，所以没有这个补丁就无法证明 gz 读取调用是安全的。提交上游用的拉取请求草稿在关于未写入字段的那项发现中。

## 0006-deflatebound-fixed-conservative.patch

本地：尚未提交上游。

在 `deflateBound_z` 中，策略为 `Z_FIXED` 时也返回保守的上界之一，而不只是在 `windowBits` 或 `memLevel` 不是默认值时。较紧的默认上界假定每个块都能退回为存储块。跨过一次窗口滑动的块没有这条退路（`FLUSH_BLOCK_ONLY` 传入 `buf = NULL`），而 `deflate_fast`（级别 1 到 3）接受任意距离上的 3 字节匹配，用固定码时这样的匹配要 25 位。于是在 `Z_FIXED` 下输出会超过上界，给出这么多空间的一次 `deflate(Z_FINISH)` 调用返回 `Z_OK`，违背 `zlib.h` 的承诺。此时适用的保守上界（级别 1 到 9 用 `fixedlen`，级别 0 用 `storelen`，与其他参数组合相同）允许每字节 9 位。其他策略和其他参数组合都不变。发现：[deflatebound-fixed-far-matches](../docs/findings/deflatebound-fixed-far-matches/README.md)。证据：复现程序在未打补丁的 C 上于级别 1 到 3 返回 `Z_OK`，打补丁后在每个级别都返回 `Z_STREAM_END`，开启和不开启 AddressSanitizer 与 UndefinedBehaviorSanitizer 都是如此；对含远距离匹配的输入所做的搜索在打补丁后没有发现失败。这是一项没有兑现的 API 承诺，不是内存错误。没有这个补丁，两个对每种策略量化的命题不成立：往返的完备性命题（`DeflateCompletes`）和 `deflateBound` 的承诺。

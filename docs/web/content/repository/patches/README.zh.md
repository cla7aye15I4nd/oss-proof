<!-- source-sha256: b1ff10340f28e46079af96baf8f715207a275331b66e89fd2032dcf1f390c42e -->
# 补丁

被验证的源码是 zlib 1.4（上游提交 `99623ef7`），加上本目录中按文件名顺序应用的六个补丁。每条定理说的都是这份打过补丁的源码。

每个补丁修复 zlib 的一个问题：不修复它，某个安全命题就无法证明，或者 `zlib.h` 的某项承诺不成立。每个补丁都只做修复所需的最小改动。已提交上游的补丁就是所提交的修复。[发现](../docs/findings.md)把这些问题列在一张表里，每个链接的页面给出到达该问题的调用和复现。

## 0001-inflate-copy-pointer-equality.patch

`inflateCopy` 用 `>=` 和 `<=` 比较一个指向静态固定码表的指针和一个指向状态自己的码数组的指针，而 C 只对指向同一对象的指针定义这两个运算符（[发现](../docs/findings/inflate-copy-fixed/README.md)）。补丁改用指针相等来判断同一条件。没有这个补丁，就无法对每个流证明 `inflateCopy` 的安全性。

上游：该补丁就是[拉取请求 #1369](https://github.com/madler/zlib/pull/1369) 的提交，维护者答复“Applied”。zlib 1.4 中没有它。

## 0002-gzseek-negative-position-overflow.patch

开头的 `gzungetc` 把 `state->x.pos` 设为 -1。之后 `gzseek64` 使有符号运算溢出：`SEEK_CUR` 的范围检查以负的 `pos` 计算 `GZ_OFF_MAX - pos`，而接近 `GZ_OFF_MAX` 的 `SEEK_SET` 目标在 `pos - state->x.pos` 中溢出（[发现](../docs/findings/gzseek-pushback-overflow/README.md)）。补丁只对正的 `pos` 计算范围检查，并拒绝位移放不下的定位。没有这个补丁，就无法证明 `gzseek64` 和 `gzseek` 的安全性。

上游：该补丁是[拉取请求 #1361](https://github.com/madler/zlib/pull/1361) 中 `gzlib.c` 的部分，该拉取请求仍处于打开状态。

## 0003-gzread-partial-copy-read-error.patch

在透明（`COPY`）模式下，如果 `read` 先给出一些字节然后失败，`gz_load` 把部分字节数留在 `x.have` 中并返回 -1，而 `gz_fetch` 在给 `x.next` 赋值之前就返回。读取函数随后通过过时的 `x.next` 取用这部分字节，而它可能在输出缓冲区之外（[发现](../docs/findings/gzread-transparent-stale-next/README.md)）。补丁在 `gz_load` 之前设置 `state->x.next = state->out`。没有这个补丁，就无法证明 gz 读取调用的安全性。

上游：该补丁就是[拉取请求 #1363](https://github.com/madler/zlib/pull/1363) 的改动，该拉取请求仍处于打开状态。

## 0004-gz-position-overflow.patch

gz 读取函数和写入函数把字节数加到有符号位置 `state->x.pos` 上，没有上界，所以在接近 `GZ_OFF_MAX` 的位置上读或写会使它溢出（发现：[读取](../docs/findings/gzread-pos-overflow/README.md)、[写入](../docs/findings/gzwrite-pos-overflow/README.md)）。补丁使位置始终能用 `z_off64_t` 表示。读取：`gz_fetch` 只向输出缓冲区填入位置可表示的字节（至少一个，以便发现输入的结束），`gz_read` 和 `gzgets` 不交付超过 `GZ_OFF_MAX` 的字节；超出的数据给出 `Z_DATA_ERROR`（消息为 `position overflow`）。写入：`gz_write`、`gzputc` 的快速路径和 `gzprintf` 拒绝会使位置超过 `GZ_OFF_MAX` 的写入，并给出同样的错误。没有这个补丁，就无法证明 gz 读取函数和写入函数的安全性。

补丁也给 `gz_look` 的透明分支加了界。`zlib.h` 的 `gzgetc()` 宏对任何已缓冲的字节执行 `pos++`，不做检查，所以每个读取调用返回时都必须有 `x.pos + x.have <= GZ_OFF_MAX`。`gz_look` 的透明分支也缓冲输入，所以它只缓冲剩余的空间，超出时记录同样的错误。

上游：本地补丁，没有提交。

## 0005-gz-next-zero-advance.patch

`gzseek64` 和 `gz_skip_have` 在 `n` 为零时也执行 `state->x.next += n`。这时该字段可能从未被写入（`gz_reset` 不设置它），也可能指向一个在直接 `gzread` 之后已被释放的调用者缓冲区；对这两种指针做运算在 C 中都是未定义的（发现：[未写入](../docs/findings/gz-reset-next-uninitialised/README.md)、[悬空](../docs/findings/gz-next-dangling-after-direct-read/README.md)）。补丁只有当 `n` 不为零时才推进 `x.next`。结果和状态都不变。模型对悬空指针的运算报告故障，所以没有这个补丁，就无法证明 gz 读取调用是安全的。模型看不到从未写入的情形：在模型中，新分配的内存里的指针字段是 `NULL`，而 `NULL + 0` 通过。那种情形依靠的是对 C 的解读和探针运行。

上游：本地补丁，没有提交。

## 0006-deflatebound-fixed-conservative.patch

`windowBits` 为 15、`memLevel` 为 8、策略为 `Z_FIXED` 时，`deflateBound` 返回紧的默认界，而这个界指望每个块都能退回到存储块。跨越窗口滑动的块没有这条退路，而 `deflate_fast`（级别 1 到 3）接受任意距离上的 3 字节匹配，它们用固定码要花 25 位。于是输出超过这个界，用这么多空间做一次 `deflate(Z_FINISH)` 调用返回 `Z_OK`，违背了 `zlib.h` 的承诺（[发现](../docs/findings/deflatebound-fixed-far-matches/README.md)）。补丁使 `deflateBound_z` 在策略为 `Z_FIXED` 时也返回保守的界（级别 1 到 9 用 `fixedlen`，级别 0 用 `storelen`，与其他参数组合相同），它允许每字节 9 位。其他策略和其他参数组合都不变。它修复的是失信，不是内存错误：没有安全目标依赖这个界的值。

上游：本地补丁，没有提交。

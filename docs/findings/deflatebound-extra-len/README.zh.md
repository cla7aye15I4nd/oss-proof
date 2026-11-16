<!-- source-sha256: 2d2a03b30be77f449168e6b9f0da0bd46c6967b682d18f97190841f4aaeb8f04 -->
# gzip extra 字段长度为 2^32 - 2 或 2^32 - 1 时的 deflateBound

状态：已在真实的 C 上复现，源码是上游 `develop` 的提交 `757f0527154291bcf6bfbd6396ecde6bedd2db95`。`deflate.c` 在该提交与 zlib 1.4（提交 `99623ef7097352da7993ba614161fd6a311e046e`，即本项目验证的版本）之间只有版权字符串不同；这里没有记录在该版本上的运行。本仓库的补丁都不改变下面说的这个和。上游已知（[上游拉取请求 1360 中的讨论](https://github.com/madler/zlib/pull/1360)）。

`deflateBound` 把 `2 + s->gzhead->extra_len` 加到封装长度上。`extra_len` 的类型是 `uInt`，所以这个和按 32 位计算，`extra_len` 为 2^32 - 2 和 2^32 - 1 时回绕成 0 或 1。`deflate` 写出该字段的 `extra_len & 0xffff` 个字节（65534 或 65535）。于是这个界大约少了 64 KiB，按这个大小给出输出空间的一次 `deflate(Z_FINISH)` 返回 `Z_OK`（`tests/goals/deflate-bound/bound.c`，模式 `extra`：输入 100 字节时界为 125 和 126）。那次运行的输出没有保留；`tests/goals/deflate-bound/run.sh` 只有在它尝试的五个长度中恰好两个失败时才通过。

`extra_len` 从 2^16 到 2^32 - 3 时，界按 `extra_len` 个字节计，而 `deflate` 写出的更少：这个界是保守的，不是错的。

对命题的影响：

- 安全性不受影响。这里涉及的是界的值，安全目标 `Goal.deflateBound_safety` 和 `Goal.deflateBound_z_safety` 用不到它。
- 关于这个值的规格跟随 C。数值目标 `Goal.deflateBound` 和 `Goal.deflateBound_z` 使用的 `WrapperLength` 按 32 位计算 `2 + extra_len`，翻译也以同样的方式回绕。在这一点上规格与翻译一致。这两个数值目标不在计划内，未完成。
- 回绕破坏的是 zlib.h 的承诺：大小为 `deflateBound` 字节的缓冲区足够一次 `deflate(Z_FINISH)` 使用。若一个命题对 C 断言这一承诺，并且流的头部由 `deflateSetHeader` 设置，它就需要一个排除这两个长度的前提。

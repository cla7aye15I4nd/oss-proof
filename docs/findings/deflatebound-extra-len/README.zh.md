<!-- source-sha256: 50bb2f9a481098a6e685058ad2e531f397ee55ae79ea0045e62381e0455efc26 -->
# gzip extra 字段长度为 2^32 - 2 或 2^32 - 1 时的 deflateBound

状态：已在固定的 C 源码上复现。上游已知（上游拉取请求 1360 中的讨论）。

`deflateBound` 把 `2 + s->gzhead->extra_len` 加到封装长度上。`extra_len` 的类型是 `uInt`，所以这个和按 32 位计算，`extra_len` 为 2^32 - 2 和 2^32 - 1 时回绕成 0 或 1。`deflate` 写出该字段的 `extra_len & 0xffff` 个字节（65534 或 65535）。于是这个界大约少了 64 KiB，按这个大小给出输出空间的一次 `deflate(Z_FINISH)` 返回 `Z_OK`（`tests/goals/deflate-bound/bound.c`，模式 `extra`：输入 100 字节时界为 125 和 126）。

`extra_len` 从 2^16 到 2^32 - 3 时，界按 `extra_len` 个字节计，而 `deflate` 写出的更少：这个界是保守的，不是错的。

对命题的影响：`Goal.deflateBound` 和 `Goal.deflateBound_z` 使用的 `WrapperLength`（`ZlibF/Spec/Public/Streams.lean`）写的是不回绕的 `2 + gh.extra_len.toNat`，所以这两个数值目标对这两个长度不成立；翻译和 C 一样会回绕。包含 `deflateSetHeader` 的承诺目标需要一个排除这两个长度的前提。

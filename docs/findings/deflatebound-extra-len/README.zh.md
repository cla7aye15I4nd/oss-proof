<!-- source-sha256: 4005278c90e8e722b72942dad086928310f16aa1dc88b6f521d7585e5a099a01 -->
# gzip extra 字段长度为 2^32 - 2 或 2^32 - 1 时的 deflateBound

状态：已在真实的 C 上复现。上游已知（上游拉取请求 1360 中的讨论）。

`deflateBound` 把 `2 + s->gzhead->extra_len` 加到封装长度上。`extra_len` 的类型是 `uInt`，所以这个和按 32 位计算，`extra_len` 为 2^32 - 2 和 2^32 - 1 时回绕成 0 或 1。`deflate` 写出该字段的 `extra_len & 0xffff` 个字节（65534 或 65535）。于是这个界大约少了 64 KiB，按这个大小给出输出空间的一次 `deflate(Z_FINISH)` 返回 `Z_OK`（`tests/goals/deflate-bound/bound.c`，模式 `extra`：输入 100 字节时界为 125 和 126）。

`extra_len` 从 2^16 到 2^32 - 3 时，界按 `extra_len` 个字节计，而 `deflate` 写出的更少：这个界是保守的，不是错的。

对命题的影响：规格跟随 C。数值目标 `Goal.deflateBound` 和 `Goal.deflateBound_z` 使用的 `WrapperLength` 按 32 位计算 `2 + extra_len`，翻译也以同样的方式回绕。若一个命题断言，对头部由 `deflateSetHeader` 设置的流，这个界足够，它就需要一个排除这两个长度的前提。

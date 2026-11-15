<!-- source-sha256: 0885a7dc3015ce643360df5c61e1711338c64654f0fafa059238d710f2ae3d92 -->
# gz：在 `GZ_OFF_MAX` 附近经透明探测后位置溢出

这是本项目本地[补丁 0004](../../patches/README.md) 第一版的缺陷，不是上游 zlib 的又一个缺陷。补丁 0004 修复的是 [gzread-pos-overflow](gzread-pos-overflow/README.md)；它的第一版（2026-11-12）留下一条路径，读取者在这条路径上仍可能让位置溢出。第二版（2026-11-13）把它补上了。

状态：已在模型中确认，也已通过阅读 C 确认。没有在 sanitizer 下复现：这段历史需要约 2^63 个解码字节。仓库中的补丁已覆盖它：`gz_look` 的 COPY 分支只缓冲 `gz_room(state, avail_in)` 个字节，输入超出这个量时记录 `Z_DATA_ERROR`“position overflow”。该补丁是本地补丁，没有提交上游；项目所有者于 2026-11-13 批准了这一扩展。

## 当时出了什么问题

补丁 0004 让位置 `state->x.pos` 保持在 `z_off64_t` 范围内。`gz_fetch` 只载入 `GZ_OFF_MAX` 之前放得下的部分（`gz_room`）；`x.pos` 到达 `GZ_OFF_MAX` 时，`gz_read` 和 `gzgets` 丢弃缓冲的输出。读取者不变式在每次返回时还要求更多：`x.pos + x.have <= GZ_OFF_MAX`，因为 zlib.h 的 `gzgetc()` 宏对任何缓冲字节都执行 `(g)->pos++`。

在补丁的第一版中，`gz_look` 的透明 COPY 分支没有限制。它把全部待处理输入复制到输出缓冲区，并设置 `x.have = strm->avail_in`，至多 `size` 个字节，而不管 `x.pos` 是多少。`gz_read` 中的丢弃只在其循环的下一轮才执行。所以 `gz_read` 返回时可能有 `x.pos + x.have > GZ_OFF_MAX`。经由 `gz_skip`（`gz_skip_have` 只取 `min(have, skip)`）和 `gzdirect`（它调用 `gz_look` 后就返回）也是一样。

开始之后，`gz_look` 只在一种历史中走 COPY 分支：`tests/verification/regressions/gz-copy-direct.c` 在真实的 C 中展示了它。一个 gzip 成员之后跟着不是 gzip 的数据；`gz_decomp` 把它当作尾部垃圾（`junk == 1`）并设置 `eof`；`gzclearerr` 清除 `eof`；下一次读取进入 `gz_look`，此时 `direct == 0`、`junk == 1`，于是透明地复制随后的输入。如果该成员解码出将近 `GZ_OFF_MAX` 个字节，那么此处的 `x.pos` 就接近 `GZ_OFF_MAX`。

## 调用序列

在补丁 0004 的第一版下：

```c
/* 一个解码为 GZ_OFF_MAX - 3 字节的 gzip 成员，其后是非 gzip 字节 */
gzread(f, ...);            /* 把成员读到末尾：x.pos = GZ_OFF_MAX - 3 */
gzread(f, buf, 1);         /* 尾部垃圾：设置 eof，how = LOOK，junk = 1 */
gzclearerr(f);             /* 清除 eof */
gzread(f, buf, 3);         /* gz_look COPY：have = 8；复制 3 个；x.pos = GZ_OFF_MAX，have = 5 */
gzgetc(f);                 /* 宏：(g)->pos++ 溢出 */
```

在仓库中的补丁下，第四个调用缓冲三个字节，返回 3，`x.have = 0`，并记录 `Z_DATA_ERROR`；`gzgetc` 返回 -1。

## 证据

- 模型，扩展之前：从一个构造的读取者出发：`x.pos = GZ_OFF_MAX - 3`，`how = LOOK`，`direct = 0`，`junk = 1`，输入缓冲区 8 字节，文件中还剩 8 个字节 `'A'`。内核求值 `gzread(file, buf, 3)`，结果返回 3，且 `x.pos = GZ_OFF_MAX`、`x.have = 5`。起点满足读取者不变式中关于位置的子句，终点不满足。随后的 `gzgetc` 在 `x.pos + 1` 上以 `Fault.ub` 出错；它的缓冲路径与宏相同。这个状态是构造出来的，不是由公开调用历史到达的。
- 模型，扩展之后：`ZlibF/Proof/gz.position-copy-overflow-regression.lean`（在 `tests/verification/regressions/gz-position-copy-overflow.lean` 中重述）从同一状态检查修复后的运行：`gzread` 返回 3，`x.have = 0`，记录 `Z_DATA_ERROR`，关于位置的子句成立；随后的 `gzgetc` 返回 -1，没有故障。该文件的头部说明记录了早先的那次运行。
- C：在补丁 0004 的第一版下阅读 `gz_look`、`gz_fetch` 和 `gz_read`，得到与早先模型运行相同的轨迹。
- 没有运行 sanitizer：这段历史需要约 2^63 个解码字节。

## 范围与置信度

对以下两点置信度高：带补丁 0004 第一版的 C 允许这个状态；只要能读取那么长的 gzip 成员，上述历史就能到达它。范围：带该版本补丁的读取者，位置距 `GZ_OFF_MAX` 不到 `size` 个字节，且在一个带尾部数据的 gzip 成员和 `gzclearerr` 之后。没有补丁 0004 时，同一段历史在 `gz_read` 中就已经溢出（[gzread-pos-overflow](gzread-pos-overflow/README.md)）。

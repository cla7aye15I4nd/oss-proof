<!-- source-sha256: 9a3c0b7ae9b8968e949da464b6a7e6a1bfda828d14b2e68a7b08709e7ce9597c -->
# gz：`gz_look` 可能缓冲位置超过 `GZ_OFF_MAX` 的字节

在 zlib 的 `gzread.c` 中，`gz_look` 的透明 COPY 分支把全部待处理输入交给输出缓冲区，而不管位置 `state->x.pos` 是多少。在一个带尾部数据的 gzip 成员和一次 `gzclearerr` 之后，这会发生在文件中途。如果此时位置接近 `GZ_OFF_MAX`，读取返回时缓冲区里就有位置无法表示的字节，`gzgetc()` 宏会让 `x.pos` 溢出。这是 [gzread-pos-overflow](gzread-pos-overflow/README.md) 中位置溢出的又一条路径，不是 zlib 的另一个缺陷。正因为它，该发现的修复，即本地[补丁 0004](../../patches/README.md)，也限制了这个分支：只限制 `gz_fetch`、`gz_read` 和 `gzgets` 补不上这条路径。

状态：已通过对 C 的解读确认。没有在 sanitizer 下复现：这段历史需要约 2^63 个解码字节。所读的 C 是上游 `develop` 的提交 `757f0527154291bcf6bfbd6396ecde6bedd2db95`；`gzread.c` 在 zlib 1.4（提交 `99623ef7097352da7993ba614161fd6a311e046e`，即本项目验证的版本）中逐字节相同。带补丁 0004 时，COPY 分支只缓冲 `gz_room(state, avail_in)` 个字节，输入超出这个量时记录 `Z_DATA_ERROR`“position overflow”。该补丁没有提交上游。

## 问题

zlib.h 的 `gzgetc()` 宏对任何缓冲字节都执行 `(g)->pos++`，它在调用者的代码中执行，不做任何检查。所以只有每个读取调用返回时都满足 `x.pos + x.have <= GZ_OFF_MAX`，位置才始终可以表示。

`gz_look` 的透明 COPY 分支把全部待处理输入复制到输出缓冲区，并设置 `x.have = strm->avail_in`，至多 `size` 个字节，而不管 `x.pos` 是多少。未打补丁的 zlib 对位置根本没有界限。如果一个修复只限制 `gz_fetch` 载入的量，并让 `gz_read` 和 `gzgets` 在 `x.pos` 到达 `GZ_OFF_MAX` 时丢弃缓冲的输出，它管不到这个分支，而且 `gz_read` 中的丢弃只在其循环的下一轮才执行。所以 `gz_read` 返回时可能有 `x.pos + x.have > GZ_OFF_MAX`。经由 `gz_skip`（`gz_skip_have` 只取 `min(have, skip)`）和 `gzdirect`（它调用 `gz_look` 后就返回）也是一样。

对 C 的解读是：文件开头之后，`gz_look` 只在一种历史中走 COPY 分支。一个 gzip 成员之后跟着不是 gzip 的数据；`gz_decomp` 把它当作尾部垃圾（`junk == 1`）并设置 `eof`；`gzclearerr` 清除 `eof`；下一次读取进入 `gz_look`，此时 `direct == 0`、`junk == 1`，于是透明地复制随后的输入。`tests/verification/regressions/gz-copy-direct.c` 在真实的 C 中、在一个很小的位置上走到了这个分支。如果该成员解码出将近 `GZ_OFF_MAX` 个字节，那么此处的 `x.pos` 就接近 `GZ_OFF_MAX`。

## 调用序列

在未打补丁的 zlib 中，以及在任何不限制 `gz_look` 的修复之下：

```c
/* 一个解码为 GZ_OFF_MAX - 3 字节的 gzip 成员，其后是非 gzip 字节 */
gzread(f, ...);            /* 把成员读到末尾：x.pos = GZ_OFF_MAX - 3 */
gzread(f, buf, 1);         /* 尾部垃圾：设置 eof，how = LOOK，junk = 1 */
gzclearerr(f);             /* 清除 eof */
gzread(f, buf, 3);         /* gz_look COPY：have = 8；复制 3 个；x.pos = GZ_OFF_MAX，have = 5 */
gzgetc(f);                 /* 宏：(g)->pos++ 溢出 */
```

注释假定输入缓冲区为 8 字节，文件中还剩 8 个字节。带补丁 0004 时，第四个调用缓冲三个字节，返回 3，`x.have = 0`，并记录 `Z_DATA_ERROR`；`gzgetc` 返回 -1。

## 证据

- C：对 `gz_look`、`gz_fetch` 和 `gz_read` 的解读得到上面的轨迹。没有在真实 C 上的运行展示它：这段历史需要约 2^63 个解码字节。
- 模型，带补丁 0004：三个定理检查从一个构造的读取者出发的运行：`x.pos = GZ_OFF_MAX - 3`，`how = LOOK`，`direct = 0`，`junk = 1`，输入缓冲区 8 字节，文件中还剩 8 个字节 `'A'`。`start_clauses`：起点满足读取者不变量中关于位置的子句。`gzread_within_room`：`gzread(file, buf, 3)` 返回 3，`x.pos = GZ_OFF_MAX`，`x.have = 0`，记录 `Z_DATA_ERROR`，关于位置的子句成立。`gzgetc_after_refused`：随后的 `gzgetc` 返回 -1，没有故障。这个状态是构造出来的，不是由公开调用历史到达的。
- 模型，`gz_look` 中没有这个界限：曾在一份只限制 `gz_fetch`、`gz_read` 和 `gzgets` 的 `gzread.c` 翻译上对同一个调用求值。它返回 3，且 `x.pos = GZ_OFF_MAX`、`x.have = 5`，不满足关于位置的子句；随后的 `gzgetc` 在 `x.pos + 1` 上出故障 `Fault.ub`；`gzgetc` 函数的缓冲路径与宏相同。那份翻译没有保留，也没有定理记录这次运行。

## 范围与置信度

对以下两点置信度高：C 允许这个状态；只要能读取那么长的 gzip 成员，上述历史就能到达它。范围：位置距 `GZ_OFF_MAX` 不超过 `size` 个字节的读取者，且在一个带尾部数据的 gzip 成员和 `gzclearerr` 之后。在未打补丁的 zlib 中，没有哪条读取路径限制位置（[gzread-pos-overflow](gzread-pos-overflow/README.md)）；本页只补充一点：修复也必须限制 `gz_look`。

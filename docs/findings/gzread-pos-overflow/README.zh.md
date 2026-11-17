<!-- source-sha256: fcf63181888eb1fa503083ce7dcd6c3a1a152138b39af89b52d47ae0239b5c1e -->
# `gzread`：在设备上定位之后位置发生有符号溢出

gz 读取函数把它们交付的字节数加到有符号位置 `state->x.pos` 上，没有上界。在 Linux 上，对 `/dev/zero` 这样的字符设备做透明的 `gzseek`，可以把位置设为 `INT64_MAX`，下一次读取就使它溢出：在 `gz_read` 中，在 `gzgetc` 函数中，以及在 `zlib.h` 的 `gzgetc()` 宏中，而这个宏运行在调用者的代码里。有符号溢出是未定义行为。写入一侧见 [gzwrite-pos-overflow](../gzwrite-pos-overflow/README.md)。

## 到达它的调用

```c
int fd = open("/dev/zero", O_RDONLY);
gzFile f = gzdopen(fd, "r");
gzread(f, buf, 1);                       /* 不是 gzip：透明模式（how == COPY） */
gzseek(f, INT64_MAX, SEEK_SET);          /* 设备上的 lseek 返回 0：x.pos = INT64_MAX */
gzread(f, buf, 16);                      /* gz_read：state->x.pos += n 溢出 */
```

第二个序列在调用者的代码中溢出：

```c
gzseek(f, INT64_MAX - 4, SEEK_SET);
gzread(f, buf, 1);                       /* gz_fetch 填满整个输出缓冲区 */
gzgetc(f); gzgetc(f); gzgetc(f);         /* 宏：x.pos 到达 INT64_MAX */
gzgetc(f);                               /* 宏中的 (g)->pos++ 溢出 */
```

`gzseek64` 只检查目标能否用 `z_off64_t` 表示。在透明模式下，它随后对描述符调用 `lseek`。在 Linux 上，对 `/dev/zero` 的 `lseek` 返回 0 而不失败，设备继续交付字节。

透明读取者在这样的描述符上到达溢出：它的 `lseek` 成功却不限制偏移，之后仍交付数据，并且程序定位到了 `INT64_MAX` 附近。运行过的描述符是 Linux 的 `/dev/zero`。gzip 流要到达同样的溢出，需要大约 2^63 字节的解压输出。

每个调用都是文档用法：`zlib.h` 允许对任何描述符调用 `gzdopen`，允许定位到偏移类型能表示的任何位置，也允许之后读取。关于这个上限，它只说如果结果位置 `would not be representable in the offset type`（无法用偏移类型表示，`zlib.h:1687`），`gzseek` 返回 -1。

完整程序是 [`devzero.c`](../../../tests/regression/gzread-pos-overflow/devzero.c)。

## 证据

在 x86_64 Linux 上，对带有除 0004 以外全部补丁的 C，UndefinedBehaviorSanitizer 报告这次溢出。在 Linux 上，于仓库根目录、已检出 `zlib/` 子模块时运行：

```sh
ZLIB_SRC=$PWD/zlib bash tests/regression/gzread-pos-overflow/run.sh
```

脚本用 `-fsanitize=address,undefined -fno-sanitize-recover=undefined -g -O1` 把 zlib 源码构建两次：一次带 `patches/*.patch` 中除 0004 以外的补丁，一次带全部补丁。它在每个构建上以三种模式运行 `devzero.c`。不带 0004 时，每次运行都必须报告位置的有符号溢出。带 0004 时不得有任何报告，并且读取必须以 `Z_DATA_ERROR`（消息为 `position overflow`）结束。六项检查全部成立时脚本以状态 0 退出。在其他系统上，脚本打印 `skip: needs Linux (/dev/zero with a succeeding lseek)`，不做任何检查。

摘自 [`report.txt`](../../../tests/regression/gzread-pos-overflow/report.txt)，x86_64 Linux，不带补丁 0004 的源码：

```
gzread.c:414:22: runtime error: signed integer overflow: 9223372036854775807 + 16 cannot be represented in type 'long int'
devzero.c:73:17: runtime error: signed integer overflow: 9223372036854775807 + 1 cannot be represented in type 'long int'
gzread.c:539:21: runtime error: signed integer overflow: 9223372036854775807 + 1 cannot be represented in type 'long int'
```

第一行是 `gz_read` 中的 `state->x.pos += n`（不打补丁的文件的第 413 行）。第二行是在 `devzero.c` 中展开的 `gzgetc()` 宏。第三行是 `gzgetc` 函数。

## 影响

有符号计数器上的未定义行为。按通常的回绕，`gztell` 变为负数，之后的定位从错误的位置算起。没有发现由这次溢出引起的内存错误。这是对不打补丁的 C 的解读，**尚未由证明确认**；定理不会确认它，因为定理说的是带补丁 0004 的源码，其中不会发生这次溢出。

## 修复

[补丁 0004](../../../patches/README.md)，读取一侧。辅助函数 `gz_room(state, max)` 返回 `max`；如果再交付 `max` 个字节会使 `x.pos` 超过 `GZ_OFF_MAX`，就返回更小的值。补丁保证每个读取调用返回时 `x.pos + x.have <= GZ_OFF_MAX`，这正是 `gzgetc()` 宏所需要的。每个产生 `x.have` 的地方都保持它：

- `gz_fetch` 向输出缓冲区最多填入 `gz_room` 个字节，并且至少一个，以便仍能发现输入的结束；
- `gz_look` 在透明模式下最多缓冲 `gz_room(state, avail_in)` 个字节，输入超出时记录 `Z_DATA_ERROR`（消息为 `position overflow`）；
- `gz_read` 和 `gzgets` 最多交付 `gz_room` 个字节；如果还剩下无法交付的数据，就丢弃它并设置同样的错误；
- `gzungetc` 加入一个字节的同时把 `x.pos` 减一；
- 透明模式下的定位会清空缓冲区。

`gz_fetch` 在 `GZ_OFF_MAX` 处为发现输入结束而装入的那一个字节，会被它在该处仅有的调用者 `gz_read` 和 `gzgets` 在返回之前丢弃。所以逐字节取用已缓冲数据的路径（`gzgetc` 函数、`gzgetc()` 宏）以及 `gz_skip_have` 不需要检查。

在 `GZ_OFF_MAX - 2 * size` 以下，什么都不变。接近上限时，交付的字节相同，只是每次填入的更少。到达上限时，输入的结束仍像以前一样报告；只有会使位置溢出的数据才变成错误。

上游：该补丁是本地补丁，没有提交。

## 与证明的关系

[gzip 证明](../../proof/gzip.md)针对的是打过补丁的源码。

<!-- source-sha256: afef764451894aa875947646d0408f380d4adf2ded518d109fc0528a2f962ce9 -->
# 开头的 `gzungetc` 之后调用 `gzseek`：`gzseek64` 中有符号溢出

紧接 `gzopen` 之后调用 `gzungetc`，会使位置 `state->x.pos` 等于 -1。随后的 `gzseek` 在 `gzseek64` 中使有符号 64 位运算溢出，或者在范围检查里，或者在它计算的位移里。有符号溢出是未定义行为。

这些语句在不打补丁的 `gzlib.c` 中：

```c
    if (offset > GZ_OFF_MAX - pos)                                           /* 395 */
        ret = LSEEK(state->fd, pos - state->x.pos - (z_off64_t)state->x.have, /* 403 */
    offset = pos - state->x.pos;                                             /* 424 */
```

## 到达它的调用

两个序列，各自在一个新的句柄上。文件可以是 gzip 文件，也可以是任何其他文件（透明模式）。

```c
gzFile f = gzopen(path, "rb");
gzungetc('Q', f);                   /* 在位置 0 是允许的：x.pos 变为 -1 */
gzseek(f, 1, SEEK_CUR);             /* gzlib.c:395：GZ_OFF_MAX - pos，其中 pos == -1 */
```

```c
gzFile f = gzopen(path, "rb");
gzungetc('Q', f);                   /* x.pos 变为 -1 */
gzseek(f, LONG_MAX, SEEK_SET);      /* 范围检查通过（pos 先是 0，然后是 LONG_MAX）；
                                       pos - state->x.pos 是 LONG_MAX + 1：
                                       gzlib.c:403（透明），gzlib.c:424（gzip） */
```

用 `SEEK_CUR` 时，任何偏移都会到达第 395 行。用 `SEEK_SET` 时，需要目标大于 `GZ_OFF_MAX + x.pos`；推回一个字符之后，这就是 `GZ_OFF_MAX` 本身。完整程序是 [`seek.c`](../../../tests/regression/gzseek-pushback-overflow/seek.c)。

`zlib.h` 允许这个序列：`If gzungetc is used immediately after gzopen or gzdopen`（如果紧接 gzopen 或 gzdopen 之后使用 gzungetc，`zlib.h:1643`），推回的字符数最多可以达到输出缓冲区的大小。对 `gzseek`，它说如果结果位置 `would not be representable in the offset type`（无法用偏移类型表示，`zlib.h:1687`），调用返回 -1。

## 证据

在不打补丁的 C 上，UndefinedBehaviorSanitizer 报告全部三条语句。在仓库根目录、已检出 `zlib/` 子模块时运行：

```sh
ZLIB_SRC=$PWD/zlib bash tests/regression/gzseek-pushback-overflow/run.sh
```

脚本用 `-fsanitize=address,undefined -fno-sanitize-recover=undefined -g -O1` 把 zlib 源码构建两次：一次不带任何补丁，一次带 `patches/*.patch`。它在每个构建上运行 `seek.c` 四次（透明输入和 gzip 输入，`SEEK_CUR` 和 `SEEK_SET`）。不打补丁的构建必须在每次运行中报告有符号溢出。打补丁的构建必须没有任何报告；这时 `SEEK_CUR` 返回 0，`SEEK_SET` 返回 -1。八项检查全部成立时脚本以状态 0 退出，最后一行是：

```
ok: patched: seek set LONG_MAX = -1, no report
```

摘自 [`report.txt`](../../../tests/regression/gzseek-pushback-overflow/report.txt)，x86_64 Linux，不打补丁的源码，每条语句一行：

```
gzlib.c:395:29: runtime error: signed integer overflow: 9223372036854775807 - -1 cannot be represented in type 'long int'
gzlib.c:403:36: runtime error: signed integer overflow: 9223372036854775807 - -1 cannot be represented in type 'long int'
gzlib.c:424:12: runtime error: signed integer overflow: 9223372036854775807 - -1 cannot be represented in type 'long int'
```

arm64 macOS 在相同的行给出同样的三条报告。

## 影响

溢出的值是文件偏移或位移。在第 403 行它被传给 `lseek`；在第 424 行它成为待执行的跳过量。没有发现由此引起的内存错误。

## 修复

[补丁 0002](../../../patches/README.md) 在 `gzseek64` 中改了两处：

- 只有当 `pos > 0` 时才计算上界检查，所以 `GZ_OFF_MAX - pos` 不会溢出；
- 在 `pos += offset` 之后，如果位移 `pos - state->x.pos` 放不下，就拒绝从负位置出发的定位：`state->x.pos < 0 && pos > GZ_OFF_MAX + state->x.pos` 时返回 -1。

上游：该补丁是[拉取请求 #1361](https://github.com/madler/zlib/pull/1361) 中 `gzlib.c` 的部分，该拉取请求仍处于打开状态。

## 与证明的关系

[`gzseek64` 和 `gzseek` 的安全证明](../../proof/gzip.md)针对的是打过补丁的源码。

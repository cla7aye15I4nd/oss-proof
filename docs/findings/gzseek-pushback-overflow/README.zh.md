<!-- source-sha256: edc3743cac96a25011d953d61b5342a6054c5e2398667140d87ebd0daf043ad5 -->
# 开头的 `gzungetc` 之后调用 `gzseek`：`gzseek64` 中有符号溢出

`gzopen` 之后立即调用 `gzungetc`，会使位置 `state->x.pos` 等于 -1。随后的 `gzseek` 在 `gzseek64` 中让有符号 64 位运算溢出，溢出发生在一处范围检查里，或者在它计算的位移里。zlib 的维护者只读本页，就能复现这些报告并作出判断。测试文件在 [`tests/regression/gzseek-pushback-overflow`](../../../tests/regression/gzseek-pushback-overflow/README.md)。

## 状态

- 未定义行为：有符号整数溢出，出现在 `gzlib.c` 的三条语句上。在文档用法之内。
- 在未修改的上游 `develop` 的提交 `757f0527154291bcf6bfbd6396ecde6bedd2db95` 上由 UndefinedBehaviorSanitizer 报告，平台为 x86_64 Linux（GCC 15.2）和 arm64 macOS（Apple clang 21）。`gzlib.c` 在 zlib 1.4（提交 `99623ef7097352da7993ba614161fd6a311e046e`，即本项目验证的版本）中逐字节相同；这里没有记录在该版本上的运行。
- 修复已作为[拉取请求 #1361](https://github.com/madler/zlib/pull/1361) 提交上游。2026-11-14 时，该拉取请求处于打开状态，维护者还没有答复。被验证的源码把其中 `gzlib.c` 的部分作为[补丁 0002](../../../patches/README.md) 应用。

## 调用序列

两个序列，各用一个新打开的句柄。文件可以是 gzip 文件，也可以是别的文件（透明模式）。

```c
gzFile f = gzopen(path, "rb");
gzungetc('Q', f);                   /* 位置 0 处允许：x.pos 变为 -1 */
gzseek(f, 1, SEEK_CUR);             /* gzlib.c:395：GZ_OFF_MAX - pos，此时 pos == -1 */
```

```c
gzFile f = gzopen(path, "rb");
gzungetc('Q', f);                   /* x.pos 变为 -1 */
gzseek(f, LONG_MAX, SEEK_SET);      /* 范围检查通过（pos 先是 0，后是 LONG_MAX）；
                                       pos - state->x.pos 等于 LONG_MAX + 1：
                                       gzlib.c:403（透明），gzlib.c:424（gzip） */
```

未打补丁的 `gzlib.c` 中的语句：

```c
    if (offset > GZ_OFF_MAX - pos)                                           /* 395 */
        ret = LSEEK(state->fd, pos - state->x.pos - (z_off64_t)state->x.have, /* 403 */
    offset = pos - state->x.pos;                                             /* 424 */
```

完整程序是 [`seek.c`](../../../tests/regression/gzseek-pushback-overflow/seek.c)。

## 运行

在仓库根目录，`zlib/` 子模块已检出：

```sh
ZLIB_SRC=$PWD/zlib bash tests/regression/gzseek-pushback-overflow/run.sh
```

脚本用 `-fsanitize=address,undefined -fno-sanitize-recover=undefined -g -O1` 把 zlib 源码构建两次：一次不打任何补丁，一次打上 `patches/*.patch`。它在每个构建上运行 `seek.c` 四次（透明输入和 gzip 输入，`SEEK_CUR` 和 `SEEK_SET`）。未打补丁的构建每次运行都必须报告有符号溢出。打过补丁的构建不得有任何报告；这时 `SEEK_CUR` 返回 0，`SEEK_SET` 返回 -1。八项检查全部成立时脚本以状态 0 退出，最后一行是：

```
ok: patched: seek set LONG_MAX = -1, no report
```

## Sanitizer 判定

摘自 [`report.txt`](../../../tests/regression/gzseek-pushback-overflow/report.txt)，x86_64 Linux，未打补丁的源码，每条语句一行：

```
gzlib.c:395:29: runtime error: signed integer overflow: 9223372036854775807 - -1 cannot be represented in type 'long int'
gzlib.c:403:36: runtime error: signed integer overflow: 9223372036854775807 - -1 cannot be represented in type 'long int'
gzlib.c:424:12: runtime error: signed integer overflow: 9223372036854775807 - -1 cannot be represented in type 'long int'
```

在 arm64 macOS 上运行了一次，在相同的行得到同样的三份报告；那里类型打印为 `off_t`，第三份报告在第 18 列。

## 范围与严重程度

- **谁会遇到。** 在读取任何数据之前调用 `gzungetc`、随后调用 `gzseek` 或 `gzseek64` 的读取者，两种模式都一样。用 `SEEK_CUR` 时，任何偏移都会到达第 395 行。用 `SEEK_SET` 时，目标要大于 `GZ_OFF_MAX + x.pos`；只推回一个字符时，这就是 `GZ_OFF_MAX` 本身。
- **后果。** 溢出的值是文件偏移或位移。在第 403 行它被传给 `lseek`；在第 424 行它成为待执行的跳过量。未打补丁的代码在溢出之后按回绕算术会做什么，没有测量过。同一批运行中 AddressSanitizer 也在起作用，第一份报告就是这个溢出。
- **严重程度。** 低：位置上的未定义算术，只有不常见的调用顺序才能到达；没有发现随之而来的内存错误。

## `zlib.h` 的说法

这个序列是文档用法：zlib.h 写到 “`If gzungetc is used immediately after gzopen or gzdopen`”（如果 gzungetc 紧跟在 gzopen 或 gzdopen 之后使用，`zlib.h:1643`）的情形：这时允许推回的字符数可达输出缓冲区的大小。关于 `gzseek`，zlib.h 说，如果结果位置 “`would not be representable in the offset type`”（不能用偏移类型表示），它返回 -1（`zlib.h:1687`）；还说流被重新定位时，推回的字符会被丢弃。

## 修复

[拉取请求 #1361](https://github.com/madler/zlib/pull/1361)，最新提交 `ce2248ee9750`，`gzlib.c` 部分：

- 上界检查只在 `pos > 0` 时求值，所以 `GZ_OFF_MAX - pos` 不会溢出；
- 在 `pos += offset` 之后，如果位移 `pos - state->x.pos` 放不下，就拒绝从负位置出发的定位：`state->x.pos < 0 && pos > GZ_OFF_MAX + state->x.pos` 时返回 -1。

[补丁 0002](../../../patches/README.md) 就是这一改动。该拉取请求中 `test/example.c` 的部分不属于被验证的源码。

## 与证明的关系

[`gzseek64` 和 `gzseek` 的安全证明](../../proof/gzip.md)针对的是打过补丁的源码。

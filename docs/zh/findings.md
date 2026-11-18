<!-- source-sha256: 966f80fe84116798834123de15ca75d402bf7ad702b1b74c288bead2ea5198f1 -->
# 发现：在 zlib 中发现的问题

这项工作在 zlib 中发现了八个问题。每一个都是 zlib 本身的缺陷，都能通过对 `zlib.h` 中有文档的函数的文档用法到达，并且由一次真实 C 的运行展示。七个[补丁](../../patches/README.md)修复全部八个：补丁 0003 修复两个。其中六个是未定义行为或内存错误。另外两个是 `deflateBound` 的失信：界太小，但没有任何行为是未定义的。

| 问题 | 错在哪里 | 到达它的调用 | 证据 | 修复 | 上游 |
| --- | --- | --- | --- | --- | --- |
| `inflateCopy` 比较无关的指针 | `inflateCopy` 用 `>=` 和 `<=` 比较一个指向静态表的指针和一个指向堆上状态的指针：未定义行为。没有观察到错误结果。 | 对已经解码过固定码块、之后没有解码过动态码块的流调用 `inflateCopy` | AddressSanitizer 的指针对检查，`inflate.c:1383` | 补丁 0001 | [拉取请求 #1369](https://github.com/madler/zlib/pull/1369)，维护者答复“Applied”；zlib 1.4 中没有 |
| 开头的 `gzungetc` 之后调用 `gzseek` | 推回一个字符之后位置是 -1，`gzseek64` 的范围检查使有符号 64 位运算溢出。 | `gzopen`、`gzungetc`，然后 `gzseek` | UndefinedBehaviorSanitizer，`gzlib.c:395`、`403`、`424` | 补丁 0002 | [拉取请求 #1361](https://github.com/madler/zlib/pull/1361)，处于打开状态 |
| `gzread` 从过时的 `x.next` 复制 | `read()` 返回一些字节后失败时，`gz_fetch` 在设置 `x.next` 之前就返回，读取者从旧指针复制：读到输出缓冲区之外的堆内存。 | 对不是 gzip 的输入调用 `gzread`，而描述符在给出部分数据后失败 | AddressSanitizer，`gzread.c:369` | 补丁 0003 | [拉取请求 #1405](https://github.com/madler/zlib/pull/1405)，处于打开状态 |
| gz 位置溢出，读取 | 读取函数把字节数加到有符号 64 位位置 `x.pos` 上，没有上界：`gz_read`、`gzgetc` 和 `gzgetc()` 宏中有符号溢出。 | 在 `lseek` 成功却不移动的设备（Linux 的 `/dev/zero`）上用 `gzseek` 定位到 2^63 附近，然后 `gzread` 或 `gzgetc` | x86_64 Linux 上的 UndefinedBehaviorSanitizer | 补丁 0003 | [拉取请求 #1405](https://github.com/madler/zlib/pull/1405)，处于打开状态 |
| gz 位置溢出，写入 | 写入函数把字节数加到 `x.pos` 上，没有上界：`gz_write` 和 `gzputc` 中有符号溢出。 | 不压缩的写入者向能接受这些零的接收端（`/dev/null`）写，用 `gzseek` 向前定位到 2^63 附近，然后 `gzwrite` 或 `gzputc` | UndefinedBehaviorSanitizer，`gzwrite.c:230`、`352` | 补丁 0004 | [拉取请求 #1406](https://github.com/madler/zlib/pull/1406)，处于打开状态 |
| 描述符偏移为负时的 `gzoffset64` | `gzoffset64` 只把 `lseek` 返回的 `-1` 当作失败。结果是别的负值时，减去已缓冲输入的那次减法使有符号 64 位运算溢出。 | 对 `lseek` 会返回负偏移的描述符（Linux 的 `/proc/<pid>/mem`）调用 `gzdopen`，然后 `gzread`，调用者把描述符移到一个很大的负偏移，再调用 `gzoffset64` | UndefinedBehaviorSanitizer，`gzlib.c:494` | 补丁 0005 | [拉取请求 #1404](https://github.com/madler/zlib/pull/1404)，处于打开状态 |
| `Z_FIXED` 时 `deflateBound` 太小 | 失信：一次带 `Z_FINISH` 的 `deflate` 调用，输出空间为 `deflateBound` 个字节，返回 `Z_OK`。对 1,000,000 字节的输入，界是 1,000,318，而流最多需要 1,008,570 字节。 | 以 `windowBits` 15、`memLevel` 8、`Z_FIXED`、级别 1 到 3 调用 `deflateInit2`；`deflateBound`；`deflate`。`compress`、`compress2` 和 `compressBound` 不受影响。 | 真实 C 的一次运行返回 `Z_OK` | 补丁 0006 | [拉取请求 #1394](https://github.com/madler/zlib/pull/1394)，处于打开状态 |
| gzip extra 字段长度为 2^32 − 2 或 2^32 − 1 时的 `deflateBound` | 失信：`2 + extra_len` 在 32 位上回绕，界大约小了 64 KiB，用这么多空间调用 `deflate(Z_FINISH)` 返回 `Z_OK`。 | 以这两个长度之一调用 `deflateSetHeader`，然后 `deflateBound`、`deflate`。`zlib.h` 对 `extra_len` 没有规定上限；gzip 头部的 extra 字段最多容纳 65535 个字节。 | 真实 C 的一次运行返回 `Z_OK` | 补丁 0007 | [拉取请求 #1360](https://github.com/madler/zlib/pull/1360) 的 `deflate.c` 部分，处于打开状态 |

被验证的源码是 zlib 1.4（上游提交 `99623ef7`）加七个补丁。真实 C 的运行是在 `99623ef7` 上或它的直接父提交、上游提交 `757f0527` 上做的，每次运行都不带修复该问题的补丁。这两个提交之间，库的 C 源码只在版本和版权字符串以及 `inftrees.c` 中表 `lext` 的最后两项上不同。

sanitizer 报告或真实 C 的一次运行，是关于那一次运行的证据，不是证明。安全定理说的是打过补丁的源码。

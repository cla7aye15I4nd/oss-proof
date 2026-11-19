<!-- source-sha256: efa3da779f1fd6be7f79cc8ab670801bebe7cf3db443ed29b4e7142e65047db7 -->
# 发现：zlib-ng 中发现的问题

本工作在被验证提交的 zlib-ng `develop` 分支中发现了十个问题。每个都是 zlib-ng 自身的缺陷，可通过 `zlib.h`
有文档的函数触达，并由真实 C 代码的运行（消毒器无法发现时，由经跟踪的运行与 ISO C17 条文）展示。补丁 0003、0004、
0006、0007、0008、0009、0010、0011、0012 与 0013 修复了它们，每个问题一个补丁。

| 问题 | 错在哪里 | 触达的调用 | 证据 | 修复 | 上游 |
| --- | --- | --- | --- | --- | --- |
| `inflateCopy` 比较无关指针 | `inflateCopy` 用 `>=` 与 `<=` 比较指向静态表 `lenfix` 的指针与指向堆状态的指针：未定义行为（ISO C17 §6.5.8p5）。 | 对处于固定编码块内的流调用 `inflateCopy` | AddressSanitizer 指针对检查，`inflate.c:1410` | 补丁 0003 | 未提交 |
| `gzseek` 偏移溢出 | `gzseek64` 在 `SEEK_CUR` 下无界地把待跳过量加到偏移上：64 位有符号溢出。在首次读取之前还会对从未赋值的 `x.next` 加 0。 | 以写模式 `gzopen`，`gzseek(file, INT64_MAX, SEEK_SET)`，`gzseek(file, 1, SEEK_CUR)` | UndefinedBehaviorSanitizer，`gzlib.c:412` | 补丁 0004 | 未提交 |
| gzip 额外字段长度很大时 `deflateBound` 过小 | 对带额外字段的用户 gzip 头，`deflateBound` 以 32 位 `unsigned` 计算 `2 + extra_len`，在 `extra_len >= 0xfffffffe` 时回绕，而 `deflate` 写出 `2 + (extra_len & 0xffff)` 个头字节。于是以 `avail_out = deflateBound(...)` 进行一次 `deflate(Z_FINISH)` 不返回 `Z_STREAM_END`，违背 `zlib.h`。 | gzip 模式 `deflateInit2`，`extra_len = 0xffffffff` 的 `deflateSetHeader`，`deflateBound`，`deflate(Z_FINISH)` | 真实 C 代码返回 `Z_OK` 而非 `Z_STREAM_END` | 补丁 0006 | 未提交 |
| `inflate` 比较窗口指针与输出指针 | 当匹配回溯到滑动窗口时，`inflate`（`MATCH` 状态）调用 `chunkcopy_safe`，`inflate_fast` 调用 `CHUNKCOPY_SAFE` 与 `chunkmemset`，其中 `from` 指向窗口（位于 inflate 自身的分配中），`out` 指向调用者的输出缓冲区。它们用 `>=`、`<` 比较并相减这两个指针：未定义行为（ISO C17 §6.5.8p5、§6.5.6p9）。 | 对匹配回溯到窗口的合法 zlib 流调用 `inflate`，每次调用的 `avail_out` 较小 | AddressSanitizer 指针对检查，`inflate_p.h:224`、`inflate_p.h:225`、`chunkset_tpl.h:119`、`chunkset_tpl.h:125`、`chunkset_tpl.h:319` | 补丁 0007 | 未提交 |
| `inflateSync` 对空 `next_in` 加 0 | 没有输入（`next_in == NULL`，`avail_in == 0`）但已由 `inflatePrime` 预置至少 8 位时，`inflateSync` 执行 `strm->next_in += len` 且 `len == 0`：`NULL + 0`（ISO C17 §6.5.6p8）。 | `inflateInit`，`inflatePrime(strm, 16, v)`，`inflateSync` | 经跟踪的运行（加法之后返回 `Z_DATA_ERROR`）；UndefinedBehaviorSanitizer 在 C 中不报告 `NULL + 0` | 补丁 0008 | 未提交 |
| `inflateSetDictionary` 接受空字典 | `zlib.h` 规定 `NULL` 字典是无效参数（`Z_STREAM_ERROR`）。在原始流上，`inflateSetDictionary(strm, NULL, 0)` 却以 `end = NULL + 0` 调用 `updatewindow`，计算 `end - 0` 并以空源指针、长度 0 调用 `memcpy`（ISO C17 §6.5.6p8、§7.24.1p2），然后返回 `Z_OK`。 | `inflateInit2(strm, -15)`，`inflateSetDictionary(strm, NULL, 0)` | 经跟踪的运行（返回 `Z_OK`） | 补丁 0009 | 未提交 |
| `inflatePrime` 之后 `inflate` 把 `next_in` 移到输入之前 | `inflate_fast` 假定进入时位缓冲中少于 8 位，并在退出时退还 `bits >> 3` 个输入字节（`in -= len`）。`inflatePrime` 在其中放入多达 32 位之后，它退还的字节多于读入的字节：`next_in` 指向调用者缓冲区之前（ISO C17 §6.5.6p8），`avail_in` 大于调用者给出的值，`total_in` 回绕到 0 以下。 | `inflateInit2(strm, -15)`，`inflatePrime(strm, 16, 3)`，`inflatePrime(strm, 16, 0)`，以 32 字节输入调用 `inflate` | 真实 C 代码的运行：以 32 字节调用后 `avail_in` 为 34，`total_in` 为 4294967294 | 补丁 0010 | 未提交 |
| 两个共享同一 `gz_header` 的流写出其额外字段缓冲区 | `inflate`（`EXTRA` 状态）把额外字段放在 `len = head->extra_len - state->length` 处，并用 `len < extra_max` 与 `len + copy > extra_max` 限定拷贝，都以 32 位 `unsigned` 计算。它假定 `head->extra_len` 是本流 `EXLEN` 状态存入的值。两个流共享该头时，另一个流的 `EXLEN` 可以存入更小的 `extra_len`；此时 `len` 回绕到接近 2^32，而 `extra_max` 接近 2^32 时 `len + copy` 也回绕，于是 `memcpy` 写出缓冲区末尾。 | `inflateInit2(a, 31)`，以 `g.extra_max = 0xffffffff` 调用 `inflateGetHeader(a, &g)`，`inflate(a)` 读到额外字段长度之前，`inflateCopy(b, a)`（或再次 `inflateInit2(b, 31)`、`inflateGetHeader(b, &g)`），`inflate(a)` 读入额外长度 100，`inflate(b)` 读入额外长度 10，以 100 字节额外字段调用 `inflate(a)` | AddressSanitizer heap-buffer-overflow，`inflate.c:625`（写 100 字节，越过缓冲区 11 字节） | 补丁 0011 | 未提交 |
| 7 至 9 级 `deflate` 构造出指向窗口所在块之前的指针 | 在慢速最长匹配搜索（`longest_match_slow_roll_c`，以及 7、8 级使用的 `longest_match_slow_knuth_c`，均来自 `match_tpl.h`）中，惰性搜索若为当前匹配的某个子串找到更早的链，就按该子串的偏移把匹配基址往回移：`mbase_start -= match_offset`（`match_tpl.h:133`），在接受一个匹配之后还有 `mbase_start = window - match_offset`（`match_tpl.h:287`）。`alloc_deflate` 把窗口放在其块的起始处，前面至多 63 字节的对齐填充（`malloc` 返回 64 字节对齐的块时为 0，glibc 的大块为 48 字节），而 `match_offset` 可达 256。于是 `window - match_offset` 指向所分配对象的起点之前：未定义行为（ISO C17 §6.5.6p8），尽管之后经由它读取的每个字节都在窗口内。 | `deflateInit2(strm, 9, Z_DEFLATED, 15, 4, Z_FILTERED)` 或 `deflateInit2(strm, 9, Z_DEFLATED, 31, 1, Z_FIXED)`，然后对 70000 字节的随机、文本与重复混合数据调用 `deflate` | 真实 C 代码的经跟踪运行（插桩的 `match_tpl.h` 副本打印 `match_offset` 与窗口在块内的偏移）：窗口偏移为 0 时出现偏移 191 与 223；没有消毒器报告该指针本身 | 补丁 0012 | 未提交 |
| 以负的 `max_lazy` 调用 `deflateTune` 后 `deflate` 除以零 | `deflateTune` 原样保存 `max_lazy`。3 至 6 级（`deflate_medium`）把它用作每个匹配的哈希插入次数，并以 32 位 `unsigned` 计算 `max_len = 2 * max_insert_count`，`max_lazy = INT_MIN` 时回绕为 0。于是距离为 1 的匹配（一串相同字节）只留下一个待插入位置，`insert_knuth_stepped` 除以 `inserts - 1 = 0`：未定义行为（ISO C17 §6.5.5p5），在 x86_64 上崩溃（`SIGFPE`）。 | `deflateInit(strm, 4)`，`deflateTune(strm, 8, INT_MIN, 128, 128)`，对 4096 个相同字节调用 `deflate(strm, Z_FINISH)` | UndefinedBehaviorSanitizer，`insert_string_p.h:186` | 补丁 0013 | 未提交 |

早先 2.3.3 版本中发现的问题（`gzbuffer` 大小溢出、负长度时 `crc32_combine*` 不返回、`adler32` 以 `NULL`
和长度 1 调用）已在 `develop` 分支修复；它们的复现保留为回归测试。

这些运行在被验证源码按被验证配置（参见[概述](index.html)）的 LP64 构建上进行，应用了除修复该问题的补丁之外的
所有补丁，而非在 x86_64 Linux 目标本身上。应用全部补丁后，这些调用均无消毒器报告并正常返回。

消毒器报告或真实 C 代码的运行只是关于那次运行的证据，不是证明。安全性定理针对的是打过补丁的源码。

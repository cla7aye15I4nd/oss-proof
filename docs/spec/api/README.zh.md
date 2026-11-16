<!-- source-sha256: ac8099d0035dc19365897985a940ee5bcbcfba737cf124fb778507a28c72a853 -->

# zlib API 手册

[文档](../../README.md) / API 手册

本手册有 96 个条目：默认构建的 95 个函数各一个，另有一个只在 Windows 上存在的 `gzopen_w`。
可以用它查找函数，了解调用者必须提供什么、调用返回什么或改变什么，
以及哪个 Lean 目标陈述了它的安全性、在什么条件下成立。

每个条目有两层：

- **契约**：C 签名、用途、**前置条件**（调用者提供什么）、**后置条件**（结果）、
  **效果**（什么可以改变）以及边界情况。它是文字说明，读自 C 和 `zlib.h`；
- **证明目标**：函数的安全目标、其 Lean 命题的条件，以及它保证什么。这是已经证明的部分。

## 选择起点

| 你想要…… | 阅读 |
| --- | --- |
| 理解契约术语和构建范围 | [如何阅读契约](contracts.md) |
| 管理缓冲区、所有权、重置和流调用顺序 | [共享流规则](streams.md) |
| 通过 `z_stream` 增量压缩 | [流式压缩](deflate-stream.md) |
| 通过 `z_stream` 增量解压 | [流式解压](inflate-stream.md) |
| 通过回调提供解压输入并接收输出 | [回调解压](inflate-back.md) |
| 压缩或解压整个缓冲区，或查询库信息 | [缓冲区工具与库信息](utility.md) |
| 计算或组合 Adler-32 和 CRC-32 校验和 | [校验和](checksums.md) |
| 读写 gzip 文件句柄、定位或关闭文件 | [Gzip 文件](gz-file.md) |

## 范围 {#scope-and-status}

**源码与构建。** 本手册遵循固定版本的 zlib 源码，加上[补丁](../../../patches/README.md)中列出的补丁，
针对默认 LP64 Linux 静态构建和默认分配器。条目若另有限制，会自行写明。
`gzopen_w` 只在 Windows 上存在，单独列出。

**契约是聚焦的。** 聚焦契约描述通常的正确用法；它的前置条件可以比 `zlib.h` 允许的窄。
前置条件之外的调用不在该契约之内。这并不说明它在 C 中是未定义行为，安全目标往往也覆盖它
（见[如何阅读契约](contracts.md)）。

**已证明的内容。** 每个有文档的函数的必需目标是它的安全目标：没有未定义行为，没有内存错误，
没有泄漏，并且终止（见[安全性](../safety.md)）。每个条目在**证明目标**下写出它。
`zlib.h` 在“undocumented functions”（未文档化的函数）之下声明的函数有条目，但没有必需目标。
唯一的例外是 `gzvprintf`：`gzprintf` 经由它实现，它的目标 `Goal.gzvprintf_safety` 是必需的。
目标的条件中比 `zlib.h` 窄的，在[偏离记录](../../deviations.md)中各有一行。

**这里没有证明的内容。** 后置条件描述的返回值、输出字节和状态变化是功能行为。
它们读自 C；没有定理陈述的部分**尚未由证明确认**。
每个条目也写出它的功能目标。单个函数的功能目标不在计划内；条目会说明有没有定理证明它。

哪些目标已完成，见[进度](../../progress.md#functions)。

## 查找函数

索引按用途链接全部 96 个条目。函数页面保留 C 名称，包括初始化宏所调用的函数名末尾的下划线。

### 流式压缩

| 函数 | 简述 |
| --- | --- |
| [deflateInit_](deflate-stream.md#deflateinit_) | 使用默认窗口、内存级别和策略初始化 |
| [deflateInit2_](deflate-stream.md#deflateinit2_) | 指定所有参数进行初始化 |
| [deflateSetDictionary](deflate-stream.md#deflatesetdictionary) | 预载字典 |
| [deflateGetDictionary](deflate-stream.md#deflategetdictionary) | 复制出当前字典窗口 |
| [deflateResetKeep](deflate-stream.md#deflateresetkeep) | 重新开始一个流，但保留窗口和哈希表（未文档化） |
| [deflateReset](deflate-stream.md#deflatereset) | 重新开始一个流 |
| [deflateSetHeader](deflate-stream.md#deflatesetheader) | 提供要写入的 gzip 头 |
| [deflatePending](deflate-stream.md#deflatepending) | 查询待输出数据 |
| [deflateUsed](deflate-stream.md#deflateused) | 查询最近一次刷新最后一个字节使用的位数 |
| [deflatePrime](deflate-stream.md#deflateprime) | 在输出中插入位 |
| [deflateParams](deflate-stream.md#deflateparams) | 更改级别和策略 |
| [deflateTune](deflate-stream.md#deflatetune) | 设置内部匹配搜索的调优参数 |
| [deflateBound_z](deflate-stream.md#deflatebound_z) | 压缩大小上界（长度为大小类型） |
| [deflateBound](deflate-stream.md#deflatebound) | 压缩大小上界（`uLong`） |
| [deflate](deflate-stream.md#deflate) | 压缩 |
| [deflateEnd](deflate-stream.md#deflateend) | 释放流 |
| [deflateCopy](deflate-stream.md#deflatecopy) | 复制流 |

### 流式解压

| 函数 | 简述 |
| --- | --- |
| [inflateResetKeep](inflate-stream.md#inflateresetkeep) | 重新开始一个流并保留窗口内容（未文档化） |
| [inflateReset](inflate-stream.md#inflatereset) | 重新开始一个流，丢弃窗口内容 |
| [inflateReset2](inflate-stream.md#inflatereset2) | 使用新窗口大小重新开始一个流 |
| [inflateInit2_](inflate-stream.md#inflateinit2_) | 指定窗口大小进行初始化 |
| [inflateInit_](inflate-stream.md#inflateinit_) | 使用默认窗口大小初始化 |
| [inflatePrime](inflate-stream.md#inflateprime) | 在输入中插入位 |
| [inflate](inflate-stream.md#inflate) | 解压 |
| [inflateEnd](inflate-stream.md#inflateend) | 释放流 |
| [inflateGetDictionary](inflate-stream.md#inflategetdictionary) | 复制出窗口 |
| [inflateSetDictionary](inflate-stream.md#inflatesetdictionary) | 提供字典 |
| [inflateGetHeader](inflate-stream.md#inflategetheader) | 请求获取 gzip 头 |
| [inflateSync](inflate-stream.md#inflatesync) | 搜索完全刷新点 |
| [inflateSyncPoint](inflate-stream.md#inflatesyncpoint) | 检查是否停在同步刷新点 |
| [inflateCopy](inflate-stream.md#inflatecopy) | 复制流 |
| [inflateUndermine](inflate-stream.md#inflateundermine) | 请求距离检查选项；默认构建返回 `Z_DATA_ERROR` |
| [inflateValidate](inflate-stream.md#inflatevalidate) | 控制封装的完整性检查 |
| [inflateMark](inflate-stream.md#inflatemark) | 查询 `inflate` 在块或码中的位置 |
| [inflateCodesUsed](inflate-stream.md#inflatecodesused) | 查询当前块已使用的编码表项数（未文档化） |

### 回调解压

| 函数 | 简述 |
| --- | --- |
| [inflateBackInit_](inflate-back.md#inflatebackinit_) | 为回调解压初始化 |
| [inflateBack](inflate-back.md#inflateback) | 使用输入、输出回调解压 |
| [inflateBackEnd](inflate-back.md#inflatebackend) | 释放流 |

### 整块缓冲区操作与库信息

| 函数 | 简述 |
| --- | --- |
| [compress2_z](utility.md#compress2_z) | 按指定级别压缩缓冲区（长度为大小类型） |
| [compress2](utility.md#compress2) | 按指定级别压缩缓冲区 |
| [compress_z](utility.md#compress_z) | 按默认级别压缩缓冲区（长度为大小类型） |
| [compress](utility.md#compress) | 按默认级别压缩缓冲区 |
| [compressBound_z](utility.md#compressbound_z) | 压缩大小上界（长度为大小类型） |
| [compressBound](utility.md#compressbound) | 压缩大小上界 |
| [uncompress2_z](utility.md#uncompress2_z) | 解压缓冲区，报告使用的输入量（长度为大小类型） |
| [uncompress2](utility.md#uncompress2) | 解压缓冲区，报告使用的输入量 |
| [uncompress_z](utility.md#uncompress_z) | 解压缓冲区（长度为大小类型） |
| [uncompress](utility.md#uncompress) | 解压缓冲区 |
| [zlibVersion](utility.md#zlibversion) | 库的版本字符串 |
| [zlibCompileFlags](utility.md#zlibcompileflags) | 构建库所用的类型大小和选项 |
| [zError](utility.md#zerror) | 返回码对应的文本 |

### 校验和

| 函数 | 简述 |
| --- | --- |
| [adler32_z](checksums.md#adler32_z) | 缓冲区的 Adler-32（长度为大小类型） |
| [adler32](checksums.md#adler32) | 缓冲区的 Adler-32 |
| [adler32_combine](checksums.md#adler32_combine) | 组合两个 Adler-32 值 |
| [adler32_combine64](checksums.md#adler32_combine64) | 组合两个 Adler-32 值（64 位长度） |
| [get_crc_table](checksums.md#get_crc_table) | CRC-32 表 |
| [crc32_z](checksums.md#crc32_z) | 缓冲区的 CRC-32（长度为大小类型） |
| [crc32](checksums.md#crc32) | 缓冲区的 CRC-32 |
| [crc32_combine_gen64](checksums.md#crc32_combine_gen64) | 用于组合的算子（64 位长度） |
| [crc32_combine_gen](checksums.md#crc32_combine_gen) | 用于组合的算子 |
| [crc32_combine_op](checksums.md#crc32_combine_op) | 使用算子组合 |
| [crc32_combine64](checksums.md#crc32_combine64) | 组合两个 CRC-32 值（64 位长度） |
| [crc32_combine](checksums.md#crc32_combine) | 组合两个 CRC-32 值 |

### Gzip 文件

| 函数 | 简述 |
| --- | --- |
| [gzopen](gz-file.md#gzopen), [gzopen64](gz-file.md#gzopen64), [gzdopen](gz-file.md#gzdopen), [gzopen_w](gz-file.md#gzopen_w) | 打开文件 |
| [gzbuffer](gz-file.md#gzbuffer), [gzsetparams](gz-file.md#gzsetparams) | 缓冲区大小、压缩参数 |
| [gzread](gz-file.md#gzread), [gzfread](gz-file.md#gzfread), [gzgetc](gz-file.md#gzgetc), [gzgetc_](gz-file.md#gzgetc_), [gzungetc](gz-file.md#gzungetc), [gzgets](gz-file.md#gzgets) | 读取 |
| [gzwrite](gz-file.md#gzwrite), [gzfwrite](gz-file.md#gzfwrite), [gzputc](gz-file.md#gzputc), [gzputs](gz-file.md#gzputs), [gzprintf](gz-file.md#gzprintf), [gzvprintf](gz-file.md#gzvprintf), [gzflush](gz-file.md#gzflush) | 写入 |
| [gzrewind](gz-file.md#gzrewind), [gzseek](gz-file.md#gzseek), [gzseek64](gz-file.md#gzseek64), [gztell](gz-file.md#gztell), [gztell64](gz-file.md#gztell64), [gzoffset](gz-file.md#gzoffset), [gzoffset64](gz-file.md#gzoffset64) | 定位 |
| [gzeof](gz-file.md#gzeof), [gzdirect](gz-file.md#gzdirect), [gzerror](gz-file.md#gzerror), [gzclearerr](gz-file.md#gzclearerr) | 状态 |
| [gzclose](gz-file.md#gzclose), [gzclose_r](gz-file.md#gzclose_r), [gzclose_w](gz-file.md#gzclose_w) | 关闭 |

## 构建变体与宏

与 `zlib.h` 声明的函数相比，下列名称没有编译进默认 Linux 库：

| 名称 | 原因 |
| --- | --- |
| `gzopen_w` | 仅为 Windows（`_WIN32`）声明；`gzlib.c` 中的定义受宽字符选项控制 |
| `deflateInit`, `deflateInit2`, `inflateInit`, `inflateInit2`, `inflateBackInit` | 它们是 `zlib.h` 中的宏；使用头文件自身的版本字符串和 `sizeof(z_stream)` 调用 `deflateInit_`, `deflateInit2_`, `inflateInit_`, `inflateInit2_`, `inflateBackInit_` |
| 作为宏的 `gzgetc` | `zlib.h` 还把 `gzgetc` 定义为宏，直接读取缓冲区，缓冲区为空时调用函数 `gzgetc`；`gzgetc_` 是另一个导出函数，为向后兼容而保留 |

索引包含全部 95 个默认构建条目，以及单独列出的 Windows 条目 `gzopen_w`。[内部辅助函数契约](../internal-contracts.md)描述库内部使用的例程。

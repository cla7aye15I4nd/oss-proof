<!-- source-sha256: 5a31274ee8a2314e076ac1935867ce0044b467a1195005f0fb29aa1e48c065d9 -->
# zlib-ng

验证对象：zlib-ng `develop` 分支提交 `e591472c` 加二十二个补丁，按 zlib 兼容模式（`ZLIB_COMPAT`）构建为 x86_64 Linux LP64 库，使用通用 C
内核：每个分派函数（`adler32`、`crc32` 等）都运行其可移植 C 版本，不含 SIMD 代码。

## 构建配置

被验证的库以如下选项构建（其余选项保持默认值）：

```
-DZLIB_COMPAT=ON -DWITH_OPTIM=OFF -DWITH_CRC32_CHORBA=OFF -DWITH_RUNTIME_CPU_DETECTION=OFF
```

- `WITH_OPTIM=OFF` 去掉所有体系结构相关的源文件。
- `WITH_CRC32_CHORBA=OFF` 去掉 Chorba CRC-32 内核。若打开它并关闭运行时检测，`crc32` 与 `crc32_z` 会调用未翻译的
  `crc32_chorba`。
- `WITH_RUNTIME_CPU_DETECTION=OFF` 去掉函数表：每个分派调用都直接调用对应的通用 C 函数，Adler-32 函数调用
  `adler32_c`，CRC-32 函数调用 `crc32_braid`。

## 范围

- **`zlib.h` 每个公开函数的安全性：** 在严格 ISO C17 下无未定义行为、无内存错误，并且对头文件允许的每个输入都终止。
- **已声明的功能定理：** 版本与错误字符串、`zlibCompileFlags`、Adler-32 校验和及其合并、`crc32_combine*` 的拒绝值，
  以及 `compressBound` 的精确值。
- `deflate` 与 `inflate` 的**往返性质**。

## 当前已证明的内容

- 严格 ISO C17 运行时拒绝 `NULL + 0`、悬垂指针 `+ 0`、`NULL - NULL`、跨对象指针减法与 `memset(NULL, b, 0)`。
- `zlibVersion`、`zlibCompileFlags` 与 `zError` 安全且返回预期值。
- `adler32` 与 `adler32_z` 安全并计算缓冲区的 Adler-32 校验和，且如 `zlib.h` 所述，对任意长度的 `NULL`
  缓冲区返回 1；`adler32_combine` 与 `adler32_combine64`
  安全并正确合并两个校验和。
- `get_crc_table`、`crc32` 与 `crc32_z` 对每个可读缓冲区、缓冲区在内存中的每种对齐方式都安全；五个 `crc32_combine*`
  函数对每个参数都安全，并对负长度返回 0。
- `compressBound` 与 `compressBound_z` 安全并返回 `deflate_quick` 路径的精确上界。
- `gz*` 函数使用的两个内部分配辅助函数（`zcalloc` / `zcfree`、`zng_alloc_aligned` / `zng_free_aligned`）安全，
  且 `zng_alloc_aligned` 返回对齐的内存。
- 流式 `inflate*` 与 `inflateBack*` 函数、`uncompress*`、流式 `deflate*` 函数、单次调用 `compress*`
  函数，以及全部 `gz*` 文件函数（`gzopen`、`gzdopen`、读、写、`gzprintf`、定位、`gzclose` 等）安全。

本构建中 `zlib.h` 的每个公开函数都安全；往返性质尚未完成。`gzopen_w` 仅用于 Windows，不属于本构建。`zlib.h`
的每个公开函数都被列为已完成或未完成。

上述每个函数的翻译还在生成的输入上与按上述配置构建的真实 C 库进行比较。这类测试是翻译与 C 一致的证据，而不是证明。参见
[结论的状态](progress.html)、[前提与偏差](deviations.html) 与 [发现的问题](findings.html)。

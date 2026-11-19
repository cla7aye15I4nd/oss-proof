<!-- source-sha256: fd711213bc3c1299a9a63e8266c9f9ac587239a94e4fe72ba5bf55eba4bc8b71 -->
# 结论的状态

整体库验证状态：**未完成**。

| 领域 | 类别 | 状态 |
| --- | --- | --- |
| 严格 ISO C17 指针与 `memset` 未定义行为拒绝（运行时） | 运行时模型 | 完成 |
| `zlibVersion`、`zlibCompileFlags`、`zError`：安全性与返回值 | 公开 C 接口 | 完成 |
| `zcalloc` / `zcfree`、`zng_alloc_aligned` / `zng_free_aligned`：安全性与对齐 | 内部辅助函数 | 完成 |
| `adler32`、`adler32_z`：安全性 | 公开 C 接口 | 完成 |
| `adler32`、`adler32_z`：校验和值 | 公开 C 接口 | 未完成 |
| `adler32_combine`、`adler32_combine64`：安全性与合并值 | 公开 C 接口 | 完成 |
| `get_crc_table`、`crc32`、`crc32_z`：安全性 | 公开 C 接口 | 完成 |
| `crc32_combine`、`crc32_combine64`、`crc32_combine_gen`、`crc32_combine_gen64`、`crc32_combine_op`：安全性与拒绝值 | 公开 C 接口 | 完成 |
| `compressBound`：安全性与精确值 | 公开 C 接口 | 完成 |
| 流式 `deflate*` 安全性 | 公开 C 接口 | 未完成 |
| `inflateInit_`、`inflateInit2_`、`inflateUndermine`：安全性 | 公开 C 接口 | 完成 |
| 流式 `inflate*` 安全性（其他函数） | 公开 C 接口 | 未完成 |
| `inflateBack*` 安全性 | 公开 C 接口 | 未完成 |
| `compress`、`compress2` 安全性 | 公开 C 接口 | 未完成 |
| `uncompress`、`uncompress2`、`uncompress_z`、`uncompress2_z` 安全性 | 公开 C 接口 | 未完成 |
| `gz*` 文件函数安全性 | 公开 C 接口 | 未完成 |
| `deflate` / `inflate` 往返性质 | 功能 | 未完成 |

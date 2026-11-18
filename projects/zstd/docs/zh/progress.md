<!-- source-sha256: c3d8b68ee35c9d2bcfe31bf19eb3bfe7c29c9641c8c1a9b5387a05d408805beb -->
# 结论的状态

整体库验证状态：**未完成**。

| 领域 | 类别 | 状态 |
| --- | --- | --- |
| 严格 ISO C17 指针与 `memset` 未定义行为拒绝定理（`ZstdF.Runtime`） | 运行时模型 | 完成 |
| `ZSTD_decompressStream` 与 `ZSTD_DCtx` 生命周期安全性 | 公开 C 接口 | 未完成 |
| `ZSTD_decompress` 等单次解压函数安全性 | 公开 C 接口 | 未完成 |
| `ZSTD_DDict` 及外部字典/前缀借用安全性 | 公开 C 接口 | 未完成 |
| 帧检查及错误/版本查询函数安全性 | 公开 C 接口 | 未完成 |
| 压缩器（`lib/compress/`）与旧版 v0.1–v0.7 解码器 | 范围外 | 不在计划内 |

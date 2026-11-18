<!-- source-sha256: 6fa149204f34a25600adf644ff73237d057ef19fb9bf09134bcb425145f79cac -->
# 结论的状态

整体库验证状态：**未完成**。

| 领域 | 类别 | 状态 |
| --- | --- | --- |
| 严格 ISO C17 指针与 `memset` 未定义行为拒绝定理（`BrotliF.Runtime`） | 运行时模型 | 完成 |
| `BrotliDecoderDecompressStream` 流式状态机安全性 | 公开 C 接口 | 未完成 |
| `BrotliDecoderDecompress` 单次解压安全性 | 公开 C 接口 | 未完成 |
| `BrotliDecoderTakeOutput` 零拷贝借用有效性 | 公开 C 接口 | 未完成 |
| `BrotliDecoderCreateInstance` / `AttachDictionary` / `DestroyInstance` 安全性 | 公开 C 接口 | 未完成 |
| 编码器（`c/enc/`） | 范围外 | 不在计划内 |

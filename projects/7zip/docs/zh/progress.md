<!-- source-sha256: 284d1bff9600f8b51644d29ee5486e177d576410eeed7b469dd466add7cea668 -->
# 结论的状态

整体库验证状态：**未完成**。

| 领域 | 类别 | 状态 |
| --- | --- | --- |
| 严格 ISO C17 指针与 `memset` 未定义行为拒绝定理（`SevenZipF.Runtime`） | 运行时模型 | 完成 |
| `.7z` 文件夹有向无环图无环性与 `SzArEx` 固实缓存一致性（`SevenZipF.Model`） | 顶层模型 | 完成 |
| BCJ2 四流原地重叠不变量与区间解码边界（`SevenZipF.Model`） | 顶层模型 | 完成 |
| PPMd7 内存池分区与 `SplitBlock` 单元守恒（`SevenZipF.Model`） | 顶层模型 | 完成 |
| LZMA 快速循环前瞻余量与 LZMA2 控制字节状态守卫（`SevenZipF.Model`） | 顶层模型 | 完成 |
| `SzArEx_Open` / `SzArEx_Extract` / `SzArEx_Free` 翻译后 C 安全性 | 公开 C 接口 | 未完成 |
| `Bcj2Dec_Decode` 翻译后 C 安全性 | 公开 C 接口 | 未完成 |
| `Ppmd7_Alloc` / `Ppmd7_Init` / `Ppmd7_DecodeSymbol` 翻译后 C 安全性 | 公开 C 接口 | 未完成 |
| `LzmaDec_DecodeToBuf` / `Lzma2Dec_DecodeToBuf` 翻译后 C 安全性 | 公开 C 接口 | 未完成 |

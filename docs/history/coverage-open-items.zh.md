<!-- source-sha256: 57af93897c4bf8c39564059eed33d62f7779ea996503f98ea670471f758010cb -->
# 无故障覆盖：早先的未完成项（历史）

本页保存[进度](../progress.zh.md)“zlib.h 函数的无故障覆盖”一节中的编号列表“误计与未完成项”，内容是必需目标在 `bde170e9` 上通过验收之后的原文，除相对链接外未作改动。
这是历史记录：其中的状态（如 open、checked、“未完成”“已检查”）、工时、数字和日期反映各条目写作时的情况，不是当前状态。
当前状态和剩余工作只在[进度](../progress.zh.md)中。

#### 误计与未完成项

对完整文档化定义域没有已检查无故障定理的已文档化函数：

1. **inflateBack**：已登记（`inflate_back_sequence_safety`）。定义域按偏差行收窄：`inputBound < 2^48`，窗口与每个输入块都在堆字节块中。
2. **deflateCopy**：已登记。假设 `source ≠ dest`（偏差行）。
3. **inflateEnd**：已关闭。NULL、state 为 NULL、`End` 之后、初始化失败之后，以及复制失败的目标由 `Goal.inflate_refusal`（checked）覆盖。
4. **inflateCopy**：已关闭。不一致的源由 `Goal.inflate_refusal`（checked）覆盖。
5. **NULL 或不一致流的 refusal**：已关闭。`Goal.inflate_refusal` 与 `Goal.deflate_refusal`（checked）覆盖 `inflate`、`deflate`、`inflateEnd`、`inflateReset`、`inflateReset2`、`inflateGetDictionary`、`inflateSetDictionary`、`inflateCopy`、`deflateSetDictionary`、`deflateParams`、`deflateGetDictionary` 与 `deflateCopy`。这些目标与 `deflateGetDictionary_reject` 已登记。
6. **deflateParams、deflateSetDictionary、deflatePrime、deflateBound、deflateBound_z、inflateSync**：它们的逐函数安全目标（`Goal.*_safety`）已登记（dd73d9d2）。它们的功能性自身目标没有定理，不在计划内。
7. **adler32、adler32_z**：定义域比 zlib.h 更窄（NULL 只在 `len = 0` 时允许）。`len = 1` 是真实的 C 错误（偏差行）。`len ≥ 2` 的 NULL 安全但未证明。
8. **gz 函数**：`Goal.gz_sequence_safety` 已登记（`gz_sequence_safety_public`，无前提），连同其非空性目标。`gzgetc` 宏路径（审读 A1）和同一 fd 上的第二个句柄（审读 B1）都在目标之内。`NULL` 句柄由 `Goal.gz_refusal` 覆盖。
9. 相关，但不是函数：`Goal.deflate_initialisation_domain`（非空性）已登记（`deflate_initialisation_domain_public`，06cbfd06；在 dd73d9d2 登记）。`Goal.gz_initialisation_domain` 不是必需目标（见[范围](../progress.zh.md#scope)）。

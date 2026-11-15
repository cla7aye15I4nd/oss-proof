<!-- source-sha256: eab2c5a1799f96ee87c61dc421e6cbc0f64283d5a47d2fc38a2008fda1c68b13 -->
# 设计：模型、翻译与外部世界

本项目证明的命题，针对的是 C 的一份可执行 Lean 翻译。本节说明这份翻译由什么构成，它与 C 的联系在哪些地方依靠审查，以及规格是怎样布局的。本节不是状态报告；状态记在[进度](../progress.md)里。

必需的结果是安全结果。架构、翻译和外部 I/O 三页描述每个安全证明所依赖的东西。两页 API 模型描述功能性材料：这些材料保留下来，但不是安全结果所必需的。安全结果之后计划做一项功能结果，即默认 zlib 流的往返：它的条件形式已检查，完备性和无条件形式仍未证明（见[架构](architecture.md#the-layers)）。

先读[架构](architecture.md)。然后按你的问题选页面：

| 问题 | 阅读 |
| --- | --- |
| C、运行时、规格和证明怎样拼在一起？到底哪些东西是被信任的？ | [架构](architecture.md) |
| 一条 C 语句怎样翻译？我怎样把一份翻译与它的 C 对照？翻译中有哪些形式是采纳的规范化没有覆盖的？ | [翻译](translation.md) |
| 文件系统、`errno` 和 `printf` 在模型里是什么样子？ | [外部 I/O](external-io.md) |
| 安全目标在哪里？是什么把它们与功能目标分开？ | [规格的布局](safety-functional-split.md) |
| 不涉及堆的 API 关系描述什么（功能性）？ | [API 模型](api-model.md)、[各族详解](api-model-details.md) |
| 内部辅助函数的前置条件在哪里规定？ | [内部调用处的义务](../spec/internal-contracts.md) |
| 有哪些记录和指针种类？ | [生成的运行时结构定义](../runtime-schema.md) |

[API 手册](../spec/api/README.md)描述公开调用。[证明指南](../proof/README.md)解释各个证明。[检查](../checking/README.md)定义已检查、已登记和已验收这三个级别。要判断一个定理的适用范围，请读[安全性](../spec/safety.md)、[可信基础](../trusted-base.md)和[偏离记录](../deviations.md)。

[文档首页](../README.md)

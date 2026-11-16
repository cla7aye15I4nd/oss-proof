<!-- source-sha256: 219b38cb70553a7b39cf8cb3802829036e0600cda20d3977896922817d920ac1 -->
# 设计：模型、翻译与外部世界

本项目证明的命题，针对的是 C 的一份可执行 Lean 翻译。本节说明这份翻译由什么构成，以及它与 C 的联系在哪些地方依靠审查。

必需的结果是安全结论。架构、翻译和外部 I/O 三页描述每个安全证明所依赖的东西。两页 API 模型描述功能性材料，它们不是安全结论所必需的。默认 zlib 流的往返是一项功能结果，它未完成。它的一个有条件的形式有一条定理，内容见[架构](architecture.md#the-layers)。状态记在[进度](../progress.md)里。

先读[架构](architecture.md)。然后按你的问题选页面：

| 问题 | 阅读 |
| --- | --- |
| C、运行时、规格和证明怎样拼在一起？到底哪些东西是被信任的？ | [架构](architecture.md) |
| 一条 C 语句怎样翻译？我怎样把一份翻译与它的 C 对照？翻译中有哪些形式是采纳的规范化没有覆盖的？ | [翻译](translation.md) |
| 文件系统、`errno` 和 `printf` 在模型里是什么样子？ | [外部 I/O](external-io.md) |
| 安全目标与功能目标靠什么分开？安全目标是什么形式？ | [安全目标与功能目标](safety-functional-split.md) |
| 不涉及堆的 API 关系描述什么（功能性）？ | [API 模型](api-model.md)、[各族详解](api-model-details.md) |
| 内部辅助函数的前置条件在哪里规定？ | [内部调用处的义务](../spec/internal-contracts.md) |
| 有哪些记录和指针种类？ | [运行时结构定义](../runtime-schema.md) |

[API 手册](../spec/api/README.md)描述公开调用。[证明指南](../proof/README.md)解释各个证明。要判断一个定理的适用范围，请读[安全性](../spec/safety.md)、[可信基础](../trusted-base.md)和[偏离记录](../deviations.md)。

[文档首页](../README.md)

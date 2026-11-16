<!-- source-sha256: b4a34c7247d0da9f5c2e55035c9ad9c6b04a821b89d17525de5ec273d20a564d -->
# 规格的布局：安全与功能

必需的目标是安全目标。它们与功能目标分开存放，读者不读任何功能规格，就能看到全部必需的目标。本页说明每一类目标放在哪里，哪些导入规则把它们分开，以及这些规则怎样检查。形成这个布局的计划，连同它的步骤和状态，在一个[历史页面](../history/safety-functional-split-plan.md)中。

## 三个目录

| 目录 | 内容 | 是否必需 |
| --- | --- | --- |
| `ZlibF/Spec/Safety/` | 安全目标：在文档规定的定义域上，调用返回，没有 `Fault.ub`，没有 `Fault.outOfFuel`，只写自己的帧，不泄漏任何东西 | 是 |
| `ZlibF/Spec/Common/` | 两类目标共用的定义：调用、历史、帧、参数、平台前提，以及流和 gz 句柄的不变量（`Good`、`DGood`、`GzInv`）。`Common/Inflate/` 存放 inflate 表和快速解码器的不变量。这里没有关于公开函数的目标 | 它自己没有目标 |
| `ZlibF/Spec/Functional/` | 结果契约（`Goal.<function>`），包括 gzip 文件接口的结果契约；格式模型和 API 模型及它们的目标（`Format/`、`Api/`）；完整的序列契约（`Goal.inflate_sequence`、`Goal.deflate_sequence`、`Goal.inflate_back_sequence`、`Goal.gz_sequence`），它们把序列安全与功能子句合在一起。`Functional/Inflate/` 存放关于解码表和快速解码器、并且用到格式模型的命题 | 否，例外是 `Goal.compressBound` 和 `Goal.compressBound_z`（[见下文](#two-goals-per-public-function)） |

直接放在 `ZlibF/Spec/` 下的没有别的东西，只有 `Common.lean`，它导入 `Common/` 的每个模块。

关于公开函数的目标，不论在三个目录中的哪一个，Lean 名字都是 `ZlibF.Spec.Public.Goal.<name>`。目录表明种类；命名空间相同。清单文件 `tests/audit/public-api.json` 只列这个命名空间里的目标。

命名空间不跟随目录。`Public` 是现在的 `Common/` 目录原来的名字；其中的模块保留了命名空间 `ZlibF.Spec.Public`，所以没有目标或定理改名。`Functional/Api/` 下的模块的命名空间是 `ZlibF.Spec.Api`；来自 API 模型的 `Common/Parameters.lean` 也是这个命名空间。

`Spec/Functional/` 下有两组功能目标用的是别的命名空间。第一组是 `ZlibF.Spec.Api.Goal.<name>`，例如 `ZlibF.Spec.Api.Goal.roundtrip`。`tests/audit/goals.txt` 列出其中 20 个目标，都定义在 `Functional/Api/` 下：`Goals.lean` 里 17 个，`Inflate.lean` 里 1 个，`Concrete.lean` 里 2 个。`Concrete.lean` 里的两个（`compress_bound_value`、`compress2_z_first_alloc_failure`）说的是翻译后的 `compress.c`；其余 18 个是关于 API 模型的命题，不是关于翻译后的 C 的命题。第二组是记号格式的目标 `ZlibF.Spec.Token.Goal.<name>`（`Functional/Format/Token.lean`），它们是关于格式模型的命题。`tests/audit/goals.txt` 按完整名字列出每个目标；它还列出关于内部函数和关于不涉及堆的数学的命题，这些命题各自在所属模块的命名空间里。

默认 zlib 流的往返在这些目录里还没有目标定义。它的条件形式是一条定理，即 `ZlibF/Proof/public-deflate-inflate-roundtrip.lean` 中的 `deflate_inflate_roundtrip`。完备性和无条件的往返排在它之后（定理的内容见[架构](architecture.md#the-layers)；这项工作进行到哪一步，见[进度，范围](../progress.md#scope)）。

功能规格仍然参加构建。有[已登记](../checking/README.md)定理的功能目标接受完整的审计。没有已登记定理的功能目标报告为未证明，不使任何检查失败。形成这个布局时，没有削弱或删除任何命题：完整契约 `Goal.X` 是 `X` 的功能目标，安全目标写在它旁边。

## 导入规则

```mermaid
flowchart TD
  Safety["Spec/Safety：安全目标"] --> Common
  Functional["Spec/Functional：契约、Api、Format、序列"] --> Common
  Common["Spec/Common：调用、历史、帧、参数、不变量"] --> Base
  Base["Zlib 翻译、Runtime"]
  Safety -. "禁止，有检查" .-> Functional
  Common -. "禁止，有检查" .-> Safety
  Common -. "禁止，有检查" .-> Functional
```

关于 `ZlibF/Spec/` 下的模块有三条规则。每一条对直接导入成立，对经由任意一串其他模块的导入也成立。

1. `Spec/Safety/` 或 `Spec/Common/` 下的模块不导入 `Spec/Functional/` 下的模块。所以读必需目标的读者不用读任何功能规格。
2. `Spec/Common/` 下的模块不导入 `Spec/Safety/` 下的模块。Common 位于两类目标之下。
3. `ZlibF/Spec/` 下的模块不导入 `ZlibF/Proof/` 下的模块。所以一个目标的命题要在 `ZlibF/Spec/` 中读，也要在它提到的翻译、运行时和数学中读，但从不在证明模块中读。目标提到的、曾经放在证明模块里的定义现在在 `Spec/Common/` 中：`Good` 在 `InflateGood.lean`，`DGood` 在 `DeflateGood.lean`，`GzInv` 在 `GzInv.lean`。关于它们的引理留在证明模块里。

第四条规则说的是定义，不是导入。

4. 清单文件 `tests/audit/public-api.json` 列出的目标都不定义在 `Spec/Common/` 下。这样的目标在 `Spec/Safety/` 或 `Spec/Functional/` 下。

脚本 `scripts/check-spec-layers.py` 遍历导入关系，遇到违反规则的导入就失败。对规则 4，它读公共模块中每一个以 `def Goal.` 或 `abbrev Goal.` 开头的行，并在清单文件中查找完整的名字。如果直接放在 `ZlibF/Spec/` 下的东西不是这三个目录及其根导入文件，它也失败。它在快速关卡中运行（作业 `no-sorry`）。对这四条规则，它没有例外列表。

脚本还有一条规则，是关于 `ZlibF/Math/` 的：那里的模块不直接导入证明模块，例外是脚本中 `MATH_PROOF_IMPORTS` 列表里的导入。脚本记录说，这些 Math 模块从证明模块导入的是引理，不是定义。这张列表只能缩短：遇到不在列表里的导入，或者列表里的某个导入已经不存在，脚本都失败。规则 3 也覆盖这些 Math 模块：`ZlibF/Spec/` 下没有模块导入其中任何一个。列表的大小见[进度](../progress.md#ordered-next-work)。

关于导入，还有三点：

- `Spec/Common/` 中没有模块导入 gz 模型。gz 模式解码器和 `GzLooksGzip` 在 `Functional/Api/Gz.lean` 中；导入它的是 `Functional/GzState.lean`，`Common/GzState.lean` 不导入它。
- 安全目标需要的参数解码器（返回码、刷新值、窗口和封装的选择）在 `Common/Parameters.lean` 中，它什么也不导入。
- `Functional/Crc32ByteViews.lean` 属于功能部分，因为它的命题提到格式模型的 `crc32Update`。

## 每个公开函数两个目标

清单文件 `tests/audit/public-api.json` 给 `zlib.h` 的每个函数一个 `safety_goal` 和一个 `functional_goal`。[安全性，“目标在哪里”](../spec/safety.md#where-the-goals-are)为每个函数列出安全目标及其所在文件。安全目标有三种形式。

- **不带流的调用**（校验和、`zlibVersion`、`zlibCompileFlags`、`compress*`、`uncompress*`）：在文档规定的定义域上，调用无故障地返回，只写声明的调用者区域，存活块保持原样。
- **流函数**（inflate 族和 deflate 族）：每个函数一个目标。它陈述的是：在一个流的每个可达历史上，再调用一次这个函数；以及对 `NULL` 流或不一致的流的拒绝。四个初始化函数不需要历史：它们的目标覆盖 `zlib.h` 允许的每一次调用（`InitArguments`）。`Goal.inflate_refusal` 和 `Goal.deflate_refusal` 各用一个命题陈述若干函数的拒绝。
- **gzip 文件接口和 `inflateBack`**：同样是每个函数一个目标（`Safety/GzCalls.lean`、`Safety/Back.lean`）。每个目标把所属一族的序列目标（`Goal.gz_sequence_safety` 或 `Goal.inflate_back_sequence_safety`）的一个子句限制到一个函数上。它还带有这个函数的拒绝：对接受句柄的 gz 函数是 `NULL` 句柄；对 `inflateBack` 和 `inflateBackEnd` 是 `NULL` 流和状态为 `NULL` 的流记录，对 `inflateBackEnd` 还有 `zfree` 为 `NULL`。`Goal.inflateBackInit__safety` 与其他初始化目标一样，覆盖 `zlib.h` 允许的每一次调用。两个序列目标仍然是必需的。没有函数与别的函数共用安全目标：`scripts/verification.py` 中的 `SHARED_SAFETY_GOALS` 列表是空的。

清单文件中的特殊情况：

- `compressBound` 和 `compressBound_z` 把它们的完整契约写作安全目标。它们的翻译是纯函数，没有堆，也没有故障，所以单独的安全目标会按定义成立。
- 对 `zlib.h` 列为未文档化的函数，`safety_goal` 为 `null`；其中包括不在目标构建中的 `gzopen_w`。例外是 `gzvprintf`：它写的是 `Goal.gzvprintf_safety`，这个目标通过 `safety_goals` 列表成为必需。
- 四个 `uncompress*` 目标以 `_safe` 结尾；其他每个单函数安全目标都以 `_safety` 结尾。清单文件写出每个目标的全名，所以任何检查都不必去猜后缀。

流目标的强度取决于它的可达历史集合。四个非空性目标为每一族给出一个可达的见证，它们属于必需集合：`Goal.inflate_initialisation_domain`、`Goal.deflate_initialisation_domain`、`Goal.inflate_back_initialisation_domain` 和 `Goal.gz_sequence_nonvacuity`。`Goal.gz_initialisation_domain` 不是必需的：它陈述的是 `gzopen` 的功能契约，清单文件把它列在 `not_planned` 之下。

## 必需集合怎样检查

验收审计（`scripts/verification.py`）从清单文件读出必需集合：目标构建中每个有文档的函数的安全目标，加上 `safety_goals` 和 `nonvacuity_goals` 的各项。每个必需的目标都需要一个类型恰好是它的已登记定理，并且只用允许的公理。没有定理的必需目标必须写在清单文件的 `open_safety` 列表里，否则审计失败（有没有这样的目标，见[进度](../progress.md#scope)）。各登记表、必需集合和[防止悄悄删除的规则](../checking/goals.md#shrink-only-rules)，完整内容见[目标](../checking/goals.md)。

## 没有分开的部分

- 清单文件把 `Goal.compressBound` 和 `Goal.compressBound_z` 写作安全目标，它们在 `Functional/Queries.lean` 中。这是有意的设计（[见上文](#two-goals-per-public-function)）。
- 关于内部函数的命题不在清单文件里。其中不用格式模型的在 `Spec/Common/` 中（`ByteAddress.lean`、`Common/Inflate/`），用到格式模型的在 `Spec/Functional/` 中。它们也是 `Goal.<name>` 的形式，各自在所属模块的命名空间里。

[设计](README.md) · [文档首页](../README.md)

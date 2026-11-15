<!-- source-sha256: f436c3cc3b31b176c01a802523925f2ce6ea8eb67976e3384f3d5478ce5c2dcf -->
# 参与贡献

本页列出修改证明、翻译或文档的步骤，以及把已检查的结果变成已验收结果的步骤。所有命令都在仓库根目录运行。规则见 `AGENTS.md`。每项检查能证明什么，见[检查指南](README.md)。

这些命令取自工作流 `.github/workflows/lean.yml` 及其调用的脚本。写本页时，运行了第 4 步的三项脚本检查和第 6 步的站点命令；没有重新运行 Lean 构建和验收命令。

## 两个层级

- **已检查。** 定理在 `dev` 上，且该提交上快速关卡为绿。
- **已验收。** 定理还列在 `tests/audit/theorems.txt` 中，且验收套件在某个具名提交上全部通过。只有已验收的结论才是最终结论。

## 每次改动

1. 获取源码，包括上游子模块。如果克隆时没有带子模块，运行 `git submodule update --init zlib`。

   ```bash
   git clone --recurse-submodules <repository-url>
   ```

2. 从 `dev` 建分支工作。小步提交。按路径暂存文件。直接推送到 `dev`，或在快速关卡为绿后把拉取请求合并进 `dev`。不需要评审。

3. 构建库和审计工具。最多用四个并行任务，内存上限 16 GB。`crc32.c` 和 `inftrees.c` 的证明各需要 8 到 9 GB。

   ```bash
   lake build ZlibF zlibf-audit zlibf-span zlibf-proof-replay
   ```

4. 运行快速关卡的其余检查。

   ```bash
   scripts/check-sorry.sh
   python3 scripts/check-strlit.py
   python3 scripts/check-spec-layers.py
   lake env lean --run tests/audit/PartialCheck.lean
   grep -rnE '\b(native_decide|bv_decide|implemented_by)\b|^\s*axiom\b' ZlibF.lean ZlibF
   ```

   前三条不需要构建。第四条需要第 3 步的构建。`grep` 不应输出任何内容；它是 `lean.yml` 中那个模式的简化形式，后者还拒绝 `partial`、`unsafe`、`opaque` 和 `extern`。

5. 如果改了 `patches/`，检查每个补丁都能应用到固定版本的上游源码。

   ```bash
   rm -rf /tmp/zlib-verified && cp -r zlib /tmp/zlib-verified && rm -rf /tmp/zlib-verified/.git
   for p in patches/*.patch; do (cd /tmp/zlib-verified && git apply "$OLDPWD/$p"); done
   ```

6. 如果改了 `docs/`，构建并检查网站。使用 Python 3.12 或更新版本。

   ```bash
   python3 -m pip install -r docs/web/requirements.txt
   python3 docs/web/build.py
   python3 docs/web/check.py
   node --test docs/web/tests/*.test.mjs
   ```

7. 每个英文文档旁边都有中文对应文件 `*.zh.md`。`docs/` 之外的文件，其中文对应文件在 `docs/web/content/repository/` 下。中文文件第一行记录英文文件的 `source-sha256`。修改英文文件后，在同一个提交中更新中文内容并设置哈希。

   ```bash
   sha256sum docs/glossary.md
   ```

   没有 `sha256sum` 的系统上，`shasum -a 256` 输出相同的哈希。

   中文文件过时不会使构建失败。这时中文页面会显示提示，说明英文原文更新。

8. 推送到 `dev`。快速关卡（`build`、`no-sorry`）在每次推送和每个拉取请求上运行。它是合并的唯一关卡。如果某次推送使它失败，先修复它。

对翻译的修改还需要一个能发现旧行为的差分测试（见 `AGENTS.md`）。对目标或规范的修改单独成一个提交，并把反例保留在 `tests/verification/regressions/` 下。

## 在里程碑处

验收工作成批进行，不是每次改动都做。里程碑是指：`inflate` 证完，`deflate` 证完，某个序列目标证完，或者新增约二十个已检查的目标。登记需要什么、为什么需要，见[公开目标](goals.md#what-a-registration-needs)。

1. 给每个定理写文档字符串。已登记的定理若没有文档字符串，审计工具会拒绝。

2. 登记定理及其目标。把定理的完全限定名加入 `tests/audit/theorems.txt`，把目标的名称加入 `tests/audit/proved-goals.txt`，每行一个名称。如果目标列在 `tests/audit/public-api.json` 的 `open_safety` 中，删除那个条目。

3. 为每个新证明的公开函数添加证明变异，并在 `tests/audit/public-mutants.json` 中为它们建键。变异后的翻译必须无法通过检查，且错误位于该函数的证明中。格式和规则见[证明变异](proof-mutants.md)。可以先运行一个列表试一试：

   ```bash
   bash tests/audit/proofmut.sh tests/audit/proofmut/adler32.tsv
   ```

4. 检查清单。这一步需要子模块，不需要构建。

   ```bash
   python3 scripts/verification.py coverage
   ```

5. 重新生成进度视图，即 `docs/progress.md` 和 `docs/progress.zh.md` 中两个 `proof-progress` 标记之间的部分。它需要上面第 3 步的构建。

   ```bash
   python3 scripts/proof-progress.py
   python3 scripts/proof-progress.py --check
   ```

6. 运行审计和变异检查。两者都需要完整历史（浅克隆中先运行 `git fetch --unshallow`）和基准分支 `origin/main`。

   ```bash
   python3 scripts/verification.py specs
   python3 scripts/verification.py mutants
   ```

   第二条命令在一个进程中运行全部分片，需要很多小时。在 CI 中变异检查分二十个分片运行（`--shard-count 20 --shard-index N`）。

7. 运行差分测试：先普通运行，再让 C 在 sanitizer 下运行。

   ```bash
   ZLIB_SRC=$PWD/zlib bash tests/run.sh
   SAN=1 ZLIB_SRC=$PWD/zlib bash tests/run.sh
   ```

8. 在已推送的提交上运行验收套件：在 `dev` 上用手动触发启动 `lean` 工作流。第 4 到第 7 步是它可以在本地运行的部分；套件还运行审计工具的自测和差分测试框架的自测。

9. 套件全部通过后，把结果报告为已验收，并写明提交。此后 `main` 接收 `dev`。

没有运行过的检查，绝不能报告为通过。差分测试是忠实度的证据，不是证明。

## 删除或修改已登记的条目

已登记的定理、已证明的目标、变异引用或冻结的变异行如果消失或改变，审计会拒绝（见[只减不增规则](goals.md#shrink-only-rules)）。确实应当删除时，在同一个提交中向 `tests/audit/registry-removals.json` 添加带理由的条目。这个条目就是这次删除经过审查的记录。什么也不豁免的条目会被审计拒绝。

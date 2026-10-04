# 验证记录

以下记录来自 2026-10-03 对本版本的本地验证。上传前再次核对了
`povm-validation.json` 中的全部 1,447 个文件哈希，与上传版本一致。
该哈希表涵盖全部 Lean 证明源码、三个检查脚本、依赖配置及原中文说明；
新加的 GitHub 首页和本验证目录不在该历史哈希表内。

| 检查 | 结果 | 原始日志 |
| --- | --- | --- |
| `lake --fail-fast build ThomGame.Construction.PaperPOVMGap` | 通过 | [集成构建](povm-resumed-build-20261003-153950.log) |
| `lake --fail-fast build` | 通过 | [完整构建](povm-full-build.log) |
| `lake env lean scripts/CheckPOVM.lean` | 通过 | [POVM 连接检查](povm-check.log) |
| `lake env lean scripts/CheckMain.lean` | 通过 | [具体主定理检查](povm-main-check-20261003-153950.log) |
| `lake env lean scripts/AuditAxioms.lean` | 通过，17,942 个定理 | [全项目公理审计](povm-all-axioms.log) |

公理审计允许的基础公理仅为 `propext`、`Classical.choice`、`Quot.sound`。
`CheckPOVM.lean` 和 `CheckMain.lean` 会递归检查关键定理的公理依赖；
`AuditAxioms.lean` 会检查导入的所有项目定理，并在发现额外公理时失败。

[机器可读验证记录](povm-validation.json) 包含检查结果、固定依赖版本及源文件 SHA-256。
记录中的 Windows 绝对路径仅表示原验证环境的位置，不是构建依赖。
构建日志中的少量 `letI` / `haveI` 风格提示不影响成功结果。

本次验证覆盖一般 POVM 下的量子结论；精确经典值仍未形式化。

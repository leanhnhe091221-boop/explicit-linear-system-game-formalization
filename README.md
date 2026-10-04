# Explicit linear-system game: Lean formalization

本仓库保存显式线性系统博弈的独立 Lean 4 / mathlib 形式化，以及已经完成验证的
一般 POVM 与投影测量之间的语义连接。

最终入口为 [`ThomGame/Construction/PaperPOVMGap.lean`](ThomGame/Construction/PaperPOVMGap.lean)：

```lean
import ThomGame.Construction.PaperPOVMGap

#check ThomGame.Construction.paper_main_results_povm
```

该定理保留具体构造的中央元素非平凡性、一致近似平凡性，并在一般 POVM 定义下证明
`ωq = ωqa < 1 = ωqc`。有限维测量扩张允许扩大局部维数，并保持完整相关数组；
commuting 部分直接使用原有完美投影策略到 POVM 策略的包含关系。

本版本保留原有全部 1,429 个核心模块，另外增加 10 个语义连接模块。
精确经典值 `ωc = 1 - 1/4251456` 尚未形式化，不包含在上述已证明结论中。

## 构建

安装 elan 和 Git 后，在仓库根目录运行：

```sh
lake exe cache get
lake build
lake env lean scripts/CheckPOVM.lean
lake env lean scripts/CheckMain.lean
lake env lean scripts/AuditAxioms.lean
```

Lean 固定为 `v4.35.0-rc3`，mathlib 固定为
`16efc2c756299924184fe015f6384ad6538d42c7`，mathlib 是唯一直接 Lean 包依赖。

2026-10-03 的完整构建及上述检查均已通过。全项目公理审计覆盖 **17,942 个定理**，
仅允许 `propext`、`Classical.choice`、`Quot.sound`。

详细说明见 [中文说明](README.zh.md)；原始检查日志及已验证源码的 SHA-256 记录见
[验证记录](validation/README.md)。

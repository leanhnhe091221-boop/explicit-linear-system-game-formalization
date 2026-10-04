# Explicit linear-system game: Lean formalization

本仓库保存显式线性系统博弈的独立 Lean 4 / mathlib 形式化，以及已经完成验证的
一般 POVM 与投影测量之间的语义连接，并在原有证明之外补充两个数值推论。

最终入口为 [`ThomGame/Construction/PaperPOVMGap.lean`](ThomGame/Construction/PaperPOVMGap.lean)：

```lean
import ThomGame.Construction.PaperPOVMGap

#check ThomGame.Construction.paper_main_results_povm
```

该定理保留具体构造的中央元素非平凡性、一致近似平凡性，并在一般 POVM 定义下证明
`ωq = ωqa < 1 = ωqc`。有限维测量扩张允许扩大局部维数，并保持完整相关数组；
commuting 部分直接使用原有完美投影策略到 POVM 策略的包含关系。

数值推论入口为
[`ThomGame/Construction/PaperValueCorollaries.lean`](ThomGame/Construction/PaperValueCorollaries.lean)：

```lean
import ThomGame.Construction.PaperValueCorollaries

#check ThomGame.Construction.paper_classical_value_corollary
#check ThomGame.Construction.paper_quantum_gap_corollary
```

两个推论陈述

\[
\omega_c=1-\frac1{4251456},\qquad
0<2^{-2^{50003}}\le 1-\omega_q=\omega_{qc}-\omega_q\le\frac1{4251456}.
\]

这里的量子值使用一般 POVM；经典值允许共享随机性。推论没有额外的谱隙、证书或
定量估计假设，也没有局部维数上限。
原有 1,429 个核心模块及 10 个 POVM 连接模块均保持不变。
新增定量证明和证书的来源及核验方式见
[数值推论证明说明](validation/corollaries-proof-sources.md)。

## 构建

安装 elan 和 Git 后，在仓库根目录运行：

```sh
lake exe cache get
lake build
lake env lean scripts/CheckPOVM.lean
lake env lean scripts/CheckMain.lean
lake env lean scripts/CheckCorollaries.lean
lake env lean scripts/AuditAxioms.lean
```

Lean 固定为 `v4.35.0-rc3`，mathlib 固定为
`16efc2c756299924184fe015f6384ad6538d42c7`，mathlib 是唯一直接 Lean 包依赖。

全项目公理审计仅允许 `propext`、`Classical.choice`、`Quot.sound`。
证书数据已嵌入 Lean 源码，构建不需要 PDF、ZIP、Python、Mathematica 或在线附件。
当前版本已通过完整构建、两个数值推论及原主结论检查，并通过覆盖 19,331 个
项目定理的递归公理审计。

详细说明见 [中文说明](README.zh.md)；原始检查日志及已验证源码的 SHA-256 记录见
[验证记录](validation/README.md)。

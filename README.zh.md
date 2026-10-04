# 论文主结论的 Lean 形式化

这是可单独移动和构建的源码副本，保留原有全部 1,429 个核心模块、总入口和固定版本的
构建配置，并在外层加入一般 POVM 与投影测量之间的语义连接。证书数据已包含在 Lean
源码中，构建不需要原目录的论文附件、生成器或历史记录。

按手稿一般 POVM 定义陈述的量子主结论位于 `ThomGame/Construction/PaperPOVMGap.lean`：

```lean
import ThomGame.Construction.PaperPOVMGap

#check ThomGame.Construction.paper_main_results_povm
```

它证明指定构造上的 J 非平凡、所有正维数下的一致近似平凡性，以及
`ωq = ωqa < 1 = ωqc`，其中三个值允许任意 POVM。
原有 `PaperQuantumGap.lean` 中的投影测量版定理及全部核心证明保持不变。

新增的 `POVM.exists_projective_dilation` 对每个测量族构造一个与问题无关的固定
等距嵌入，并允许扩大有限局部维数。`FinitePOVMStrategy.exists_projective` 证明
整个相关数组与某个投影测量策略完全相同，因此量子相关集及其闭包、上确界均相同。
任意有限维复 Hilbert 空间的策略可通过 `FinitePOVMCoordinates.lean` 转到显式坐标空间。
commuting 部分只使用投影策略到 POVM 策略的包含关系和成功率不超过一，将原有完美策略转移过去。
新值的 Lean 名称为 `omegaQPOVM`、`omegaQaPOVM`、`omegaQcPOVM`。

## 构建与验证

需要安装 Lean 工具链管理器 elan 和 Git。在本目录执行：

```sh
lake exe cache get
lake build
lake env lean scripts/CheckPOVM.lean
lake env lean scripts/AuditAxioms.lean
lake env lean scripts/CheckMain.lean
```

首次运行会下载固定版本的依赖和 mathlib 编译缓存，生成 `.lake/`。
`lean-toolchain` 固定 Lean 为 `v4.35.0-rc3`，`lake-manifest.json` 固定依赖版本；
mathlib 提交为 `16efc2c756299924184fe015f6384ad6538d42c7`。

`AuditAxioms.lean` 审计全部项目定理的公理依赖，允许的基础公理仅有
`propext`、`Classical.choice`、`Quot.sound`。
`CheckMain.lean` 核对最终主定理、实际定义、具体参数及其应用。
`CheckPOVM.lean` 可独立核对新增语义连接及其公理依赖，不导入大型具体构造。

## 目录

```text
ThomGame/                 形式化源码及 Lean 证书数据
ThomGame.lean             全项目导入入口
lakefile.toml             构建配置
lake-manifest.json        依赖版本锁
lean-toolchain            Lean 版本
scripts/AuditAxioms.lean   公理审计
scripts/CheckMain.lean     主结论核对
scripts/CheckPOVM.lean     一般 POVM 与投影测量的语义连接核对
```

该证明针对 Lean 内定义的具体矩阵。原始数据文件解析器的内核验证、一般轮式嵌入
等独立扩展未计入已完成的主结论；正量子缺口的存在已证明，未计算具体数值。
手稿 Theorem 1.1 另含精确经典值 `ωc = 1 - 1/4251456`；这一项尚未形式化，
不包含在上述量子主结论中。

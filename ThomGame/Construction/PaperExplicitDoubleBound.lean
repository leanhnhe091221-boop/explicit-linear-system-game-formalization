module

public import ThomGame.Analysis.FiniteNoDriftExplicitDouble
public import ThomGame.Analysis.FiniteNoDriftRootWeakGap
public import ThomGame.Analysis.FiniteUCPShearGap

/-! Unconditional assembly of the explicit double-group obstruction estimate. -/

@[expose] public section
namespace ThomGame.Construction
open Analysis

theorem paper_explicit_double_bound : PaperExplicitDoubleBound := by
  intro d hd f hf
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hH := finiteNoDrift_double_H_weakGap f false paperExplicitDefect_pos.le hf
  have hN := finiteNoDrift_double_N_weakGap f false paperExplicitDefect_pos.le hf
  have hS := finiteUCP_double_shear_weakGap f paperExplicitDefect_pos.le hf false
  exact (finiteNoDrift_explicit_double_of_weakGaps f
    (CH := 10000000000) (CN := 10000000000) (CS := 1000000000)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hf hH hN hS).le

end ThomGame.Construction

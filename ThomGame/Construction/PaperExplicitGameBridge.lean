module

public import ThomGame.Construction.PaperGame
public import ThomGame.Quantum.ExplicitNearPerfectApproximation

/-! An explicit game-to-solution-group error estimate derived from the existing
spectral-cut proof. The conservative constant avoids changing its core estimates.
It does not, by itself, assert a quantitative obstruction for the double group. -/

@[expose] public section
namespace ThomGame.Construction

open Quantum Analysis

theorem paper_systemDensityBudget_le {ε : ℝ} (hε : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    systemDensityBudget (Fin 1417152) ε ≤ 10000000000000000 * Real.sqrt ε := by
  have he : ε ≤ Real.sqrt ε := by
    exact (Real.le_sqrt hε hε).mpr (by nlinarith)
  have htwo : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hscale : Real.sqrt (4251456 : ℝ) ≤ 3000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hmul : Real.sqrt 2 * Real.sqrt (4251456 : ℝ) ≤ 6000 :=
    (mul_le_mul htwo hscale (Real.sqrt_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hlarge : 3855973998919680 * ε ≤ 3855973998919680 * Real.sqrt ε :=
    mul_le_mul_of_nonneg_left he (by norm_num)
  have hroot : Real.sqrt 2 * Real.sqrt (4251456 : ℝ) * Real.sqrt ε ≤
      6000 * Real.sqrt ε := mul_le_mul_of_nonneg_right hmul (Real.sqrt_nonneg ε)
  unfold systemDensityBudget
  norm_num only [Fintype.card_fin, Nat.cast_ofNat]
  rw [Real.sqrt_mul (by norm_num)]
  nlinarith [Real.sqrt_nonneg ε]

theorem paper_densityBudget_le_quarterPower {ε : ℝ} (hε : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    2 * systemDensityBudget (Fin 1417152) ε ≤
      (10000000000 * Real.sqrt (Real.sqrt ε) / 9) ^ 2 := by
  have hb := paper_systemDensityBudget_le hε hε₁
  have hs := Real.sq_sqrt (Real.sqrt_nonneg ε)
  nlinarith [Real.sqrt_nonneg ε]

/-- A concrete fourth-root rate, for the entire paper solution presentation. -/
theorem paper_near_perfect_approximation_quarterPower {ε : ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (T : FiniteStrategy (Fin 1417152) (Fin 1889684) (Fin 3 → ZMod 2) (ZMod 2))
    (hT : 1 - ε ≤ paperGame.success T.correlation) :
    ∃ d : Nat, 0 < d ∧ ∃ f : MatrixAssignment (SolutionGroup.Generator (Fin 1889684)) d,
      IsApproxRepresentation (SolutionGroup.Paper.relators paperSystem)
        (10000000000 * Real.sqrt (Real.sqrt ε)) f ∧ f (FreeGroup.of none) = -1 := by
  exact paperSystem.near_perfect_approximation_explicit hε (by positivity)
    (paper_densityBudget_le_quarterPower hε.le hε₁) T hT

end ThomGame.Construction

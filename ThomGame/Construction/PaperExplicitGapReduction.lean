module

public import ThomGame.Construction.PaperExplicitGameBridge
public import ThomGame.Construction.PaperQuantitativeWheel
public import ThomGame.Construction.ExplicitGapConstants
public import ThomGame.Construction.PaperPOVMGap
public import ThomGame.Analysis.ExplicitHNNObstruction
public import ThomGame.Analysis.QuantitativeDoubleRestriction

/-! The explicit game gap follows from the separately stated quantitative double
obstruction. This file proves the entire conversion for the actual game, including
finite-dimensional dilation, the supremum, and conservative explicit constants. -/

@[expose] public section
namespace ThomGame.Construction

open Quantum Analysis

/-- The sole group-theoretic input to the explicit game-gap conversion. -/
def PaperExplicitDoubleBound : Prop :=
  ∀ d : ℕ, 0 < d → ∀ f : MatrixAssignment Double.Generator d,
    IsApproxRepresentation Double.relators paperExplicitDefect f →
      unitaryLength (f (FreeGroup.mk Double.obstructionWord)) ≤ 1 / 4

theorem paperExplicitDefect_le_conservative_reciprocal :
    paperExplicitDefect ≤ 1 / 1000000000000000000 := by
  have hexponent : (64 : ℕ) ≤ 2 ^ 50000 :=
    (show (64 : ℕ) ≤ 2 ^ 6 by norm_num).trans
      (pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (by decide : (6 : ℕ) ≤ 50000))
  have hpower : paperExplicitDefect ≤ (1 / 2 : ℝ) ^ 64 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hexponent
  exact hpower.trans (by norm_num)

theorem paperExplicitGap_quarterPower :
    Real.sqrt (Real.sqrt paperExplicitGap) = paperExplicitDefect ^ 2 := by
  rw [paperExplicitGap_eq_defect_pow_eight,
    show paperExplicitDefect ^ 8 = (paperExplicitDefect ^ 4) ^ 2 by ring,
    Real.sqrt_sq (by positivity),
    show paperExplicitDefect ^ 4 = (paperExplicitDefect ^ 2) ^ 2 by ring,
    Real.sqrt_sq (sq_nonneg _)]

theorem paper_no_nearperfect_of_double_bound (hD : PaperExplicitDoubleBound)
    (T : FiniteStrategy (Fin 1417152) (Fin 1889684) (Fin 3 → ZMod 2) (ZMod 2)) :
    paperGame.success T.correlation < 1 - paperExplicitGap := by
  by_contra hT
  obtain ⟨d, hd, f, hf, hJ⟩ := paper_near_perfect_approximation_quarterPower
    paperExplicitGap_pos paperExplicitGap_le_one T (le_of_not_gt hT)
  rw [paperExplicitGap_quarterPower] at hf
  let F := wheelLambdaAssignment (paperToWheelAssignment f)
  have hσ : 0 ≤ 10000000000 * paperExplicitDefect ^ 2 := by positivity
  have hF := paperToLambda_isApprox hσ f hf
  have hJF := paperToLambda_J_bound hσ f hf
  rw [hJ] at hJF
  have hsq : paperExplicitDefect ^ 2 ≤ paperExplicitDefect / 1000000000000000000 := by
    have h := mul_le_mul_of_nonneg_left paperExplicitDefect_le_conservative_reciprocal
      paperExplicitDefect_pos.le
    nlinarith
  have hcoeff : 28343040 * (10000000000 * paperExplicitDefect ^ 2) ≤ paperExplicitDefect := by
    nlinarith [paperExplicitDefect_pos]
  have hsmall := hD d hd (lambdaDoubleAssignment F)
    (isApprox_mono (lambdaDouble_isApprox F hF) hcoeff)
  rw [lambdaDouble_obstruction] at hsmall
  have hhnn := lambda_hnn_defect F hF
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have himpossible := unitary_hnn_bridge_inequality
    (F (FreeGroup.of (73 : Lambda.Generator))) (F (FreeGroup.mk Lambda.w))
    (F (FreeGroup.of (72 : Lambda.Generator)))
  have htotal : 240 * (10000000000 * paperExplicitDefect ^ 2) +
      28343040 * (10000000000 * paperExplicitDefect ^ 2) + 2 * (1 / 4 : ℝ) < 2 := by
    nlinarith [paperExplicitDefect_le_one]
  linarith

/-- Conditional conversion only: the quantitative double bound is an explicit hypothesis. -/
theorem paper_explicit_gap_of_double_bound (hD : PaperExplicitDoubleBound) :
    paperExplicitGap ≤ 1 - paperGame.omegaQ := by
  have hv : paperGame.omegaQ ≤ 1 - paperExplicitGap := by
    apply csSup_le (quantumCorrelations_nonempty.image paperGame.success)
    rintro _ ⟨p, ⟨T, rfl⟩, rfl⟩
    exact (paper_no_nearperfect_of_double_bound hD T).le
  linarith

theorem paper_explicit_povm_gap_of_double_bound (hD : PaperExplicitDoubleBound) :
    paperExplicitGap ≤ 1 - paperGame.omegaQPOVM := by
  rw [paperGame.omegaQPOVM_eq_omegaQ]
  exact paper_explicit_gap_of_double_bound hD

theorem paper_explicit_qa_gap_of_double_bound (hD : PaperExplicitDoubleBound) :
    paperExplicitGap ≤ 1 - paperGame.omegaQa := by
  rw [← paperGame.omegaQ_eq_omegaQa]
  exact paper_explicit_gap_of_double_bound hD

end ThomGame.Construction

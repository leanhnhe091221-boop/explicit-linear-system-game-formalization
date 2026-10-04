module

public import ThomGame.Analysis.MatrixUnitBallHausdorff
public import ThomGame.Analysis.MatrixFrameStabilizationBounds

/-!
# Retaining an original normalization in unit-ball estimates

The ambient matrix dimension can be different from either denominator.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator

theorem matrixHSUnitBallHausdorff_bound_rescale {n r s : Nat} [NeZero r]
    (hs : 0 < s) (A B : StarSubalgebra ℂ (CMatrix n)) {ε : ℝ} (hε : 0 ≤ ε)
    (hAB : ∀ X ∈ A, matrixOpNorm X ≤ 1 →
      ∃ Y ∈ B, matrixOpNorm Y ≤ 1 ∧ rectHSNorm s (X - Y) ≤ ε)
    (hBA : ∀ Y ∈ B, matrixOpNorm Y ≤ 1 →
      ∃ X ∈ A, matrixOpNorm X ≤ 1 ∧ rectHSNorm s (Y - X) ≤ ε) :
    matrixHSUnitBallHausdorff r A B ≤ Real.sqrt ((s : ℝ) / r) * ε := by
  apply matrixHSUnitBallHausdorff_le r A B (mul_nonneg (Real.sqrt_nonneg _) hε)
  · intro X hX hn
    obtain ⟨Y, hY, hYn, he⟩ := hAB X hX hn
    refine ⟨Y, hY, hYn, ?_⟩
    rw [rectHSNorm_rescale (NeZero.pos r) hs]
    exact mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _)
  · intro Y hY hn
    obtain ⟨X, hX, hXn, he⟩ := hBA Y hY hn
    refine ⟨X, hX, hXn, ?_⟩
    rw [rectHSNorm_rescale (NeZero.pos r) hs]
    exact mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _)

end ThomGame.Analysis

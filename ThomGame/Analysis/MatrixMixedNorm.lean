module

public import ThomGame.Analysis.FiniteMatrixHilbert
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The operator-to-trace norm of a matrix linear map

The domain carries the Euclidean operator norm; the separate codomain
type carries the normalized Hilbert--Schmidt norm. Compactness of the
matrix unit ball gives an actual maximizing contraction.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d]

noncomputable def matrixMapToHilbert (F : CMatrix d →ₗ[ℂ] CMatrix d) :
    CMatrix d →L[ℂ] FiniteMatrixHilbert d :=
  ((finiteMatrixHilbertEquiv d).toLinearMap.comp F).toContinuousLinearMap

@[simp] theorem matrixMapToHilbert_apply (F : CMatrix d →ₗ[ℂ] CMatrix d) (X : CMatrix d) :
    matrixMapToHilbert F X = finiteMatrixHilbertEquiv d (F X) := rfl

noncomputable def matrixMixedNorm (F : CMatrix d →ₗ[ℂ] CMatrix d) : ℝ := ‖matrixMapToHilbert F‖

theorem matrixMixedNorm_nonneg (F : CMatrix d →ₗ[ℂ] CMatrix d) : 0 ≤ matrixMixedNorm F := by
  unfold matrixMixedNorm
  exact norm_nonneg (matrixMapToHilbert F)

theorem hsNorm_apply_le_matrixMixedNorm (F : CMatrix d →ₗ[ℂ] CMatrix d) (X : CMatrix d) :
    hsNorm (F X) ≤ matrixMixedNorm F * matrixOpNorm X := by
  simpa only [matrixMixedNorm, matrixOpNorm, matrixMapToHilbert_apply, finiteMatrixHilbert_norm] using
    (matrixMapToHilbert F).le_opNorm X

theorem matrixMixedNorm_le (F : CMatrix d →ₗ[ℂ] CMatrix d) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ X, hsNorm (F X) ≤ C * matrixOpNorm X) : matrixMixedNorm F ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro X
  simpa only [matrixOpNorm, matrixMapToHilbert_apply, finiteMatrixHilbert_norm] using hF X

theorem matrixMixedNorm_le_of_unit_bound (F : CMatrix d →ₗ[ℂ] CMatrix d) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ X, matrixOpNorm X ≤ 1 → hsNorm (F X) ≤ C) : matrixMixedNorm F ≤ C := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro X hX
  simpa only [matrixMapToHilbert_apply, finiteMatrixHilbert_norm] using hF X hX.le

theorem exists_matrixMixedNorm_maximizer (F : CMatrix d →ₗ[ℂ] CMatrix d) :
    ∃ X : CMatrix d, matrixOpNorm X ≤ 1 ∧ hsNorm (F X) = matrixMixedNorm F := by
  obtain ⟨X, hX, hmax⟩ := (isCompact_closedBall (0 : CMatrix d) 1).exists_isMaxOn
    (Metric.nonempty_closedBall.mpr zero_le_one) (matrixMapToHilbert F).continuous.norm.continuousOn
  have hX' : matrixOpNorm X ≤ 1 := by simpa only [matrixOpNorm, Metric.mem_closedBall, dist_zero_right] using hX
  refine ⟨X, hX', le_antisymm ?_ ?_⟩
  · exact (hsNorm_apply_le_matrixMixedNorm F X).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hX' (matrixMixedNorm_nonneg F))
  · apply matrixMixedNorm_le_of_unit_bound F _ (hsNorm_nonneg _)
    intro Y hY
    have h := hmax (by simpa only [matrixOpNorm, Metric.mem_closedBall, dist_zero_right] using hY)
    simpa only [Set.mem_ofPred_eq, matrixMapToHilbert_apply, finiteMatrixHilbert_norm] using h

end ThomGame.Analysis

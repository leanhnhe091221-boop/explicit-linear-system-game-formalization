module

public import ThomGame.Analysis.MatrixCenterProjectionBound
public import ThomGame.Analysis.MatrixMixedNorm

/-!
# One-sided near inclusion and its exact mixed-norm formula

This is the finite-dimensional notion used in Thom (2.1). Distances
are expressed by actual witnesses in the target algebra. Orthogonal
projection and contractivity identify the error with ||(1-E_A)E_B||.
-/

@[expose] public section
namespace ThomGame.Analysis

variable {d : Nat}

def MatrixNearInclusion (B A : StarSubalgebra ℂ (CMatrix d)) (ε : ℝ) : Prop :=
  ∀ X : CMatrix d, X ∈ B → matrixOpNorm X ≤ 1 → ∃ Y ∈ A, hsNorm (X - Y) ≤ ε

variable [NeZero d]

noncomputable def matrixNearInclusionError (B A : StarSubalgebra ℂ (CMatrix d)) : ℝ :=
  matrixMixedNorm (matrixTraceProjection B - (matrixTraceProjection A).comp (matrixTraceProjection B))

theorem matrixNearInclusionError_nonneg (B A : StarSubalgebra ℂ (CMatrix d)) :
    0 ≤ matrixNearInclusionError B A := matrixMixedNorm_nonneg _

theorem matrixNearInclusionError_mem_bound (B A : StarSubalgebra ℂ (CMatrix d))
    {X : CMatrix d} (hX : X ∈ B) :
    hsNorm (X - matrixTraceProjection A X) ≤ matrixNearInclusionError B A * matrixOpNorm X := by
  have h := hsNorm_apply_le_matrixMixedNorm
    (matrixTraceProjection B - (matrixTraceProjection A).comp (matrixTraceProjection B)) X
  simpa only [LinearMap.sub_apply, LinearMap.comp_apply, matrixTraceProjection_eq_self B X hX,
    matrixNearInclusionError] using h

theorem exists_matrixNearInclusion_maximizer (B A : StarSubalgebra ℂ (CMatrix d)) :
    ∃ X : CMatrix d, X ∈ B ∧ matrixOpNorm X ≤ 1 ∧
      hsNorm (X - matrixTraceProjection A X) = matrixNearInclusionError B A := by
  obtain ⟨Y, hY, hmax⟩ := exists_matrixMixedNorm_maximizer
    (matrixTraceProjection B - (matrixTraceProjection A).comp (matrixTraceProjection B))
  exact ⟨matrixTraceProjection B Y, matrixTraceProjection_mem B Y,
    (matrixTraceProjection_matrixOpNorm_le B Y).trans hY, hmax⟩

theorem matrixNearInclusion_iff_error_le (B A : StarSubalgebra ℂ (CMatrix d)) (ε : ℝ) :
    MatrixNearInclusion B A ε ↔ matrixNearInclusionError B A ≤ ε := by
  constructor
  · intro h
    obtain ⟨X, hXB, hXnorm, hmax⟩ := exists_matrixNearInclusion_maximizer B A
    obtain ⟨Y, hYA, hY⟩ := h X hXB hXnorm
    rw [← hmax]
    exact (matrixTraceProjection_bestApproximation A X Y hYA).trans hY
  · intro h X hXB hXnorm
    refine ⟨matrixTraceProjection A X, matrixTraceProjection_mem A X, ?_⟩
    calc
      hsNorm (X - matrixTraceProjection A X) ≤ matrixNearInclusionError B A * matrixOpNorm X :=
        matrixNearInclusionError_mem_bound B A hXB
      _ ≤ matrixNearInclusionError B A * 1 :=
        mul_le_mul_of_nonneg_left hXnorm (matrixNearInclusionError_nonneg B A)
      _ = matrixNearInclusionError B A := mul_one _
      _ ≤ ε := h

end ThomGame.Analysis

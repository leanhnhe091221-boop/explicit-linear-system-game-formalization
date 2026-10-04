module

public import ThomGame.Analysis.MatrixProjectionSubrank
public import ThomGame.Analysis.RectangularCompressionTraceLoss
public import ThomGame.Analysis.MatrixProjectionRankBounds

/-! Relative Frobenius bounds become normalized HS bounds on the actual positive rank. -/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem rectHSNorm_projection_rank {d : Nat} {P : CMatrix d} (hP : IsStarProjection P) :
    rectHSNorm 1 P ^ 2 = (P.rank : ℝ) := by
  rw [rectHSNorm_projection_sq 1 hP, matrixTraceReal_projection_rank 1 hP]
  simp

theorem rectHSNorm_normalization_sq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : Nat) (X : Matrix ι κ ℂ) :
    rectHSNorm r X ^ 2 = rectHSNorm 1 X ^ 2 / r := by
  simp only [rectHSNorm_sq, Nat.cast_one, div_one]

theorem rectHSNorm_rank_le_of_relative {d : Nat} {P : CMatrix d}
    (hP : IsStarProjection P) (hP0 : P ≠ 0)
    {ι κ : Type*} [Fintype ι] [Fintype κ] (X : Matrix ι κ ℂ)
    {η : ℝ} (hη : 0 ≤ η) (hX : rectHSNorm 1 X ^ 2 ≤ η ^ 2 * rectHSNorm 1 P ^ 2) :
    rectHSNorm P.rank X ≤ η := by
  have hr : 0 < (P.rank : ℝ) := by exact_mod_cast matrixProjection_rank_pos hP hP0
  apply (sq_le_sq₀ (rectHSNorm_nonneg _ _) hη).mp
  rw [rectHSNorm_normalization_sq, div_le_iff₀ hr]
  simpa only [rectHSNorm_projection_rank hP] using hX

end ThomGame.Analysis

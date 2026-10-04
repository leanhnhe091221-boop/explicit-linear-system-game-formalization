module

public import ThomGame.Analysis.MatrixInclusionCells

/-!
# The scalar comparison on each nonzero inclusion cell

The two actual dimension equations imply r_j q_i/(s_j p_i) >= k_ji^2.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} (B C : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks B) (Q : MatrixSubalgebraStarBlocks C) (hBC : B ≤ C)

noncomputable def matrixInclusionScaleCoefficient (j : Fin Q.count) (i : Fin P.count) : ℝ :=
  ((Q.size j : ℝ) / matrixStarRepresentationMultiplicity C Q C.subtype j) *
    ((matrixStarRepresentationMultiplicity B P B.subtype i : ℝ) / P.size i)

theorem matrixInclusionScaleCoefficient_pos (j : Fin Q.count) (i : Fin P.count) :
    0 < matrixInclusionScaleCoefficient B C P Q j i := by
  exact mul_pos (div_pos (Nat.cast_pos.mpr (Q.size_pos j))
    (Nat.cast_pos.mpr (matrixStarRepresentationMultiplicity_pos C Q C.subtype Subtype.val_injective j)))
    (div_pos (Nat.cast_pos.mpr (matrixStarRepresentationMultiplicity_pos B P B.subtype Subtype.val_injective i))
      (Nat.cast_pos.mpr (P.size_pos i)))

theorem matrixInclusionScaleCoefficient_sq_lower (j : Fin Q.count) (i : Fin P.count) :
    (matrixInclusionMultiplicity B C P Q hBC j i : ℝ) ^ 2 ≤ matrixInclusionScaleCoefficient B C P Q j i := by
  have hp : (0 : ℝ) < P.size i := Nat.cast_pos.mpr (P.size_pos i)
  have hs : (0 : ℝ) < matrixStarRepresentationMultiplicity C Q C.subtype j :=
    Nat.cast_pos.mpr (matrixStarRepresentationMultiplicity_pos C Q C.subtype Subtype.val_injective j)
  have hr : (P.size i : ℝ) * matrixInclusionMultiplicity B C P Q hBC j i ≤ Q.size j := by
    exact_mod_cast matrixInclusionMultiplicity_size_bound B C P Q hBC j i
  have hq : (matrixStarRepresentationMultiplicity C Q C.subtype j : ℝ) *
      matrixInclusionMultiplicity B C P Q hBC j i ≤ matrixStarRepresentationMultiplicity B P B.subtype i := by
    exact_mod_cast matrixInclusionMultiplicity_multiplicity_bound B C P Q hBC j i
  rw [matrixInclusionScaleCoefficient, div_mul_div_comm]
  apply (le_div_iff₀ (mul_pos hs hp)).mpr
  have h := mul_le_mul hr hq
    (mul_nonneg hs.le (Nat.cast_nonneg _)) (Nat.cast_nonneg (Q.size j))
  nlinarith only [h]

include hBC in
theorem matrixInclusionScaleCoefficient_one_le (j : Fin Q.count) (i : Fin P.count)
    (hne : matrixInclusionCell B C P Q j i ≠ 0) : 1 ≤ matrixInclusionScaleCoefficient B C P Q j i := by
  have hk : 0 < matrixInclusionMultiplicity B C P Q hBC j i :=
    Nat.pos_of_ne_zero (fun hz => hne ((matrixInclusionCell_zero_iff B C P Q hBC j i).mpr hz))
  have hk' : (1 : ℝ) ≤ matrixInclusionMultiplicity B C P Q hBC j i := by exact_mod_cast hk
  have h := matrixInclusionScaleCoefficient_sq_lower B C P Q hBC j i
  nlinarith only [hk', h]

end ThomGame.Analysis

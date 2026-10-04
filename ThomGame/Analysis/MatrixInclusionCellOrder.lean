module

public import ThomGame.Analysis.MatrixInclusionCellAlgebra
public import ThomGame.Analysis.MatrixInclusionScaleTrace

/-!
# Order, trace, and Hilbert--Schmidt geometry of joint cell scalars
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} (B C : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks B) (Q : MatrixSubalgebraStarBlocks C) (hBC : B ≤ C)

theorem matrixInclusionCell_row_sum (j : Fin Q.count) :
    ∑ i, matrixInclusionCell B C P Q j i = matrixStarBlockSupport C Q j := by
  simp only [matrixInclusionCell, ← Matrix.mul_sum, matrixStarBlockSupport_sum, Matrix.mul_one]

theorem matrixInclusionCell_column_sum (i : Fin P.count) :
    ∑ j, matrixInclusionCell B C P Q j i = matrixStarBlockSupport B P i := by
  simp only [matrixInclusionCell, ← Matrix.sum_mul, matrixStarBlockSupport_sum, Matrix.one_mul]

include hBC in
theorem matrixInclusionCellScalar_nonneg (c : Fin Q.count → Fin P.count → ℝ)
    (hc : ∀ j i, 0 ≤ c j i) : 0 ≤ matrixInclusionCellScalar B C P Q c := by
  rw [matrixInclusionCellScalar_sum]
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro i _
  exact smul_nonneg (by exact_mod_cast hc j i) (matrixInclusionCell_projection B C P Q hBC j i).nonneg

include hBC in
theorem matrixInclusionCellScalar_mono {a b : Fin Q.count → Fin P.count → ℝ}
    (hab : ∀ j i, a j i ≤ b j i) :
    matrixInclusionCellScalar B C P Q a ≤ matrixInclusionCellScalar B C P Q b := by
  apply sub_nonneg.mp
  rw [matrixInclusionCellScalar_sub]
  exact matrixInclusionCellScalar_nonneg B C P Q hBC _ (fun j i => sub_nonneg.mpr (hab j i))

include hBC in
theorem matrixInclusionCellScalar_posDef {a : Fin Q.count → Fin P.count → ℝ}
    (ha : ∀ j i, 0 < a j i) : (matrixInclusionCellScalar B C P Q a).PosDef :=
  (Matrix.nonneg_iff_posSemidef.mp
    (matrixInclusionCellScalar_nonneg B C P Q hBC a (fun j i => (ha j i).le))).posDef_iff_isUnit.mpr
      (matrixInclusionCellScalar_isUnit B C P Q hBC a (fun j i => ne_of_gt (ha j i)))

include hBC in
theorem matrixInclusionCellScalar_mem (c : Fin Q.count → Fin P.count → ℝ) :
    matrixInclusionCellScalar B C P Q c ∈ C := by
  rw [matrixInclusionCellScalar_sum]
  apply C.sum_mem
  intro j _
  apply C.sum_mem
  intro i _
  exact C.smul_mem (C.mul_mem (matrixStarBlockSupport_mem C Q j) (hBC (matrixStarBlockSupport_mem B P i))) _

include hBC in
theorem matrixInclusionCellScalar_commutes (c : Fin Q.count → Fin P.count → ℝ)
    (X : CMatrix d) (hX : X ∈ B) : Commute (matrixInclusionCellScalar B C P Q c) X := by
  apply matrixPartitionScalarSum_commute
  intro u
  exact (matrixStarBlockSupport_commutes C Q u.1 X (hBC hX)).mul_left
    (matrixStarBlockSupport_commutes B P u.2 X hX)

include hBC in
theorem matrixInclusionCellScalar_star (c : Fin Q.count → Fin P.count → ℝ) :
    star (matrixInclusionCellScalar B C P Q c) = matrixInclusionCellScalar B C P Q c := by
  simp only [matrixInclusionCellScalar_sum, star_sum, star_smul, Complex.star_def, Complex.conj_ofReal,
    fun j i => (matrixInclusionCell_projection B C P Q hBC j i).isSelfAdjoint.star_eq]

theorem matrixInclusionCellScalar_trace (r : Nat) (c : Fin Q.count → Fin P.count → ℝ) :
    matrixTraceReal r (matrixInclusionCellScalar B C P Q c) =
      ∑ j, ∑ i, c j i * matrixTraceReal r (matrixInclusionCell B C P Q j i) := by
  simp only [matrixInclusionCellScalar_sum, matrixTraceReal_sum, matrixTraceReal_ofReal_smul]

include hBC in
theorem matrixInclusionCellScalar_hsNorm_sq (r : Nat) (c : Fin Q.count → Fin P.count → ℝ) :
    rectHSNorm r (matrixInclusionCellScalar B C P Q c) ^ 2 =
      ∑ j, ∑ i, (c j i) ^ 2 * matrixTraceReal r (matrixInclusionCell B C P Q j i) := by
  rw [← matrixTraceReal_gram]
  change matrixTraceReal r (star (matrixInclusionCellScalar B C P Q c) * matrixInclusionCellScalar B C P Q c) = _
  rw [matrixInclusionCellScalar_star B C P Q hBC, matrixInclusionCellScalar_mul B C P Q hBC,
    matrixInclusionCellScalar_trace]
  simp only [Pi.mul_apply, pow_two]

end ThomGame.Analysis

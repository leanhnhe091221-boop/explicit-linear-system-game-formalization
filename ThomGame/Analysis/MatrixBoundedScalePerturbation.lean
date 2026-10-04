module

public import ThomGame.Analysis.MatrixBoundedScaleCells

/-!
# Uniform bounded-scale perturbation in the original matrix trace

The positive regularizing matrix may have arbitrarily ill-conditioned
eigenvalues. Only relative changes of the central scales enter the bound.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} (B C : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks B) (Q : MatrixSubalgebraStarBlocks C) (hBC : B ≤ C)

include hBC in
theorem matrixBoundedScale_cellPerturbation_sq (r : Nat)
    (a b s : Fin Q.count → Fin P.count → ℝ)
    (ha : ∀ j i, 0 < a j i) (hb : ∀ j i, 0 < b j i) (hs : ∀ j i, 0 < s j i) :
    rectHSNorm r (matrixBoundedScale (matrixInclusionCellScalar B C P Q a) (matrixInclusionCellScalar B C P Q s) -
      matrixBoundedScale (matrixInclusionCellScalar B C P Q b) (matrixInclusionCellScalar B C P Q s)) ^ 2 ≤
      ∑ j, ∑ i, |a j i / b j i - 1| * matrixTraceReal r (matrixInclusionCell B C P Q j i) := by
  rw [matrixBoundedScale_cellFormula B C P Q hBC a s ha hs,
    matrixBoundedScale_cellFormula B C P Q hBC b s hb hs, matrixInclusionCellScalar_sub,
    matrixInclusionCellScalar_hsNorm_sq B C P Q hBC]
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (matrixTraceReal_nonneg r (matrixInclusionCell_projection B C P Q hBC j i).nonneg)
  simpa only [Pi.sub_apply, sq_abs] using boundedScaleScalar_abs_sub_sq_le_ratio (ha j i) (hb j i) (hs j i)

include hBC in
theorem matrixBoundedScale_targetPerturbation_sq (r : Nat)
    (a b : Fin Q.count → ℝ) (s : Fin P.count → ℝ)
    (ha : ∀ j, 0 < a j) (hb : ∀ j, 0 < b j) (hs : ∀ i, 0 < s i) :
    rectHSNorm r (matrixBoundedScale (matrixStarBlockScalar C Q a) (matrixStarBlockScalar B P s) -
      matrixBoundedScale (matrixStarBlockScalar C Q b) (matrixStarBlockScalar B P s)) ^ 2 ≤
      ∑ j, |a j / b j - 1| * matrixTraceReal r (matrixStarBlockSupport C Q j) := by
  have he := matrixBoundedScale_cellPerturbation_sq B C P Q hBC r
    (fun j _ => a j) (fun j _ => b j) (fun _ i => s i)
    (fun j _ => ha j) (fun j _ => hb j) (fun _ i => hs i)
  simpa only [matrixInclusionCellScalar_source, matrixInclusionCellScalar_target,
    ← Finset.mul_sum, ← matrixTraceReal_sum, matrixInclusionCell_row_sum] using he

include hBC in
theorem matrixBoundedScale_targetPerturbation_rank_bound (r : Nat)
    (a b : Fin Q.count → ℝ) (s : Fin P.count → ℝ)
    (ha : ∀ j, 0 < a j) (hb : ∀ j, 0 < b j) (hs : ∀ i, 0 < s i) :
    rectHSNorm r (matrixBoundedScale (matrixStarBlockScalar C Q a) (matrixStarBlockScalar B P s) -
      matrixBoundedScale (matrixStarBlockScalar C Q b) (matrixStarBlockScalar B P s)) ^ 2 ≤
      (∑ j, (Q.size j : ℝ) * matrixStarRepresentationMultiplicity C Q C.subtype j * |a j / b j - 1|) / r := by
  have he := matrixBoundedScale_targetPerturbation_sq B C P Q hBC r a b s ha hb hs
  apply he.trans_eq
  simp only [matrixStarBlockSupport_trace, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

end ThomGame.Analysis

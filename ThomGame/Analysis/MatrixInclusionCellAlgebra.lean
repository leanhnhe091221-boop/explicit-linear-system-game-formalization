module

public import ThomGame.Analysis.MatrixInclusionScaleRatio

/-!
# The commutative algebra of the actual joint central cells
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} (B C : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks B) (Q : MatrixSubalgebraStarBlocks C) (hBC : B ≤ C)

include hBC in
theorem matrixInclusionCell_mul (j l : Fin Q.count) (i k : Fin P.count) :
    matrixInclusionCell B C P Q j i * matrixInclusionCell B C P Q l k =
      (matrixStarBlockSupport C Q j * matrixStarBlockSupport C Q l) *
        (matrixStarBlockSupport B P i * matrixStarBlockSupport B P k) := by
  unfold matrixInclusionCell
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (matrixStarBlockSupport B P i),
    (matrixInclusion_supports_commute B C P Q hBC l i).eq.symm]
  simp only [Matrix.mul_assoc]

include hBC in
theorem matrixInclusionCell_orthogonal :
    Pairwise (fun (u v : Fin Q.count × Fin P.count) =>
      matrixInclusionCell B C P Q u.1 u.2 * matrixInclusionCell B C P Q v.1 v.2 = 0) := by
  rintro ⟨j, i⟩ ⟨l, k⟩ h
  rw [matrixInclusionCell_mul B C P Q hBC]
  by_cases hj : j = l
  · have hi : i ≠ k := by intro hi; exact h (Prod.ext hj hi)
    rw [matrixStarBlockSupport_orthogonal B P hi, Matrix.mul_zero]
  · rw [matrixStarBlockSupport_orthogonal C Q hj, Matrix.zero_mul]

noncomputable def matrixInclusionCellScalar (c : Fin Q.count → Fin P.count → ℝ) : CMatrix d :=
  matrixPartitionScalarSum (fun u : Fin Q.count × Fin P.count => matrixInclusionCell B C P Q u.1 u.2)
    (fun u => (c u.1 u.2 : ℂ))

theorem matrixInclusionCellScalar_sum (c : Fin Q.count → Fin P.count → ℝ) :
    matrixInclusionCellScalar B C P Q c = ∑ j, ∑ i, (c j i : ℂ) • matrixInclusionCell B C P Q j i := by
  simp only [matrixInclusionCellScalar, matrixPartitionScalarSum, Fintype.sum_prod_type]

theorem matrixInclusionCellScalar_one : matrixInclusionCellScalar B C P Q (fun _ _ => 1) = 1 := by
  simpa only [matrixInclusionCellScalar_sum, Complex.ofReal_one, one_smul] using
    matrixInclusionCell_sum B C P Q

theorem matrixInclusionCellScalar_add (a b : Fin Q.count → Fin P.count → ℝ) :
    matrixInclusionCellScalar B C P Q a + matrixInclusionCellScalar B C P Q b =
      matrixInclusionCellScalar B C P Q (a + b) := by
  simp only [matrixInclusionCellScalar_sum, Pi.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]

theorem matrixInclusionCellScalar_sub (a b : Fin Q.count → Fin P.count → ℝ) :
    matrixInclusionCellScalar B C P Q a - matrixInclusionCellScalar B C P Q b =
      matrixInclusionCellScalar B C P Q (a - b) := by
  simp only [matrixInclusionCellScalar_sum, Pi.sub_apply, Complex.ofReal_sub, sub_smul, Finset.sum_sub_distrib]

include hBC in
theorem matrixInclusionCellScalar_mul (a b : Fin Q.count → Fin P.count → ℝ) :
    matrixInclusionCellScalar B C P Q a * matrixInclusionCellScalar B C P Q b =
      matrixInclusionCellScalar B C P Q (a * b) := by
  have he := matrixPartitionScalarSum_mul
    (fun u : Fin Q.count × Fin P.count => matrixInclusionCell B C P Q u.1 u.2)
    (fun u => matrixInclusionCell_projection B C P Q hBC u.1 u.2)
    (matrixInclusionCell_orthogonal B C P Q hBC)
    (fun u => (a u.1 u.2 : ℂ)) (fun u => (b u.1 u.2 : ℂ))
  refine he.trans ?_
  change matrixPartitionScalarSum (fun u : Fin Q.count × Fin P.count => matrixInclusionCell B C P Q u.1 u.2)
      ((fun u => (a u.1 u.2 : ℂ)) * (fun u => (b u.1 u.2 : ℂ))) =
    matrixPartitionScalarSum (fun u : Fin Q.count × Fin P.count => matrixInclusionCell B C P Q u.1 u.2)
      (fun u => ((a * b) u.1 u.2 : ℂ))
  apply congrArg
  funext u
  simp only [Pi.mul_apply, Complex.ofReal_mul]

include hBC in
theorem matrixInclusionCellScalar_inverse (a : Fin Q.count → Fin P.count → ℝ)
    (ha : ∀ j i, a j i ≠ 0) :
    (matrixInclusionCellScalar B C P Q a)⁻¹ =
      matrixInclusionCellScalar B C P Q (fun j i => (a j i)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [matrixInclusionCellScalar_mul B C P Q hBC]
  have he : a * (fun j i => (a j i)⁻¹) = fun _ _ => 1 := by
    funext j i
    exact mul_inv_cancel₀ (ha j i)
  rw [he, matrixInclusionCellScalar_one]

include hBC in
theorem matrixInclusionCellScalar_isUnit (a : Fin Q.count → Fin P.count → ℝ)
    (ha : ∀ j i, a j i ≠ 0) : IsUnit (matrixInclusionCellScalar B C P Q a) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨matrixInclusionCellScalar B C P Q (fun j i => (a j i)⁻¹), ?_⟩
  rw [matrixInclusionCellScalar_mul B C P Q hBC]
  have he : a * (fun j i => (a j i)⁻¹) = fun _ _ => 1 := by
    funext j i
    exact mul_inv_cancel₀ (ha j i)
  rw [he, matrixInclusionCellScalar_one]

theorem matrixInclusionCellScalar_source (a : Fin P.count → ℝ) :
    matrixInclusionCellScalar B C P Q (fun _ i => a i) = matrixStarBlockScalar B P a := by
  have he := matrixInclusionBlockScalars_product B C P Q (fun _ => 1) a
  simpa only [matrixInclusionCellScalar_sum, matrixStarBlockScalar_one, one_mul] using he.symm

theorem matrixInclusionCellScalar_target (a : Fin Q.count → ℝ) :
    matrixInclusionCellScalar B C P Q (fun j _ => a j) = matrixStarBlockScalar C Q a := by
  have he := matrixInclusionBlockScalars_product B C P Q a (fun _ => 1)
  simpa only [matrixInclusionCellScalar_sum, matrixStarBlockScalar_one, mul_one] using he.symm

end ThomGame.Analysis

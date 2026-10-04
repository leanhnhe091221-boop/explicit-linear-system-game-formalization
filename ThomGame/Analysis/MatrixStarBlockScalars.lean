module

public import ThomGame.Analysis.MatrixStarBlockSupports
public import ThomGame.Analysis.MatrixPartitionScalarAlgebra

/-!
# Positive central scalars on the actual simple blocks

Multiplication and inversion are coordinatewise, and all operators
remain in the original matrix subalgebra.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} (A : StarSubalgebra ℂ (CMatrix d)) (P : MatrixSubalgebraStarBlocks A)

noncomputable def matrixStarBlockScalar (c : Fin P.count → ℝ) : CMatrix d :=
  matrixPartitionScalarSum (matrixStarBlockSupport A P) (fun i => (c i : ℂ))

theorem matrixStarBlockScalar_mem (c : Fin P.count → ℝ) : matrixStarBlockScalar A P c ∈ A := by
  dsimp only [matrixStarBlockScalar, matrixPartitionScalarSum]
  apply A.sum_mem
  intro i _
  exact A.smul_mem (matrixStarBlockSupport_mem A P i) (c i : ℂ)

theorem matrixStarBlockScalar_commutes (c : Fin P.count → ℝ) (X : CMatrix d) (hX : X ∈ A) :
    Commute (matrixStarBlockScalar A P c) X :=
  matrixPartitionScalarSum_commute _ _ (fun i => matrixStarBlockSupport_commutes A P i X hX)

theorem matrixStarBlockScalar_nonneg (c : Fin P.count → ℝ) (hc : ∀ i, 0 ≤ c i) :
    0 ≤ matrixStarBlockScalar A P c := by
  dsimp only [matrixStarBlockScalar, matrixPartitionScalarSum]
  apply Finset.sum_nonneg
  intro i _
  exact smul_nonneg (by exact_mod_cast hc i) (matrixStarBlockSupport_projection A P i).nonneg

theorem matrixStarBlockScalar_one : matrixStarBlockScalar A P (fun _ => 1) = 1 := by
  simpa only [matrixStarBlockScalar, matrixPartitionScalarSum, Complex.ofReal_one, one_smul]
    using matrixStarBlockSupport_sum A P

theorem matrixStarBlockScalar_mul (c b : Fin P.count → ℝ) :
    matrixStarBlockScalar A P c * matrixStarBlockScalar A P b = matrixStarBlockScalar A P (c * b) := by
  rw [matrixStarBlockScalar, matrixStarBlockScalar, matrixPartitionScalarSum_mul _
    (matrixStarBlockSupport_projection A P) (matrixStarBlockSupport_orthogonal A P)]
  simp only [matrixStarBlockScalar, Pi.mul_apply, Complex.ofReal_mul]
  rfl

theorem matrixStarBlockScalar_inverse (c : Fin P.count → ℝ) (hc : ∀ i, c i ≠ 0) :
    (matrixStarBlockScalar A P c)⁻¹ = matrixStarBlockScalar A P (fun i => (c i)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [matrixStarBlockScalar_mul]
  have he : c * (fun i => (c i)⁻¹) = fun _ => 1 := by
    funext i
    exact mul_inv_cancel₀ (hc i)
  rw [he, matrixStarBlockScalar_one]

theorem matrixStarBlockScalar_isUnit (c : Fin P.count → ℝ) (hc : ∀ i, c i ≠ 0) :
    IsUnit (matrixStarBlockScalar A P c) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨matrixStarBlockScalar A P (fun i => (c i)⁻¹), ?_⟩
  rw [matrixStarBlockScalar_mul]
  have he : c * (fun i => (c i)⁻¹) = fun _ => 1 := by funext i; exact mul_inv_cancel₀ (hc i)
  rw [he, matrixStarBlockScalar_one]

theorem matrixStarBlockScalar_block (c : Fin P.count → ℝ) (i : Fin P.count) :
    matrixStarBlockSupport A P i * matrixStarBlockScalar A P c = (c i : ℂ) • matrixStarBlockSupport A P i :=
  matrixPartitionScalarSum_block_left _ (matrixStarBlockSupport_projection A P)
    (matrixStarBlockSupport_orthogonal A P) _ i

end ThomGame.Analysis

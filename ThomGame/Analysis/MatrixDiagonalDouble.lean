module

public import ThomGame.Analysis.MatrixBlockReindex
public import ThomGame.Analysis.MatrixResolventFamilies

/-!
# Actual doubled diagonal matrices

The diagonal doubling map preserves the algebra and adjoint. Its
positive resolvent is the double of the original positive resolvent,
as proved from the actual inverse identities.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable (d : Nat)

noncomputable def matrixDiagonalDouble : CMatrix d →⋆ₐ[ℝ] CMatrix (d + d) where
  toFun A := matrixDoubleBlocks d A 0 0 A
  map_one' := matrixDoubleBlocks_one d
  map_zero' := by simp [matrixDoubleBlocks]
  map_mul' A B := by
    rw [matrixDoubleBlocks_mul]
    simp only [mul_zero, zero_mul, add_zero, zero_add]
  map_add' A B := by
    dsimp [matrixDoubleBlocks]
    rw [← map_add, Matrix.fromBlocks_add, add_zero]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    have he : Matrix.fromBlocks (c • (1 : CMatrix d)) 0 0 (c • (1 : CMatrix d)) =
        c • (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ) := by
      rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]
    change matrixSumReindex d _ = _
    rw [he, map_smul, map_one]
  map_star' A := by rw [matrixDoubleBlocks_star]; simp only [star_zero]

@[simp] theorem matrixDiagonalDouble_apply (A : CMatrix d) :
    matrixDiagonalDouble d A = matrixDoubleBlocks d A 0 0 A := rfl

theorem matrixDiagonalDouble_nonneg {A : CMatrix d} (hA : 0 ≤ A) :
    0 ≤ matrixDiagonalDouble d A := by
  have hp := Matrix.nonneg_iff_posSemidef.mp (matrix_fromBlocks_diagonal_nonneg hA hA)
  exact (hp.submatrix finSumFinEquiv.symm).nonneg

theorem matrixDiagonalDouble_projection {F : CMatrix d} (hF : IsStarProjection F) :
    IsStarProjection (matrixDiagonalDouble d F) := by
  constructor
  · show matrixDiagonalDouble d F * matrixDiagonalDouble d F = matrixDiagonalDouble d F
    rw [← map_mul, hF.isIdempotentElem.eq]
  · show star (matrixDiagonalDouble d F) = matrixDiagonalDouble d F
    rw [← map_star, hF.isSelfAdjoint.star_eq]

theorem matrixDiagonalDouble_resolvent {lam : ℝ} {S : CMatrix d}
    (hlam : 0 < lam) (hS : 0 ≤ S) :
    matrixPositiveResolvent lam (matrixDiagonalDouble d S) =
      matrixDiagonalDouble d (matrixPositiveResolvent lam S) := by
  rw [matrixPositiveResolvent_eq_inverse hlam (matrixDiagonalDouble_nonneg d hS)]
  apply Matrix.inv_eq_right_inv
  have he := congrArg (matrixDiagonalDouble d) (matrixPositiveResolvent_shift_mul hlam hS)
  simpa only [map_mul, map_add, map_smul, map_one] using he

theorem matrixDiagonalDouble_partial_sum (F : Nat → CMatrix d) (n : Nat) :
    matrixProjectionPartialSum 0 (fun i => matrixDiagonalDouble d (F i)) n =
      matrixDiagonalDouble d (matrixProjectionPartialSum 0 F n) := by
  simp only [matrixProjectionPartialSum, zero_add, map_sum]

theorem matrixDiagonalDouble_hsNorm_sq [NeZero d] (A : CMatrix d) :
    hsNorm (matrixDiagonalDouble d A) ^ 2 = hsNorm A ^ 2 := by
  rw [matrixDiagonalDouble_apply, matrixDoubleBlocks_hsNorm_sq]
  simp only [hsNorm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
  ring

end ThomGame.Analysis

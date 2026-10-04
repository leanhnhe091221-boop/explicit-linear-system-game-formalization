module

public import ThomGame.Analysis.MatrixDiagonalDouble

/-!
# Self-adjoint unitary doubling and commutator norms

The actual block matrix [0 U; U* 0] is a self-adjoint involution.
Its commutator with the doubled diagonal matrix has the same normalized
Hilbert--Schmidt norm as the original commutator. One column block of
the resolvent commutator costs at most a factor two after squaring.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d : Nat}

noncomputable def matrixUnitaryDouble (U : UnitaryMatrix d) : CMatrix (d + d) :=
  matrixDoubleBlocks d 0 U.val (star U.val) 0

theorem matrixUnitaryDouble_isSelfAdjoint (U : UnitaryMatrix d) :
    IsSelfAdjoint (matrixUnitaryDouble U) := by
  show star (matrixUnitaryDouble U) = matrixUnitaryDouble U
  simp only [matrixUnitaryDouble, matrixDoubleBlocks_star, star_zero, star_star]

theorem matrixUnitaryDouble_mul_self (U : UnitaryMatrix d) :
    matrixUnitaryDouble U * matrixUnitaryDouble U = 1 := by
  rw [matrixUnitaryDouble, matrixDoubleBlocks_mul]
  simp only [zero_mul, mul_zero, zero_add, add_zero, U.prop.1, U.prop.2, matrixDoubleBlocks_one]

theorem hsNorm_unitary_star_commutator (U : UnitaryMatrix d) (X : CMatrix d) :
    hsNorm (star U.val * X - X * star U.val) = hsNorm (U.val * X - X * U.val) := by
  have he : star U.val * (U.val * X - X * U.val) * star U.val =
      -(star U.val * X - X * star U.val) := by
    calc
      _ = (star U.val * U.val) * X * star U.val - star U.val * X * (U.val * star U.val) := by noncomm_ring
      _ = _ := by rw [U.prop.1, U.prop.2, one_mul, mul_one]; noncomm_ring
  have hn : hsNorm (star U.val * (U.val * X - X * U.val) * star U.val) =
      hsNorm (U.val * X - X * U.val) := by
    change hsNorm ((U⁻¹).val * (U.val * X - X * U.val) * (U⁻¹).val) = _
    rw [hsNorm_mul_unitary, hsNorm_unitary_mul]
  rwa [he, hsNorm_neg] at hn

theorem matrixUnitaryDouble_commutator (U : UnitaryMatrix d) (X : CMatrix d) :
    matrixUnitaryDouble U * matrixDiagonalDouble d X - matrixDiagonalDouble d X * matrixUnitaryDouble U =
      matrixDoubleBlocks d 0 (U.val * X - X * U.val) (star U.val * X - X * star U.val) 0 := by
  simp only [matrixUnitaryDouble, matrixDiagonalDouble_apply, matrixDoubleBlocks_mul,
    matrixDoubleBlocks_sub, zero_mul, mul_zero, zero_add, add_zero, sub_zero]

theorem matrixUnitaryDouble_commutator_column (U : UnitaryMatrix d) (X F : CMatrix d) :
    (matrixUnitaryDouble U * matrixDiagonalDouble d X - matrixDiagonalDouble d X * matrixUnitaryDouble U) *
      matrixDiagonalDouble d F = matrixDoubleBlocks d 0 ((U.val * X - X * U.val) * F)
        ((star U.val * X - X * star U.val) * F) 0 := by
  rw [matrixUnitaryDouble_commutator, matrixDiagonalDouble_apply, matrixDoubleBlocks_mul]
  simp only [zero_mul, mul_zero, zero_add, add_zero]

theorem matrixUnitaryDouble_commutator_hsNorm_sq [NeZero d] (U : UnitaryMatrix d) (X : CMatrix d) :
    hsNorm (matrixUnitaryDouble U * matrixDiagonalDouble d X - matrixDiagonalDouble d X * matrixUnitaryDouble U) ^ 2 =
      hsNorm (U.val * X - X * U.val) ^ 2 := by
  rw [matrixUnitaryDouble_commutator, matrixDoubleBlocks_hsNorm_sq, hsNorm_unitary_star_commutator]
  simp only [hsNorm_zero, zero_pow (by decide : 2 ≠ 0), zero_add, add_zero]
  ring

theorem matrixUnitaryDouble_commutator_column_lower [NeZero d] (U : UnitaryMatrix d) (X F : CMatrix d) :
    hsNorm ((U.val * X - X * U.val) * F) ^ 2 ≤
      2 * hsNorm ((matrixUnitaryDouble U * matrixDiagonalDouble d X -
        matrixDiagonalDouble d X * matrixUnitaryDouble U) * matrixDiagonalDouble d F) ^ 2 := by
  rw [matrixUnitaryDouble_commutator_column, matrixDoubleBlocks_hsNorm_sq]
  simp only [hsNorm_zero, zero_pow (by decide : 2 ≠ 0), zero_add, add_zero]
  nlinarith [sq_nonneg (hsNorm ((star U.val * X - X * star U.val) * F))]

end ThomGame.Analysis

module

public import ThomGame.Analysis.MatrixStarBlockFrames

/-!
# Exact action of arbitrary algebra elements on the block frames
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

theorem matrix_mul_single_column_expansion {n : Nat} (X : CMatrix n) (a b : Fin n) :
    X * Matrix.single a b 1 = ∑ c, X c a • Matrix.single c b (1 : ℂ) := by
  ext r s
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  by_cases h : b = s
  · subst s
    simp [Matrix.mul_apply, Matrix.single, smul_eq_mul]
  · simp [Matrix.mul_apply, Matrix.single, smul_eq_mul, h]

variable {d m : Nat} (A : StarSubalgebra ℂ (CMatrix d))

theorem matrixAlgebraicBlockInsert_left_mul (S : MatrixSubalgebraAlgebraicBlocks A)
    (X : A) (i : Fin S.count) (Y : CMatrix (S.size i)) :
    X * matrixAlgebraicBlockInsert A S i Y = matrixAlgebraicBlockInsert A S i (S.equiv X i * Y) := by
  apply S.equiv.injective
  rw [map_mul, matrixAlgebraicBlockInsert_equiv, matrixAlgebraicBlockInsert_equiv]
  exact (Pi.single_mul_right (i := i) (f := S.equiv X) Y).symm

variable (P : MatrixSubalgebraStarBlocks A)

theorem matrixStarBlockUnit_left_mul (X : A) (i : Fin P.count) (a b : Fin (P.size i)) :
    X * matrixStarBlockUnit A P i a b =
      ∑ c, (P.equiv X i c a) • matrixStarBlockUnit A P i c b := by
  change X * matrixAlgebraicBlockInsert A P.toAlgebraic i (Matrix.single a b 1) = _
  rw [matrixAlgebraicBlockInsert_left_mul, matrix_mul_single_column_expansion]
  simp only [map_sum, map_smul, matrixStarBlockUnit, matrixAlgebraicBlockUnit]
  rfl

theorem matrixStarBlockFrame_action (ρ : A →⋆ₐ[ℂ] CMatrix m)
    (X : A) (i : Fin P.count) (a : Fin (P.size i)) :
    ρ X * matrixStarBlockFrame A P ρ i a =
      ∑ b, P.equiv X i b a • matrixStarBlockFrame A P ρ i b := by
  rw [matrixStarBlockFrame, ← Matrix.mul_assoc, ← map_mul, matrixStarBlockUnit_left_mul]
  simp only [map_sum, map_smul, Matrix.sum_mul, Matrix.smul_mul, matrixStarBlockFrame]

end ThomGame.Analysis

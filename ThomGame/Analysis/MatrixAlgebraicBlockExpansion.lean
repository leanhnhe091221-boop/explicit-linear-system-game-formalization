module

public import ThomGame.Analysis.MatrixAlgebraicBlockUnits

/-!
# Explicit expansions in the constructed algebraic matrix units
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator

variable {d : Nat} (A : StarSubalgebra ℂ (CMatrix d))
    (S : MatrixSubalgebraAlgebraicBlocks A)

theorem matrixAlgebraicBlockInsert_expansion (i : Fin S.count) (X : CMatrix (S.size i)) :
    matrixAlgebraicBlockInsert A S i X =
      ∑ a, ∑ b, X a b • matrixAlgebraicBlockUnit A S i a b := by
  have hs (a b : Fin (S.size i)) : Matrix.single a b (X a b) = X a b • Matrix.single a b (1 : ℂ) := by
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum, hs, map_smul, matrixAlgebraicBlockUnit]

theorem matrixAlgebraicBlocks_symm_expansion (X : (i : Fin S.count) → CMatrix (S.size i)) :
    S.equiv.symm X = ∑ i, ∑ a, ∑ b, X i a b • matrixAlgebraicBlockUnit A S i a b := by
  calc
    S.equiv.symm X = ∑ i, matrixAlgebraicBlockInsert A S i (X i) := by
      change S.equiv.symm X = ∑ i, S.equiv.symm (Pi.single i (X i))
      rw [← map_sum, Finset.univ_sum_single]
    _ = _ := by simp only [matrixAlgebraicBlockInsert_expansion]

end ThomGame.Analysis

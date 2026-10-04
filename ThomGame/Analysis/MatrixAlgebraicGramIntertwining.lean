module

public import ThomGame.Analysis.MatrixAlgebraicGram

/-!
# The Gram element intertwines the desired adjoint operation

For the actual algebraic units e_ab, the exact identity is
H e_ab = (e_ba)* H. No adjoint compatibility of the initial algebraic
decomposition is assumed.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator

variable {d : Nat} (A : StarSubalgebra ℂ (CMatrix d))
    (S : MatrixSubalgebraAlgebraicBlocks A)

theorem matrixAlgebraicBlockUnit_mul_ite (i : Fin S.count) (a b c e : Fin (S.size i)) :
    matrixAlgebraicBlockUnit A S i a b * matrixAlgebraicBlockUnit A S i c e =
      if b = c then matrixAlgebraicBlockUnit A S i a e else 0 := by
  by_cases h : b = c
  · subst c
    simp only [ite_true, matrixAlgebraicBlockUnit_mul_same]
  · rw [ite_eq_right h, matrixAlgebraicBlockUnit_mul_ne A S i a b c e h]

theorem matrixAlgebraicBlockUnit_mul_other (i j : Fin S.count) (hij : i ≠ j)
    (a b : Fin (S.size i)) (c e : Fin (S.size j)) :
    matrixAlgebraicBlockUnit A S i a b * matrixAlgebraicBlockUnit A S j c e = 0 :=
  matrixAlgebraicBlockInsert_mul_of_ne A S i j hij _ _

theorem matrixAlgebraicBlockGram_mul_same (i : Fin S.count) (a b : Fin (S.size i)) :
    matrixAlgebraicBlockGram A S i * matrixAlgebraicBlockUnit A S i a b =
      ∑ c, star (matrixAlgebraicBlockUnit A S i c a) * matrixAlgebraicBlockUnit A S i c b := by
  simp only [matrixAlgebraicBlockGram, Finset.sum_mul, mul_assoc,
    matrixAlgebraicBlockUnit_mul_ite, mul_ite, mul_zero]
  simp

theorem matrixAlgebraicBlockGram_mul_other (i j : Fin S.count) (hij : i ≠ j)
    (a b : Fin (S.size j)) :
    matrixAlgebraicBlockGram A S i * matrixAlgebraicBlockUnit A S j a b = 0 := by
  simp only [matrixAlgebraicBlockGram, Finset.sum_mul, mul_assoc,
    matrixAlgebraicBlockUnit_mul_other A S i j hij, mul_zero, Finset.sum_const_zero]

theorem matrixAlgebraicGram_mul_unit (i : Fin S.count) (a b : Fin (S.size i)) :
    matrixAlgebraicGram A S * matrixAlgebraicBlockUnit A S i a b =
      ∑ c, star (matrixAlgebraicBlockUnit A S i c a) * matrixAlgebraicBlockUnit A S i c b := by
  rw [matrixAlgebraicGram, Finset.sum_mul]
  calc
    _ = matrixAlgebraicBlockGram A S i * matrixAlgebraicBlockUnit A S i a b := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact matrixAlgebraicBlockGram_mul_other A S j i hji a b
      · simp
    _ = _ := matrixAlgebraicBlockGram_mul_same A S i a b

theorem matrixAlgebraicGram_intertwines_unit (i : Fin S.count) (a b : Fin (S.size i)) :
    matrixAlgebraicGram A S * matrixAlgebraicBlockUnit A S i a b =
      star (matrixAlgebraicBlockUnit A S i b a) * matrixAlgebraicGram A S := by
  rw [matrixAlgebraicGram_mul_unit]
  have he := congrArg star (matrixAlgebraicGram_mul_unit A S i b a)
  simpa only [star_mul, matrixAlgebraicGram_star, star_sum, star_star] using he.symm

end ThomGame.Analysis

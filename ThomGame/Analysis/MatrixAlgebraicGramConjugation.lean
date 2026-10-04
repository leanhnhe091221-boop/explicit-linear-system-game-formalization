module

public import ThomGame.Analysis.MatrixAlgebraicGramRoot
public import Mathlib.Algebra.Ring.Action.ConjAct

/-!
# Conjugation by the actual Gram root corrects the matrix-unit adjoints

This is an algebra automorphism of the original subalgebra. It need not
preserve the original adjoint on arbitrary elements, but it turns the
constructed algebraic units into a genuine star matrix-unit system.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator

variable {d : Nat} (A : StarSubalgebra ℂ (CMatrix d))
    (S : MatrixSubalgebraAlgebraicBlocks A)

noncomputable def matrixAlgebraicGramConj : A ≃ₐ[ℂ] A :=
  MulSemiringAction.toAlgEquiv ℂ A (ConjAct.toConjAct (matrixAlgebraicGramRootUnit A S))

theorem matrixAlgebraicGramConj_apply (X : A) :
    matrixAlgebraicGramConj A S X = matrixAlgebraicGramRoot A S * X * matrixAlgebraicGramRootInv A S := rfl

theorem matrixAlgebraicGramConj_unit_star (i : Fin S.count) (a b : Fin (S.size i)) :
    star (matrixAlgebraicGramConj A S (matrixAlgebraicBlockUnit A S i a b)) =
      matrixAlgebraicGramConj A S (matrixAlgebraicBlockUnit A S i b a) := by
  have he := congrArg (fun X : A => matrixAlgebraicGramRootInv A S * X * matrixAlgebraicGramRootInv A S)
    (matrixAlgebraicGram_intertwines_unit A S i b a)
  rw [← matrixAlgebraicGramRoot_mul_self] at he
  simp only [← mul_assoc, matrixAlgebraicGramRoot_inv_mul, one_mul] at he
  simp only [mul_assoc, matrixAlgebraicGramRoot_mul_inv, mul_one] at he
  simpa only [matrixAlgebraicGramConj_apply, star_mul, matrixAlgebraicGramRoot_star,
    matrixAlgebraicGramRootInv_star, mul_assoc] using he.symm

theorem matrixAlgebraicGramConj_support (i : Fin S.count) :
    matrixAlgebraicGramConj A S (matrixAlgebraicBlockSupport A S i) = matrixAlgebraicBlockSupport A S i := by
  rw [matrixAlgebraicGramConj_apply,
    ← matrixAlgebraicBlockSupport_commutes A S i (matrixAlgebraicGramRoot A S),
    mul_assoc, matrixAlgebraicGramRoot_mul_inv, mul_one]

end ThomGame.Analysis

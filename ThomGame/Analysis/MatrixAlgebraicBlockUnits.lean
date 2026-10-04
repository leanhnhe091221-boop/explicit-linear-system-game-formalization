module

public import ThomGame.Analysis.MatrixAlgebraicBlockSupports
public import Mathlib.Data.Matrix.Basis

/-!
# Actual algebraic matrix units in each block

These elements are pulled back through the constructed algebraic
equivalence. They satisfy exact matrix-unit multiplication and sum to
the central supports. Adjoint compatibility is not assumed.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator

variable {d : Nat} (A : StarSubalgebra ℂ (CMatrix d))
    (S : MatrixSubalgebraAlgebraicBlocks A)

noncomputable def matrixAlgebraicBlockInsert (i : Fin S.count) : CMatrix (S.size i) →ₙₐ[ℂ] A where
  toFun X := S.equiv.symm (Pi.single i X)
  map_zero' := by simp
  map_add' X Y := by rw [Pi.single_add, map_add]
  map_mul' X Y := by rw [Pi.single_mul, map_mul]
  map_smul' c X := by rw [Pi.single_smul, map_smul]; rfl

theorem matrixAlgebraicBlockInsert_equiv (i : Fin S.count) (X : CMatrix (S.size i)) :
    S.equiv (matrixAlgebraicBlockInsert A S i X) = Pi.single i X := S.equiv.apply_symm_apply _

theorem matrixAlgebraicBlockInsert_injective (i : Fin S.count) :
    Function.Injective (matrixAlgebraicBlockInsert A S i) := by
  intro X Y h
  have he := congrArg (fun Z : A => S.equiv Z i) h
  simpa only [matrixAlgebraicBlockInsert_equiv, Pi.single_eq_same] using he

theorem matrixAlgebraicBlockInsert_one (i : Fin S.count) :
    matrixAlgebraicBlockInsert A S i 1 = matrixAlgebraicBlockSupport A S i := by
  apply S.equiv.injective
  funext j
  rw [matrixAlgebraicBlockInsert_equiv, matrixAlgebraicBlockSupport_equiv]
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

theorem matrixAlgebraicBlockInsert_mul_of_ne (i j : Fin S.count) (hij : i ≠ j)
    (X : CMatrix (S.size i)) (Y : CMatrix (S.size j)) :
    matrixAlgebraicBlockInsert A S i X * matrixAlgebraicBlockInsert A S j Y = 0 := by
  apply S.equiv.injective
  simp only [map_mul, map_zero, matrixAlgebraicBlockInsert_equiv]
  funext k
  by_cases hi : k = i
  · subst k
    simp [Pi.single_eq_of_ne hij]
  · simp [Pi.single_eq_of_ne hi]

noncomputable def matrixAlgebraicBlockUnit (i : Fin S.count) (a b : Fin (S.size i)) : A :=
  matrixAlgebraicBlockInsert A S i (Matrix.single a b 1)

theorem matrixAlgebraicBlockUnit_mul_same (i : Fin S.count) (a b c : Fin (S.size i)) :
    matrixAlgebraicBlockUnit A S i a b * matrixAlgebraicBlockUnit A S i b c =
      matrixAlgebraicBlockUnit A S i a c := by
  simp [matrixAlgebraicBlockUnit, ← map_mul]

theorem matrixAlgebraicBlockUnit_mul_ne (i : Fin S.count) (a b c e : Fin (S.size i)) (hbc : b ≠ c) :
    matrixAlgebraicBlockUnit A S i a b * matrixAlgebraicBlockUnit A S i c e = 0 := by
  simp [matrixAlgebraicBlockUnit, ← map_mul, Matrix.single_mul_single_of_ne _ _ _ _ hbc]

theorem matrixAlgebraicBlockUnit_diagonal_sum (i : Fin S.count) :
    ∑ a, matrixAlgebraicBlockUnit A S i a a = matrixAlgebraicBlockSupport A S i := by
  simp only [matrixAlgebraicBlockUnit, ← map_sum, Matrix.sum_single_one,
    matrixAlgebraicBlockInsert_one]

theorem matrixAlgebraicBlockUnit_ne_zero (i : Fin S.count) (a b : Fin (S.size i)) :
    matrixAlgebraicBlockUnit A S i a b ≠ 0 := by
  intro h
  have he : matrixAlgebraicBlockInsert A S i (Matrix.single a b 1) =
      matrixAlgebraicBlockInsert A S i 0 := by
    simpa only [matrixAlgebraicBlockUnit, map_zero] using h
  have hx := congrArg (fun X : CMatrix (S.size i) => X a b)
    (matrixAlgebraicBlockInsert_injective A S i he)
  simp at hx

end ThomGame.Analysis

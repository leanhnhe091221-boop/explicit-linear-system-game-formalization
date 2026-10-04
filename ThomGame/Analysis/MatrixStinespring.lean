module

public import ThomGame.Analysis.MatrixKrausRepresentation
public import Mathlib.Data.Matrix.Block

/-!
# An actual finite Stinespring dilation for matrix maps

The dilation space has d cubed coordinates. Both its representation and
its isometry are explicit matrices obtained from the proved Kraus factorization.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

variable {d : Nat} {κ : Type*} [Fintype κ] [DecidableEq κ]

noncomputable def matrixDiagonalRepresentation (κ : Type*) [Fintype κ] [DecidableEq κ]
    (d : Nat) : CMatrix d →⋆ₐ[ℂ] Matrix (Fin d × κ) (Fin d × κ) ℂ where
  toFun X := Matrix.blockDiagonal (fun _ : κ => X)
  map_zero' := Matrix.blockDiagonal_zero
  map_one' := Matrix.blockDiagonal_one
  map_add' X Y := Matrix.blockDiagonal_add (fun _ : κ => X) (fun _ : κ => Y)
  map_mul' X Y := Matrix.blockDiagonal_mul (fun _ : κ => X) (fun _ : κ => Y)
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [show (fun _ : κ => c • (1 : CMatrix d)) = c • (1 : κ → CMatrix d) from rfl,
      Matrix.blockDiagonal_smul, Matrix.blockDiagonal_one]
  map_star' X := (Matrix.blockDiagonal_conjTranspose (fun _ : κ => X)).symm

theorem matrixDiagonalRepresentation_apply (X : CMatrix d) (i j : Fin d × κ) :
    matrixDiagonalRepresentation κ d X i j = if i.2 = j.2 then X i.1 j.1 else 0 := rfl

def matrixKrausColumn (a : κ → CMatrix d) : Matrix (Fin d × κ) (Fin d) ℂ :=
  fun i j => a i.2 i.1 j

theorem matrixDiagonalRepresentation_mul_column (X : CMatrix d) (a : κ → CMatrix d) :
    matrixDiagonalRepresentation κ d X * matrixKrausColumn a =
      matrixKrausColumn (fun j => X * a j) := by
  ext ⟨i, l⟩ j
  simp [matrixDiagonalRepresentation, matrixKrausColumn, Matrix.mul_apply,
    Matrix.blockDiagonal_apply, Fintype.sum_prod_type]

omit [DecidableEq κ] in
theorem matrixKrausColumn_inner (a b : κ → CMatrix d) :
    (matrixKrausColumn a)ᴴ * matrixKrausColumn b = ∑ j, star (a j) * b j := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, matrixKrausColumn,
    Matrix.sum_apply, Matrix.star_eq_conjTranspose, Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem matrixKrausColumn_compression (a : κ → CMatrix d) (X : CMatrix d) :
    (matrixKrausColumn a)ᴴ * matrixDiagonalRepresentation κ d X * matrixKrausColumn a =
      ∑ j, star (a j) * X * a j := by
  rw [Matrix.mul_assoc, matrixDiagonalRepresentation_mul_column, matrixKrausColumn_inner]
  simp only [Matrix.mul_assoc]

variable [NeZero d]

theorem exists_matrixStinespring (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1) :
    ∃ V : Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ,
      Vᴴ * V = 1 ∧
      ∀ X, Vᴴ * matrixDiagonalRepresentation (Fin d × Fin d) d X * V = F X := by
  obtain ⟨a, ha⟩ := exists_matrix_kraus F
  refine ⟨matrixKrausColumn a, ?_, ?_⟩
  · rw [matrixKrausColumn_inner]
    simpa only [mul_one, hF] using (ha 1).symm
  · intro X
    exact (matrixKrausColumn_compression a X).trans (ha X).symm

end ThomGame.Analysis

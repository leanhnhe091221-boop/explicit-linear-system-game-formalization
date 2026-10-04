module

public import ThomGame.Analysis.MatrixStinespring

/-!
# The concrete standard block representation

The actual matrix is the direct sum of X_i tensor identity_q_i. Zero
multiplicity is allowed. Its entries and right action on an arbitrary
rectangular matrix are explicit.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {n : Nat} (p q : Fin n → Nat)

abbrev MatrixStandardBlockIndex := Σ i : Fin n, Fin (p i) × Fin (q i)

noncomputable def matrixStandardBlockRepresentation :
    ((i : Fin n) → CMatrix (p i)) →⋆ₐ[ℂ]
      Matrix (MatrixStandardBlockIndex p q) (MatrixStandardBlockIndex p q) ℂ where
  toFun X := Matrix.blockDiagonal' (fun i => matrixDiagonalRepresentation (Fin (q i)) (p i) (X i))
  map_zero' := by simp only [Pi.zero_apply, map_zero]; exact Matrix.blockDiagonal'_zero
  map_one' := by simp only [Pi.one_apply, map_one]; exact Matrix.blockDiagonal'_one
  map_add' X Y := by
    simp only [Pi.add_apply, map_add]
    exact Matrix.blockDiagonal'_add _ _
  map_mul' X Y := by
    simp only [Pi.mul_apply, map_mul]
    exact Matrix.blockDiagonal'_mul _ _
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, Pi.smul_apply, Pi.one_apply, map_smul, map_one]
    rw [show (fun i => c • (1 : Matrix (Fin (p i) × Fin (q i)) (Fin (p i) × Fin (q i)) ℂ)) =
      c • (1 : (i : Fin n) → Matrix (Fin (p i) × Fin (q i)) (Fin (p i) × Fin (q i)) ℂ) from rfl,
      Matrix.blockDiagonal'_smul, Matrix.blockDiagonal'_one]
  map_star' X := by
    change Matrix.blockDiagonal' (fun i : Fin n =>
      matrixDiagonalRepresentation (Fin (q i)) (p i) (star (X i))) =
      (Matrix.blockDiagonal' (fun i : Fin n =>
        matrixDiagonalRepresentation (Fin (q i)) (p i) (X i)))ᴴ
    rw [Matrix.blockDiagonal'_conjTranspose]
    congr 1
    funext i
    exact map_star (matrixDiagonalRepresentation (Fin (q i)) (p i)) (X i)

theorem matrixStandardBlockRepresentation_apply_eq (X : (i : Fin n) → CMatrix (p i))
    (i : Fin n) (a b : Fin (p i)) (k l : Fin (q i)) :
    matrixStandardBlockRepresentation p q X ⟨i, a, k⟩ ⟨i, b, l⟩ = if k = l then X i a b else 0 := by
  change Matrix.blockDiagonal' (fun j : Fin n =>
    matrixDiagonalRepresentation (Fin (q j)) (p j) (X j)) ⟨i, (a, k)⟩ ⟨i, (b, l)⟩ = _
  rw [Matrix.blockDiagonal'_apply_eq]
  rfl

theorem matrixStandardBlockRepresentation_apply_ne (X : (i : Fin n) → CMatrix (p i))
    (i j : Fin n) (hij : i ≠ j) (a : Fin (p i) × Fin (q i)) (b : Fin (p j) × Fin (q j)) :
    matrixStandardBlockRepresentation p q X ⟨i, a⟩ ⟨j, b⟩ = 0 :=
  Matrix.blockDiagonal'_apply_ne (fun k : Fin n =>
    matrixDiagonalRepresentation (Fin (q k)) (p k) (X k)) a b hij

theorem matrix_mul_standardBlock_column {α : Type*}
    (F : Matrix α (MatrixStandardBlockIndex p q) ℂ)
    (X : (i : Fin n) → CMatrix (p i)) (r : α)
    (i : Fin n) (a : Fin (p i)) (k : Fin (q i)) :
    (F * matrixStandardBlockRepresentation p q X) r ⟨i, a, k⟩ =
      ∑ b, F r ⟨i, b, k⟩ * X i b a := by
  rw [Matrix.mul_apply, Fintype.sum_sigma]
  calc
    _ = ∑ c : Fin (p i) × Fin (q i),
        F r ⟨i, c⟩ * matrixStandardBlockRepresentation p q X ⟨i, c⟩ ⟨i, a, k⟩ := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        apply Finset.sum_eq_zero
        intro c _
        rw [matrixStandardBlockRepresentation_apply_ne p q X j i hji, mul_zero]
      · simp
    _ = _ := by
      simp only [Fintype.sum_prod_type, matrixStandardBlockRepresentation_apply_eq, mul_ite, mul_zero]
      simp

theorem matrix_standardBlock_mul_row {α : Type*}
    (F : Matrix (MatrixStandardBlockIndex p q) α ℂ)
    (X : (i : Fin n) → CMatrix (p i)) (r : α)
    (i : Fin n) (a : Fin (p i)) (k : Fin (q i)) :
    (matrixStandardBlockRepresentation p q X * F) ⟨i, a, k⟩ r =
      ∑ b, X i a b * F ⟨i, b, k⟩ r := by
  rw [Matrix.mul_apply, Fintype.sum_sigma]
  calc
    _ = ∑ c : Fin (p i) × Fin (q i),
        matrixStandardBlockRepresentation p q X ⟨i, a, k⟩ ⟨i, c⟩ * F ⟨i, c⟩ r := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        apply Finset.sum_eq_zero
        intro c _
        rw [matrixStandardBlockRepresentation_apply_ne p q X i j hji.symm, zero_mul]
      · simp
    _ = _ := by
      simp only [Fintype.sum_prod_type, matrixStandardBlockRepresentation_apply_eq, ite_mul, zero_mul]
      simp

end ThomGame.Analysis

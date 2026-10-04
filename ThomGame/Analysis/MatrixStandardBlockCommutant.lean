module

public import ThomGame.Analysis.MatrixStandardBlockRepresentation
public import ThomGame.Analysis.MatrixStinespringReindex

/-!
# The commutant of the concrete standard blocks

On the same coordinates, the complementary representation is the direct
sum of identity_p_i tensor Y_i. Matrix units force every commuting matrix
to have exactly this form. Only p_i is required to be positive; the
multiplicities q_i may vanish.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {n : Nat} (p q : Fin n → Nat)

def matrixStandardBlockSwap : MatrixStandardBlockIndex q p ≃ MatrixStandardBlockIndex p q :=
  Equiv.sigmaCongrRight (fun _ => Equiv.prodComm _ _)

noncomputable def matrixComplementaryBlockRepresentation :
    ((i : Fin n) → CMatrix (q i)) →⋆ₐ[ℂ]
      Matrix (MatrixStandardBlockIndex p q) (MatrixStandardBlockIndex p q) ℂ :=
  (matrixStarReindex (matrixStandardBlockSwap p q)).toStarAlgHom.comp
    (matrixStandardBlockRepresentation q p)

theorem matrixComplementaryBlockRepresentation_apply_eq (Y : (i : Fin n) → CMatrix (q i))
    (i : Fin n) (a b : Fin (p i)) (k l : Fin (q i)) :
    matrixComplementaryBlockRepresentation p q Y ⟨i, a, k⟩ ⟨i, b, l⟩ =
      if a = b then Y i k l else 0 :=
  matrixStandardBlockRepresentation_apply_eq q p Y i k l a b

theorem matrixComplementaryBlockRepresentation_apply_ne (Y : (i : Fin n) → CMatrix (q i))
    (i j : Fin n) (hij : i ≠ j) (a : Fin (p i) × Fin (q i)) (b : Fin (p j) × Fin (q j)) :
    matrixComplementaryBlockRepresentation p q Y ⟨i, a⟩ ⟨j, b⟩ = 0 :=
  matrixStandardBlockRepresentation_apply_ne q p Y i j hij (a.2, a.1) (b.2, b.1)

theorem matrixStandard_complementary_blocks_commute
    (X : (i : Fin n) → CMatrix (p i)) (Y : (i : Fin n) → CMatrix (q i)) :
    matrixStandardBlockRepresentation p q X * matrixComplementaryBlockRepresentation p q Y =
      matrixComplementaryBlockRepresentation p q Y * matrixStandardBlockRepresentation p q X := by
  ext ⟨i, a, k⟩ ⟨j, b, l⟩
  rw [matrix_standardBlock_mul_row, matrix_mul_standardBlock_column]
  by_cases hij : i = j
  · subst j
    simp [matrixComplementaryBlockRepresentation_apply_eq, mul_ite, mul_comm]
  · simp only [matrixComplementaryBlockRepresentation_apply_ne p q Y i j hij,
      mul_zero, zero_mul, Finset.sum_const_zero]

variable (T : Matrix (MatrixStandardBlockIndex p q) (MatrixStandardBlockIndex p q) ℂ)
    (hT : ∀ X, matrixStandardBlockRepresentation p q X * T = T * matrixStandardBlockRepresentation p q X)

include hT in
theorem matrixStandardBlockCommutant_off_block (i j : Fin n) (hij : i ≠ j)
    (a : Fin (p i)) (b : Fin (p j)) (k : Fin (q i)) (l : Fin (q j)) :
    T ⟨i, a, k⟩ ⟨j, b, l⟩ = 0 := by
  have he := congrArg (fun Z => Z ⟨i, a, k⟩ ⟨j, b, l⟩) (hT (Pi.single i 1))
  rw [matrix_standardBlock_mul_row, matrix_mul_standardBlock_column] at he
  simpa [hij.symm, Matrix.one_apply, ite_mul] using he

include hT in
theorem matrixStandardBlockCommutant_off_diagonal (i : Fin n)
    (a b : Fin (p i)) (hab : a ≠ b) (k l : Fin (q i)) :
    T ⟨i, a, k⟩ ⟨i, b, l⟩ = 0 := by
  have he := congrArg (fun Z => Z ⟨i, a, k⟩ ⟨i, b, l⟩)
    (hT (Pi.single i (Matrix.single a a 1)))
  rw [matrix_standardBlock_mul_row, matrix_mul_standardBlock_column] at he
  simpa [Matrix.single_apply, hab, mul_ite, ite_mul] using he

include hT in
theorem matrixStandardBlockCommutant_diagonal_eq (i : Fin n)
    (a b : Fin (p i)) (k l : Fin (q i)) :
    T ⟨i, a, k⟩ ⟨i, a, l⟩ = T ⟨i, b, k⟩ ⟨i, b, l⟩ := by
  have he := congrArg (fun Z => Z ⟨i, a, k⟩ ⟨i, b, l⟩)
    (hT (Pi.single i (Matrix.single a b 1)))
  rw [matrix_standardBlock_mul_row, matrix_mul_standardBlock_column] at he
  simpa [Matrix.single_apply, mul_ite, ite_mul] using he.symm

theorem matrixStandardBlockCommutant_iff (hp : ∀ i, 0 < p i) :
    (∀ X, matrixStandardBlockRepresentation p q X * T = T * matrixStandardBlockRepresentation p q X) ↔
      ∃ Y, T = matrixComplementaryBlockRepresentation p q Y := by
  constructor
  · intro h
    let Y : (i : Fin n) → CMatrix (q i) :=
      fun i => Matrix.of (fun k l => T ⟨i, ⟨0, hp i⟩, k⟩ ⟨i, ⟨0, hp i⟩, l⟩)
    refine ⟨Y, ?_⟩
    ext ⟨i, a, k⟩ ⟨j, b, l⟩
    by_cases hij : i = j
    · subst j
      rw [matrixComplementaryBlockRepresentation_apply_eq]
      by_cases hab : a = b
      · subst b
        simp only [ite_true]
        exact matrixStandardBlockCommutant_diagonal_eq p q T h i a ⟨0, hp i⟩ k l
      · rw [ite_eq_right hab]
        exact matrixStandardBlockCommutant_off_diagonal p q T h i a b hab k l
    · rw [matrixComplementaryBlockRepresentation_apply_ne p q _ i j hij]
      exact matrixStandardBlockCommutant_off_block p q T h i j hij a b k l
  · rintro ⟨Y, rfl⟩ X
    exact matrixStandard_complementary_blocks_commute p q X Y

end ThomGame.Analysis

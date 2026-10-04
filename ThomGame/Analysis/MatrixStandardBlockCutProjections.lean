module

public import ThomGame.Analysis.MatrixStandardBlockCommutant
public import ThomGame.Analysis.MatrixProjectionSubrank

/-!
# Actual coordinate cut projections in both factors of standard blocks

The two commuting projections retain initial coordinates in the simple
factor and in the multiplicity factor. Their product has exactly the
weighted retained dimension, including empty retained factors.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable def matrixInitialProjection (d k : Nat) : CMatrix d :=
  Matrix.diagonal (fun a => if a.val < k then 1 else 0)

theorem matrixInitialProjection_isStarProjection (d k : Nat) :
    IsStarProjection (matrixInitialProjection d k) := by
  simpa [matrixBasisProjection, matrixInitialProjection, Unitary.conjStarAlgAut_apply] using
    matrixBasisProjection_isStarProjection (1 : UnitaryMatrix d) (Finset.univ.filter (fun a : Fin d => a.val < k))

variable {n : Nat} (p q : Fin n → Nat)

theorem matrixStandardBlockRepresentation_diagonal (x : (i : Fin n) → Fin (p i) → ℂ) :
    matrixStandardBlockRepresentation p q (fun i => Matrix.diagonal (x i)) =
      Matrix.diagonal (fun c : MatrixStandardBlockIndex p q => x c.1 c.2.1) := by
  ext ⟨i, a, k⟩ ⟨j, b, l⟩
  by_cases hij : i = j
  · subst j
    rw [matrixStandardBlockRepresentation_apply_eq]
    by_cases hab : a = b <;> by_cases hkl : k = l <;> simp_all
  · rw [matrixStandardBlockRepresentation_apply_ne p q _ i j hij]
    exact (Matrix.diagonal_apply_ne _ (fun h => hij (congrArg Sigma.fst h))).symm

theorem matrixComplementaryBlockRepresentation_diagonal (y : (i : Fin n) → Fin (q i) → ℂ) :
    matrixComplementaryBlockRepresentation p q (fun i => Matrix.diagonal (y i)) =
      Matrix.diagonal (fun c : MatrixStandardBlockIndex p q => y c.1 c.2.2) := by
  ext ⟨i, a, k⟩ ⟨j, b, l⟩
  by_cases hij : i = j
  · subst j
    rw [matrixComplementaryBlockRepresentation_apply_eq]
    by_cases hab : a = b <;> by_cases hkl : k = l <;> simp_all
  · rw [matrixComplementaryBlockRepresentation_apply_ne p q _ i j hij]
    exact (Matrix.diagonal_apply_ne _ (fun h => hij (congrArg Sigma.fst h))).symm

variable (r s : Fin n → Nat) (hr : ∀ i, r i ≤ p i) (hs : ∀ i, s i ≤ q i)

def matrixRetainedBlockIndexEquiv :
    {c : MatrixStandardBlockIndex p q // c.2.1.val < r c.1 ∧ c.2.2.val < s c.1} ≃
      MatrixStandardBlockIndex r s where
  toFun c := ⟨c.val.1, ⟨c.val.2.1.val, c.property.1⟩, ⟨c.val.2.2.val, c.property.2⟩⟩
  invFun c := ⟨⟨c.1, ⟨c.2.1.val, lt_of_lt_of_le c.2.1.isLt (hr c.1)⟩,
    ⟨c.2.2.val, lt_of_lt_of_le c.2.2.isLt (hs c.1)⟩⟩, c.2.1.isLt, c.2.2.isLt⟩
  left_inv c := by cases c; rfl
  right_inv c := by cases c; rfl

include hr hs in
theorem matrixRetainedBlockIndex_card :
    Fintype.card {c : MatrixStandardBlockIndex p q // c.2.1.val < r c.1 ∧ c.2.2.val < s c.1} =
      ∑ i, r i * s i := by
  rw [Fintype.card_congr (matrixRetainedBlockIndexEquiv p q r s hr hs)]
  simp only [MatrixStandardBlockIndex, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]

include hr hs in
theorem matrixStandardBlockCuts_product_rank :
    (matrixStandardBlockRepresentation p q (fun i => matrixInitialProjection (p i) (r i)) *
      matrixComplementaryBlockRepresentation p q (fun i => matrixInitialProjection (q i) (s i))).rank =
      ∑ i, r i * s i := by
  unfold matrixInitialProjection
  rw [matrixStandardBlockRepresentation_diagonal, matrixComplementaryBlockRepresentation_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.rank_diagonal]
  have he (c : MatrixStandardBlockIndex p q) :
      (if c.2.1.val < r c.1 then (1 : ℂ) else 0) *
        (if c.2.2.val < s c.1 then 1 else 0) ≠ 0 ↔ c.2.1.val < r c.1 ∧ c.2.2.val < s c.1 := by
    by_cases h₁ : c.2.1.val < r c.1 <;> by_cases h₂ : c.2.2.val < s c.1 <;> simp [h₁, h₂]
  exact (Fintype.card_congr (Equiv.subtypeEquivRight he)).trans
    (matrixRetainedBlockIndex_card p q r s hr hs)

end ThomGame.Analysis

module

public import ThomGame.Analysis.NormalizedHilbertSchmidt
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The kernel of a finite sum of matrix Gram squares

The sum is positive semidefinite and its kernel is exactly the common
kernel of the original matrices. A trivial common kernel therefore
gives a positive definite, invertible Gram matrix.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators ComplexOrder

variable {ι : Type*} [Fintype ι] {d : Nat}

noncomputable def matrixSumGram (F : ι → CMatrix d) : CMatrix d := ∑ i, (F i)ᴴ * F i

theorem matrixSumGram_posSemidef (F : ι → CMatrix d) : (matrixSumGram F).PosSemidef :=
  Matrix.posSemidef_sum Finset.univ (fun i _ => Matrix.posSemidef_conjTranspose_mul_self (F i))

theorem matrixSumGram_mulVec_eq_zero_iff (F : ι → CMatrix d) (v : Fin d → ℂ) :
    matrixSumGram F *ᵥ v = 0 ↔ ∀ i, F i *ᵥ v = 0 := by
  constructor
  · intro hv
    have hz : star v ⬝ᵥ (matrixSumGram F *ᵥ v) = 0 := by rw [hv]; simp
    have hs : ∑ i, star v ⬝ᵥ (((F i)ᴴ * F i) *ᵥ v) = 0 := by
      simpa only [matrixSumGram, Matrix.sum_mulVec, dotProduct_sum] using hz
    have hnonneg (i : ι) : 0 ≤ star v ⬝ᵥ (((F i)ᴴ * F i) *ᵥ v) :=
      (Matrix.posSemidef_conjTranspose_mul_self (F i)).dotProduct_mulVec_nonneg v
    intro i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hs i (Finset.mem_univ i)
    exact (Matrix.conjTranspose_mul_self_mulVec_eq_zero (F i) v).mp
      ((Matrix.posSemidef_conjTranspose_mul_self (F i)).dotProduct_mulVec_zero_iff.mp hi)
  · intro hv
    simp [matrixSumGram, Matrix.sum_mulVec, ← Matrix.mulVec_mulVec, hv]

theorem matrixSumGram_isUnit (F : ι → CMatrix d)
    (hker : ∀ v : Fin d → ℂ, (∀ i, F i *ᵥ v = 0) → v = 0) : IsUnit (matrixSumGram F) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  have hz : matrixSumGram F *ᵥ (v - w) = 0 := by rw [Matrix.mulVec_sub, hvw, sub_self]
  exact sub_eq_zero.mp (hker (v - w) ((matrixSumGram_mulVec_eq_zero_iff F (v - w)).mp hz))

theorem matrixSumGram_posDef (F : ι → CMatrix d)
    (hker : ∀ v : Fin d → ℂ, (∀ i, F i *ᵥ v = 0) → v = 0) : (matrixSumGram F).PosDef :=
  (matrixSumGram_posSemidef F).posDef_iff_isUnit.mpr (matrixSumGram_isUnit F hker)

end ThomGame.Analysis

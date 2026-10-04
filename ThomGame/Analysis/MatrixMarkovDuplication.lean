module

public import ThomGame.Analysis.MatrixMarkovPowers

/-!
# Duplicating the tuple leaves its Markov operator unchanged

The doubled symmetric conjugation sum has half the original weight.
This identifies the original powers used to induce the expectation with
the unperturbed doubled powers used in ALT's correction.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators

theorem lazyMarkovWeight_add_self_mul_two (h : Nat) :
    lazyMarkovWeight (h + h) * 2 = lazyMarkovWeight h := by
  unfold lazyMarkovWeight
  rw [Nat.cast_add, show 4 * ((h : ℝ) + h) = (4 * (h : ℝ)) * 2 by ring, mul_inv_rev]
  ring

theorem matrixLazyMarkov_append_self {d h : Nat} (U : Fin h → UnitaryMatrix d) :
    matrixLazyMarkov (Fin.append U U) = matrixLazyMarkov U := by
  have hw : (lazyMarkovWeight (h + h) : ℂ) * 2 = (lazyMarkovWeight h : ℂ) := by
    exact_mod_cast lazyMarkovWeight_add_self_mul_two h
  have hw' : (lazyMarkovWeight (h + h) : ℂ) + (lazyMarkovWeight (h + h) : ℂ) =
      (lazyMarkovWeight h : ℂ) := by linear_combination hw
  simp only [matrixLazyMarkov, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  rw [smul_add, ← add_smul, hw']

theorem matrixUniformMarkovPower_append_self {ι : Type*} (dims : ι → Nat) {h : Nat} [NeZero h]
    (U : (k : ι) → Fin h → UnitaryMatrix (dims k)) (hd : ∀ k, 0 < dims k) (N : ι → Nat) :
    matrixUniformMarkovPower dims (fun k => Fin.append (U k) (U k)) hd N =
      matrixUniformMarkovPower dims U hd N := by
  unfold matrixUniformMarkovPower
  simp only [matrixLazyMarkov_append_self]

end ThomGame.Analysis

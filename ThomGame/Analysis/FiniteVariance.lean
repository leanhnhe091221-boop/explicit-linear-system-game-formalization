module

public import ThomGame.Analysis.FiniteMedian
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# The arithmetic mean minimizes the finite sum of squared deviations
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem finite_sum_sub_mean (a : ι → ℝ) :
    ∑ i, (a i - (∑ j, a j) / Fintype.card ι) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  field_simp
  ring

theorem finite_sum_sq_sub_mean_le (a : ι → ℝ) (m : ℝ) :
    (∑ i, (a i - (∑ j, a j) / Fintype.card ι) ^ 2) ≤ ∑ i, (a i - m) ^ 2 := by
  let c := (∑ j, a j) / (Fintype.card ι : ℝ)
  have hs : ∑ i, (a i - c) = 0 := finite_sum_sub_mean a
  have he : (∑ i, (a i - m) ^ 2) =
      (∑ i, (a i - c) ^ 2) + (Fintype.card ι : ℝ) * (c - m) ^ 2 := by
    calc
      _ = ∑ i, ((a i - c) ^ 2 + 2 * (c - m) * (a i - c) + (c - m) ^ 2) :=
        Finset.sum_congr rfl fun _ _ => by ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hs, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, mul_zero, add_zero]
  rw [he]
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

end ThomGame.Analysis

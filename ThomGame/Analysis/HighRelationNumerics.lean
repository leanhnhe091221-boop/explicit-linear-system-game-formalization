module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Rank overlap and the numerical obstruction for high rectangles

All masses use one common ambient normalization. The constants do not
depend on the matrix dimension or the number of blocks.
-/

@[expose] public section
namespace ThomGame.Analysis

theorem highRelation_triple_overlap (a b c rho : ℝ) (hrho : 0 ≤ rho)
    (hab : (1 - 2 * rho) * max a b ≤ min a b)
    (hbc : (1 - 2 * rho) * max b c ≤ min b c) :
    (1 - 4 * rho) * max (max a b) c ≤ min a b + min b c - b := by
  rcases le_total a b with hab' | hab' <;>
    rcases le_total b c with hbc' | hbc' <;>
    rcases le_total a c with hac' | hac' <;>
    simp_all only [max_eq_left, max_eq_right, min_eq_left, min_eq_right] <;>
    nlinarith

theorem highRelation_low_product_impossible (rho M x y : ℝ)
    (hsmall : rho ≤ 1 / 1024) (hM : 0 < M)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hmass : (1 - 4 * rho) * M ≤ x ^ 2)
    (herror : y ^ 2 ≤ 144 * rho * M) (hlow : (1 - rho) * x ≤ y) : False := by
  have hrM := mul_le_mul_of_nonneg_right hsmall hM.le
  have hrx := mul_le_mul_of_nonneg_right hsmall hx
  have hhalf : x / 2 ≤ y := by nlinarith
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ x / 2) hy).mpr hhalf
  nlinarith

end ThomGame.Analysis

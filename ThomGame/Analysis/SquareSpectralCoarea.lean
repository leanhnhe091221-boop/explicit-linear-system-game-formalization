module

public import ThomGame.Analysis.SpectralStepCoarea

/-! Coarea for squared spectral thresholds, with the two-factor Connes estimate. -/

@[expose] public section
namespace ThomGame.Analysis

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem weighted_abs_product_sum_sq_le (c x y : ι → ℝ) (hc : ∀ i, 0 ≤ c i) :
    (∑ i, c i * |x i| * |y i|) ^ 2 ≤
      (∑ i, c i * x i ^ 2) * (∑ i, c i * y i ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · exact fun i _ => mul_nonneg (hc i) (sq_nonneg _)
  · exact fun i _ => mul_nonneg (hc i) (sq_nonneg _)
  · intro i _
    simp only [mul_pow, sq_abs]
    nlinarith

theorem weighted_square_difference_sum_le (c x y : ι → ℝ) (hc : ∀ i, 0 ≤ c i) :
    (∑ i, c i * |y i ^ 2 - x i ^ 2|) ≤
      Real.sqrt (∑ i, c i * (y i - x i) ^ 2) *
        Real.sqrt (∑ i, c i * (y i + x i) ^ 2) := by
  have he (i : ι) : |y i ^ 2 - x i ^ 2| = |y i - x i| * |y i + x i| := by
    rw [← abs_mul]
    congr 1
    ring
  simp only [he, ← mul_assoc]
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (sq_nonneg _))]
  exact Real.le_sqrt_of_sq_le (weighted_abs_product_sum_sq_le c
    (fun i => y i - x i) (fun i => y i + x i) hc)

theorem weighted_squareSteps_integrable (c x y : ι → ℝ) :
    Integrable (fun s => ∑ i, c i *
      (spectralStep s (y i ^ 2) - spectralStep s (x i ^ 2)) ^ 2) := by
  apply integrable_finsetSum
  intro i _
  exact (spectralStep_sq_sub_integrable (x i ^ 2) (y i ^ 2)).const_mul (c i)

theorem weighted_squareSteps_integral (c x y : ι → ℝ) :
    (∫ s, ∑ i, c i * (spectralStep s (y i ^ 2) - spectralStep s (x i ^ 2)) ^ 2) =
      ∑ i, c i * |y i ^ 2 - x i ^ 2| := by
  rw [integral_finsetSum]
  · simp only [integral_const_mul, spectralStep_sq_sub_integral]
  · intro i _
    exact (spectralStep_sq_sub_integrable (x i ^ 2) (y i ^ 2)).const_mul (c i)

theorem weighted_squareSteps_coarea (c x y : ι → ℝ) (hc : ∀ i, 0 ≤ c i) :
    (∫ s, ∑ i, c i * (spectralStep s (y i ^ 2) - spectralStep s (x i ^ 2)) ^ 2) ≤
      Real.sqrt (∑ i, c i * (y i - x i) ^ 2) *
        Real.sqrt (∑ i, c i * (y i + x i) ^ 2) := by
  rw [weighted_squareSteps_integral]
  exact weighted_square_difference_sum_le c x y hc

end ThomGame.Analysis

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Scalar spectral cuts and finite weighted coarea

The squared difference of two upper spectral indicators is exactly
the indicator of the interval between their endpoints. These are
actual Lebesgue integrals, including the endpoint conventions.
-/

@[expose] public section
namespace ThomGame.Analysis

open MeasureTheory Set
open scoped BigOperators

noncomputable def spectralStep (s x : ℝ) : ℝ := if s ≤ x then 1 else 0

theorem spectralStep_nonneg (s x : ℝ) : 0 ≤ spectralStep s x := by
  unfold spectralStep
  split_ifs <;> norm_num

theorem spectralStep_sq (s x : ℝ) : spectralStep s x ^ 2 = spectralStep s x := by
  unfold spectralStep
  split_ifs <;> norm_num

theorem spectralStep_sq_sub (x y : ℝ) :
    (fun s => (spectralStep s y - spectralStep s x) ^ 2) =
      (Ioc (min x y) (max x y)).indicator (fun _ => (1 : ℝ)) := by
  funext s
  by_cases hx : s ≤ x <;> by_cases hy : s ≤ y <;>
    simp [spectralStep, Set.indicator, min_lt_iff, le_max_iff, hx, hy]

theorem spectralStep_sq_sub_integrable (x y : ℝ) :
    Integrable (fun s => (spectralStep s y - spectralStep s x) ^ 2) := by
  rw [spectralStep_sq_sub]
  exact (integrableOn_const (by simp [Real.volume_Ioc])).integrable_indicator measurableSet_Ioc

theorem spectralStep_sq_sub_integral (x y : ℝ) :
    (∫ s, (spectralStep s y - spectralStep s x) ^ 2) = |y - x| := by
  rw [spectralStep_sq_sub, integral_indicator_const, Real.volume_real_Ioc_of_le (min_le_max),
    smul_eq_mul, mul_one]
  · exact max_sub_min_eq_abs x y
  · exact measurableSet_Ioc

theorem spectralStep_sq_sub_intervalIntegral_le (a b x y : ℝ) (hab : a ≤ b) :
    (∫ s in a..b, (spectralStep s y - spectralStep s x) ^ 2) ≤ |y - x| := by
  rw [intervalIntegral.integral_of_le hab, ← spectralStep_sq_sub_integral x y]
  exact setIntegral_le_integral (spectralStep_sq_sub_integrable x y)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)

theorem exists_le_intervalIntegral_average {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : IntervalIntegrable f volume a b) :
    ∃ s ∈ Icc a b, f s ≤ (∫ t in a..b, f t) / (b - a) := by
  obtain ⟨s, hs, hf⟩ := exists_le_setAverage
    (μ := volume) (s := Ioc a b) (by simpa using hab) (by simp [Real.volume_Ioc]) hf.1
  refine ⟨s, Ioc_subset_Icc_self hs, ?_⟩
  simpa only [setAverage_eq, Real.volume_real_Ioc_of_le hab.le,
    intervalIntegral.integral_of_le hab.le, div_eq_inv_mul, smul_eq_mul] using hf

variable {ι : Type*} [Fintype ι]

theorem weighted_abs_sum_sq_le (c z : ι → ℝ) (hc : ∀ i, 0 ≤ c i) :
    (∑ i, c i * |z i|) ^ 2 ≤ (∑ i, c i) * ∑ i, c i * z i ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · exact fun i _ => hc i
  · exact fun i _ => mul_nonneg (hc i) (sq_nonneg _)
  · intro i _
    rw [mul_pow, sq_abs]
    nlinarith

theorem weighted_spectralStep_intervalIntegrable (a b : ℝ) (c x y : ι → ℝ) :
    IntervalIntegrable (fun s => ∑ i, c i * (spectralStep s (y i) - spectralStep s (x i)) ^ 2)
      volume a b := by
  have he : (fun s => ∑ i, c i * (spectralStep s (y i) - spectralStep s (x i)) ^ 2) =
      ∑ i, (fun s => c i * (spectralStep s (y i) - spectralStep s (x i)) ^ 2) := by
    funext s
    simp only [Finset.sum_apply]
  rw [he]
  exact IntervalIntegrable.sum Finset.univ fun i _ =>
    ((spectralStep_sq_sub_integrable (x i) (y i)).const_mul (c i)).intervalIntegrable

theorem weighted_spectralStep_coarea (a b : ℝ) (hab : a ≤ b) (c x y : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    (∫ s in a..b, ∑ i, c i * (spectralStep s (y i) - spectralStep s (x i)) ^ 2) ≤
      Real.sqrt ((∑ i, c i) * ∑ i, c i * (y i - x i) ^ 2) := by
  calc
    _ = ∑ i, c i * ∫ s in a..b, (spectralStep s (y i) - spectralStep s (x i)) ^ 2 := by
      rw [intervalIntegral.integral_finsetSum]
      · simp only [intervalIntegral.integral_const_mul]
      · intro i _
        exact ((spectralStep_sq_sub_integrable (x i) (y i)).const_mul (c i)).intervalIntegrable
    _ ≤ ∑ i, c i * |y i - x i| := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (spectralStep_sq_sub_intervalIntegral_le a b _ _ hab) (hc i)
    _ ≤ _ := Real.le_sqrt_of_sq_le (weighted_abs_sum_sq_le c (fun i => y i - x i) hc)

end ThomGame.Analysis

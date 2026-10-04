module

public import ThomGame.Analysis.SpectralStepCoarea

/-!
# Coarea for signed upper spectral thresholds

For positive thresholds the signed cut splits into the cuts of the
positive and negative scalar parts. This gives the constant two in
the scalar estimate used in ALT (3.13), including zero eigenvalues.
-/

@[expose] public section
namespace ThomGame.Analysis

open MeasureTheory Set
open scoped BigOperators

noncomputable def signedSpectralStep (b t : ℝ) : ℝ :=
  (t * |t|⁻¹) * spectralStep b |t|

theorem spectralStep_mul (b x y : ℝ) :
    spectralStep b x * spectralStep b y = spectralStep b (min x y) := by
  by_cases hx : b ≤ x <;> by_cases hy : b ≤ y <;>
    simp [spectralStep, hx, hy]

theorem spectralStep_intervalIntegrable (x a b : ℝ) :
    IntervalIntegrable (fun s => spectralStep s x) volume a b := by
  apply Antitone.intervalIntegrable
  intro s t hst
  by_cases ht : t ≤ x
  · simp [spectralStep, ht, hst.trans ht]
  · simp only [spectralStep, ite_eq_right ht]
    exact spectralStep_nonneg s x

theorem signedSpectralStep_sq_sub_intervalIntegrable (x y a b : ℝ) :
    IntervalIntegrable (fun s => (signedSpectralStep s x - signedSpectralStep s y) ^ 2) volume a b := by
  have he : (fun s => (signedSpectralStep s x - signedSpectralStep s y) ^ 2) =
      (fun s => (x * |x|⁻¹) ^ 2 * spectralStep s |x| +
        (y * |y|⁻¹) ^ 2 * spectralStep s |y| -
        (2 * (x * |x|⁻¹) * (y * |y|⁻¹)) * spectralStep s (min |x| |y|)) := by
    funext s
    simp only [signedSpectralStep, sub_sq, mul_pow, spectralStep_sq]
    rw [← spectralStep_mul]
    ring
  rw [he]
  exact (((spectralStep_intervalIntegrable |x| a b).const_mul _).add
    ((spectralStep_intervalIntegrable |y| a b).const_mul _)).sub
      ((spectralStep_intervalIntegrable (min |x| |y|) a b).const_mul _)

theorem signedSpectralStep_eq_parts {b : ℝ} (hb : 0 < b) (t : ℝ) :
    signedSpectralStep b t = spectralStep b (max t 0) - spectralStep b (max (-t) 0) := by
  have hz : spectralStep b 0 = 0 := by simp [spectralStep, not_le_of_gt hb]
  rcases lt_trichotomy 0 t with ht | ht | ht
  · rw [max_eq_left ht.le, max_eq_right (neg_nonpos.mpr ht.le), hz, sub_zero]
    simp [signedSpectralStep, abs_of_pos ht, ne_of_gt ht]
  · subst t
    simp [signedSpectralStep, hz]
  · rw [max_eq_right ht.le, max_eq_left (neg_nonneg.mpr ht.le), hz, zero_sub]
    simp [signedSpectralStep, abs_of_neg ht, ne_of_lt ht]

theorem abs_sub_parts (x y : ℝ) :
    |max x 0 - max y 0| + |max (-x) 0 - max (-y) 0| = |x - y| := by
  have hp (t : ℝ) : max t 0 - max (-t) 0 = t := by
    rcases le_total 0 t with ht | ht
    · rw [max_eq_left ht, max_eq_right (neg_nonpos.mpr ht)]; ring
    · rw [max_eq_right ht, max_eq_left (neg_nonneg.mpr ht)]; ring
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr (max_le_max hxy le_rfl)),
      abs_of_nonneg (sub_nonneg.mpr (max_le_max (neg_le_neg hxy) le_rfl)),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    linarith [hp x, hp y]
  · rw [abs_of_nonneg (sub_nonneg.mpr (max_le_max hyx le_rfl)),
      abs_of_nonpos (sub_nonpos.mpr (max_le_max (neg_le_neg hyx) le_rfl)),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    linarith [hp x, hp y]

theorem signedSpectralStep_sq_sub_intervalIntegral_le (x y : ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ s in a..b, (signedSpectralStep s x - signedSpectralStep s y) ^ 2) ≤ 2 * |x - y| := by
  let f := fun s => (spectralStep s (max x 0) - spectralStep s (max y 0)) ^ 2
  let g := fun s => (spectralStep s (max (-x) 0) - spectralStep s (max (-y) 0)) ^ 2
  have hf : IntervalIntegrable f volume a b := (spectralStep_sq_sub_integrable _ _).intervalIntegrable
  have hg : IntervalIntegrable g volume a b := (spectralStep_sq_sub_integrable _ _).intervalIntegrable
  calc
    _ ≤ ∫ s in a..b, 2 * (f s + g s) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hab
        (signedSpectralStep_sq_sub_intervalIntegrable x y a b) ((hf.add hg).const_mul 2)
      intro s hs
      have hs0 : 0 < s := ha.trans_lt hs.1
      rw [signedSpectralStep_eq_parts hs0, signedSpectralStep_eq_parts hs0]
      dsimp only [f, g]
      nlinarith [sq_nonneg ((spectralStep s (max x 0) - spectralStep s (max y 0)) +
        (spectralStep s (max (-x) 0) - spectralStep s (max (-y) 0)))]
    _ = 2 * ((∫ s in a..b, f s) + ∫ s in a..b, g s) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hf hg]
    _ ≤ 2 * (|max x 0 - max y 0| + |max (-x) 0 - max (-y) 0|) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add (spectralStep_sq_sub_intervalIntegral_le a b _ _ hab)
        (spectralStep_sq_sub_intervalIntegral_le a b _ _ hab)
    _ = _ := by rw [abs_sub_parts]

variable {ι : Type*} [Fintype ι]

theorem weighted_signedSpectralStep_intervalIntegrable (a b : ℝ) (c x y : ι → ℝ) :
    IntervalIntegrable (fun s => ∑ i, c i * (signedSpectralStep s (x i) - signedSpectralStep s (y i)) ^ 2)
      volume a b := by
  have he : (fun s => ∑ i, c i * (signedSpectralStep s (x i) - signedSpectralStep s (y i)) ^ 2) =
      ∑ i, (fun s => c i * (signedSpectralStep s (x i) - signedSpectralStep s (y i)) ^ 2) := by
    funext s
    simp only [Finset.sum_apply]
  rw [he]
  exact IntervalIntegrable.sum Finset.univ fun i _ =>
    (signedSpectralStep_sq_sub_intervalIntegrable _ _ a b).const_mul _

theorem weighted_signedSpectralStep_coarea (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (c x y : ι → ℝ) (hc : ∀ i, 0 ≤ c i) :
    (∫ s in a..b, ∑ i, c i * (signedSpectralStep s (x i) - signedSpectralStep s (y i)) ^ 2) ≤
      2 * Real.sqrt ((∑ i, c i) * ∑ i, c i * (x i - y i) ^ 2) := by
  calc
    _ = ∑ i, c i * ∫ s in a..b, (signedSpectralStep s (x i) - signedSpectralStep s (y i)) ^ 2 := by
      rw [intervalIntegral.integral_finsetSum]
      · simp only [intervalIntegral.integral_const_mul]
      · intro i _
        exact (signedSpectralStep_sq_sub_intervalIntegrable _ _ a b).const_mul _
    _ ≤ ∑ i, c i * (2 * |x i - y i|) := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (signedSpectralStep_sq_sub_intervalIntegral_le _ _ ha hab) (hc i)
    _ = 2 * ∑ i, c i * |x i - y i| := by simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.le_sqrt_of_sq_le (weighted_abs_sum_sq_le c (fun i => x i - y i) hc)) (by norm_num)

end ThomGame.Analysis

module

public import ThomGame.Analysis.ALTLogarithmicParameters
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The actual logarithmic scale in ALT (4.5)

For alpha <= exp(-16), use (log(1/alpha))^(-1/8), and use 1 elsewhere.
The scale tends to zero with positive alpha and verifies both the
polynomial and exponential smallness required in the decomposition.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

noncomputable def altDecompositionScale (α : ℝ) : ℝ :=
  if 0 < α ∧ α ≤ Real.exp (-16) then (Real.log (1 / α)) ^ (-(1 / 8 : ℝ)) else 1

theorem altDecompositionScale_eq {α : ℝ} (hα : 0 < α) (hsmall : α ≤ Real.exp (-16)) :
    altDecompositionScale α = (Real.log (1 / α)) ^ (-(1 / 8 : ℝ)) := by
  simp only [altDecompositionScale, hα, hsmall, and_self, ite_true]

theorem alt_inverse_eighth_four {t : ℝ} (ht : 0 ≤ t) :
    (t ^ (-(1 / 8 : ℝ))) ^ 4 = (Real.sqrt t)⁻¹ := by
  rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul ht,
    show (-(1 / 8 : ℝ)) * ((4 : Nat) : ℝ) = -(1 / 2 : ℝ) by norm_num,
    Real.rpow_neg ht, ← Real.sqrt_eq_rpow]

theorem alt_exp_neg_le_inv_sqrt {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (-t) ≤ (Real.sqrt t)⁻¹ := by
  have hp : 0 < t := by linarith
  have hs := (Real.sqrt_le_self_iff).mpr (Or.inr ht)
  have he : Real.sqrt t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hi := (inv_le_inv₀ (Real.exp_pos t) (Real.sqrt_pos.mpr hp)).mpr he
  simpa only [← Real.exp_neg] using hi

theorem alt_nine_exp_neg_le_exp_neg_sqrt {t : ℝ} (ht : 16 ≤ t) :
    9 * Real.exp (-t) ≤ Real.exp (-Real.sqrt t) := by
  have hs : Real.sqrt t ≤ t / 2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by linarith, ?_⟩
    nlinarith [mul_nonneg (show 0 ≤ t by linarith) (show 0 ≤ t - 16 by linarith)]
  have he : 9 ≤ Real.exp (t / 2) := by linarith [Real.add_one_le_exp (t / 2)]
  calc
    _ ≤ Real.exp (t / 2) * Real.exp (-t) := mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = Real.exp (-(t / 2)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (neg_le_neg hs)

theorem altDecompositionScale_pos (α : ℝ) : 0 < altDecompositionScale α := by
  unfold altDecompositionScale
  split_ifs with hh
  · have ht := (alt_logarithmic_parameters hh.1 hh.2).1
    exact Real.rpow_pos_of_pos (by linarith) _
  · norm_num

theorem altDecompositionScale_small_bounds {α : ℝ} (hα : 0 < α) (hsmall : α ≤ Real.exp (-16)) :
    α ≤ altDecompositionScale α ^ 4 ∧ 9 * α ≤ Real.exp (-(altDecompositionScale α ^ 4)⁻¹) := by
  have ht := (alt_logarithmic_parameters hα hsmall).1
  have ht16 : 16 ≤ Real.log (1 / α) := by linarith
  have hid : Real.exp (-Real.log (1 / α)) = α := by
    rw [one_div, Real.log_inv, neg_neg, Real.exp_log hα]
  rw [altDecompositionScale_eq hα hsmall, alt_inverse_eighth_four (by linarith), inv_inv]
  constructor
  · simpa only [hid] using alt_exp_neg_le_inv_sqrt (show 1 ≤ Real.log (1 / α) by linarith only [ht16])
  · simpa only [hid] using alt_nine_exp_neg_le_exp_neg_sqrt ht16

theorem altDecompositionScale_tendsto_zero {ι : Type*} {L : Filter ι} {α : ι → ℝ}
    (hα : ∀ i, 0 < α i) (hlim : Tendsto α L (𝓝 0)) :
    Tendsto (fun i => altDecompositionScale (α i)) L (𝓝 0) := by
  have hpos : Tendsto α L (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨hlim, Filter.Eventually.of_forall hα⟩
  have hi := tendsto_inv_nhdsGT_zero.comp hpos
  have ht := Real.tendsto_log_atTop.comp hi
  have hraw := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp ht
  have hsmall : ∀ᶠ i in L, α i ≤ Real.exp (-16) := hlim.eventually_le_const (Real.exp_pos _)
  apply hraw.congr'
  filter_upwards [hsmall] with i hi
  simpa only [Function.comp_apply, one_div] using (altDecompositionScale_eq (hα i) hi).symm

theorem altDecompositionScale_eventually_admissible {ι : Type*} {L : Filter ι} {α : ι → ℝ}
    (hα : ∀ i, 0 < α i) (hlim : Tendsto α L (𝓝 0)) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ i in L,
      altDecompositionScale (α i) ≤ 1 / 8 ∧
      altDecompositionScale (α i) ≤ κ / 1024 ∧
      (1 + 61440 / (κ * Real.sqrt κ)) * altDecompositionScale (α i) ≤ 1 ∧
      α i ≤ altDecompositionScale (α i) ^ 4 ∧
      9 * α i ≤ Real.exp (-(altDecompositionScale (α i) ^ 4)⁻¹) := by
  have hη := altDecompositionScale_tendsto_zero hα hlim
  have hη8 := hη.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 8)
  have hηκ := hη.eventually_le_const (div_pos hκ (by norm_num : (0 : ℝ) < 1024))
  have hC : Tendsto (fun i => (1 + 61440 / (κ * Real.sqrt κ)) * altDecompositionScale (α i)) L (𝓝 0) := by
    simpa only [mul_zero] using hη.const_mul (1 + 61440 / (κ * Real.sqrt κ))
  have hsmall : ∀ᶠ i in L, α i ≤ Real.exp (-16) := hlim.eventually_le_const (Real.exp_pos _)
  filter_upwards [hη8, hηκ, hC.eventually_le_const zero_lt_one, hsmall] with i hi8 hiκ hiC hiα
  exact ⟨hi8, hiκ, hiC, altDecompositionScale_small_bounds (hα i) hiα⟩

end ThomGame.Analysis

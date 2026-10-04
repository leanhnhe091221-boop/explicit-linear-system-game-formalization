module

public import ThomGame.Analysis.MatrixALTPrunedDecomposition

/-! Conservative scalar estimates for the original finite ALT edit constants. -/

@[expose] public section
namespace ThomGame.Analysis

theorem finiteUCP_altPrunedEditBound_le {κ η : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hη : 0 ≤ η) (hη1 : η ≤ 1) :
    altPrunedEditBound κ η ≤ (2 : ℝ) ^ 42 * κ⁻¹ ^ 3 * η := by
  have hr : 1 ≤ κ⁻¹ := (one_le_inv₀ hκ).mpr hκ1
  have hr0 : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
  have hr3 : 1 ≤ κ⁻¹ ^ 3 := one_le_pow₀ hr
  have hr13 : κ⁻¹ ≤ κ⁻¹ ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hr (by decide : (1 : ℕ) ≤ 3)
  have hr23 : κ⁻¹ ^ 2 ≤ κ⁻¹ ^ 3 := pow_le_pow_right₀ hr (by decide : (2 : ℕ) ≤ 3)
  have he : η ^ 2 ≤ η := by nlinarith
  have h0 : η ^ 2 ≤ κ⁻¹ ^ 3 * η := he.trans (le_mul_of_one_le_left hη hr3)
  have h1 : κ⁻¹ ^ 2 * η ≤ κ⁻¹ ^ 3 * η := mul_le_mul_of_nonneg_right hr23 hη
  have h2 : η ≤ κ⁻¹ ^ 3 * η := le_mul_of_one_le_left hη hr3
  have h3 : κ⁻¹ * η ^ 2 ≤ κ⁻¹ ^ 3 * η :=
    (mul_le_mul_of_nonneg_left he hr0).trans (mul_le_mul_of_nonneg_right hr13 hη)
  have hpos : 0 ≤ κ⁻¹ ^ 3 * η := mul_nonneg (pow_nonneg hr0 _) hη
  unfold altPrunedEditBound altPrunedTraceBound altBlockErrorBound
  simp only [div_eq_mul_inv]
  norm_num only [show (2 : ℝ) ^ 42 = 4398046511104 by norm_num]
  nlinarith only [h0, h1, h2, h3, hpos]

/-- The explicit heat-channel edit parameter used in the companion calculation
satisfies the corrected-channel hypothesis of the finite reconstruction. -/
theorem finiteUCP_altPrunedEditBound_heat_parameter {κ η : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hη : 0 ≤ η) (hη1 : η ≤ 1) :
    altPrunedEditBound κ η ≤
      2 * ((2 : ℝ) ^ 22 * κ⁻¹ ^ 2 * Real.sqrt η) ^ 2 := by
  have hr : 1 ≤ κ⁻¹ := (one_le_inv₀ hκ).mpr hκ1
  have hpow : κ⁻¹ ^ 3 ≤ κ⁻¹ ^ 4 := pow_le_pow_right₀ hr (by decide : (3 : ℕ) ≤ 4)
  have hmul := mul_le_mul_of_nonneg_right hpow hη
  have hnonneg : 0 ≤ κ⁻¹ ^ 4 * η := mul_nonneg (pow_nonneg (inv_nonneg.mpr hκ.le) _) hη
  have hs := Real.sq_sqrt hη
  exact (finiteUCP_altPrunedEditBound_le hκ hκ1 hη hη1).trans (by
    simp only [mul_pow, hs, ← pow_mul]
    norm_num only [show (22 : ℕ) * 2 = 44 from rfl, show (2 : ℕ) * 2 = 4 from rfl]
    nlinarith only [hmul, hnonneg])

end ThomGame.Analysis

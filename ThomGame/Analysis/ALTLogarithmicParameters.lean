module

public import ThomGame.Analysis.MatrixALTOrthogonalFamily

/-!
# Explicit parameters for ALT Proposition 3.5

The exponential parameterization gives absolute constants, independent
of the matrix dimension and the number of projections. The logarithmic
form is obtained with `t = log (1 / s) / 16`.
-/

@[expose] public section
namespace ThomGame.Analysis

theorem alt_exp_neg_two_le_inv_sqrt {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (-2 * t) ≤ (Real.sqrt t)⁻¹ := by
  have hp : 0 < t := by linarith
  have he : Real.sqrt t ≤ Real.exp (2 * t) := by
    have hs : Real.sqrt t ≤ t := (Real.sqrt_le_self_iff).mpr (Or.inr ht)
    have hh := Real.add_one_le_exp (2 * t)
    linarith
  have hi := (inv_le_inv₀ (Real.exp_pos (2 * t)) (Real.sqrt_pos.mpr hp)).mpr he
  simpa only [← Real.exp_neg, neg_mul] using hi

theorem alt_exponential_energy_bound {t : ℝ} (ht : 1 ≤ t) :
    2 * Real.exp (-16 * t) +
        8 * Real.exp (4 * t) * Real.sqrt (Real.exp (-16 * t)) / Real.exp (-2 * t) +
        64 * t ^ (-(1 / 2 : ℝ)) ≤ 74 * (Real.sqrt t)⁻¹ := by
  have hs : Real.sqrt (Real.exp (-16 * t)) = Real.exp (-8 * t) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  have he : Real.exp (4 * t) * Real.exp (-8 * t) / Real.exp (-2 * t) =
      Real.exp (-2 * t) := by
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    ring
  have hpow : t ^ (-(1 / 2 : ℝ)) = (Real.sqrt t)⁻¹ := by
    rw [Real.rpow_neg (by linarith : 0 ≤ t), ← Real.sqrt_eq_rpow]
  have htwo := alt_exp_neg_two_le_inv_sqrt ht
  have hsixteen : Real.exp (-16 * t) ≤ (Real.sqrt t)⁻¹ :=
    (Real.exp_le_exp.mpr (by linarith)).trans htwo
  rw [hs, mul_assoc 8, mul_div_assoc, he, hpow]
  linarith

theorem alt_logarithmic_parameters {s : ℝ} (hs : 0 < s)
    (hsmall : s ≤ Real.exp (-16)) :
    1 ≤ Real.log (1 / s) / 16 ∧
      Real.exp (-16 * (Real.log (1 / s) / 16)) = s ∧
      (Real.sqrt (Real.log (1 / s) / 16))⁻¹ = 4 * (Real.sqrt (Real.log (1 / s)))⁻¹ := by
  have hl : Real.log s ≤ -16 := by
    simpa only [Real.log_exp] using Real.log_le_log hs hsmall
  have hi : Real.log (1 / s) = -Real.log s := by rw [one_div, Real.log_inv]
  have hp : 0 ≤ Real.log (1 / s) := by rw [hi]; linarith
  refine ⟨by rw [hi]; linarith, ?_, ?_⟩
  · rw [hi]
    convert Real.exp_log hs using 1
    congr 1
    ring
  · rw [Real.sqrt_div hp]
    have h16 : Real.sqrt (16 : ℝ) = 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
    rw [h16, inv_div, div_eq_mul_inv]

end ThomGame.Analysis

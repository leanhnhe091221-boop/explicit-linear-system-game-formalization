module

public import ThomGame.Analysis.ALTLogarithmicParameters

/-!
# Explicit small parameters for ALT Proposition 3.6

For `0 < eta ≤ 1/8`, choose `gamma = exp (-1 / (16 eta^4))`
and the orthogonalization time `t = 1 / (256 eta^4)`.
-/

@[expose] public section
namespace ThomGame.Analysis

theorem alt_inverse_four_large {η : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8) :
    4096 ≤ (η ^ 4)⁻¹ := by
  have hp : η ^ 4 ≤ (1 / 8 : ℝ) ^ 4 := by gcongr
  have hi := (inv_le_inv₀ (by norm_num : (0 : ℝ) < (1 / 8) ^ 4) (pow_pos hη 4)).mpr hp
  norm_num at hi
  exact hi

theorem alt_inverse_four_sqrt_scale (η : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    (Real.sqrt ((η ^ 4)⁻¹ / c ^ 2))⁻¹ = c * η ^ 2 := by
  rw [Real.sqrt_div (by positivity), Real.sqrt_inv,
    show η ^ 4 = (η ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg η), Real.sqrt_sq hc,
    inv_div, div_eq_mul_inv, inv_inv]

theorem alt_correction_parameters {η : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8) :
    let γ := Real.exp (-(η ^ 4)⁻¹ / 16)
    let t := (η ^ 4)⁻¹ / 256
    0 < γ ∧ γ ≤ η ∧ γ ≤ 1 / 4 ∧
      γ ^ 16 = Real.exp (-(η ^ 4)⁻¹) ∧
      100 * γ ^ 2 ≤ Real.exp (-16 * t) ∧
      1 ≤ t ∧ (Real.sqrt t)⁻¹ = 16 * η ^ 2 := by
  dsimp only
  have hx := alt_inverse_four_large hη hη8
  have hγ : Real.exp (-(η ^ 4)⁻¹ / 16) ≤ η := by
    have he := alt_exp_neg_two_le_inv_sqrt (show 1 ≤ (η ^ 4)⁻¹ / 32 by linarith)
    have hs : (Real.sqrt ((η ^ 4)⁻¹ / 32))⁻¹ ≤ (Real.sqrt ((η ^ 4)⁻¹ / 64))⁻¹ := by
      apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
      apply Real.sqrt_le_sqrt
      linarith
    have hscale : (Real.sqrt ((η ^ 4)⁻¹ / 64))⁻¹ = 8 * η ^ 2 := by
      convert alt_inverse_four_sqrt_scale η (by norm_num : (0 : ℝ) ≤ 8) using 1
      norm_num
    have he' : Real.exp (-(η ^ 4)⁻¹ / 16) ≤ 8 * η ^ 2 := by
      convert he.trans (hs.trans_eq hscale) using 1
      congr 1
      ring
    nlinarith
  refine ⟨Real.exp_pos _, hγ, by linarith, ?_, ?_, by linarith, ?_⟩
  · rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  · have he : 100 ≤ Real.exp ((η ^ 4)⁻¹ / 16) := by
      have hh := Real.add_one_le_exp ((η ^ 4)⁻¹ / 16)
      linarith
    calc
      _ ≤ Real.exp ((η ^ 4)⁻¹ / 16) * Real.exp (-(η ^ 4)⁻¹ / 16) ^ 2 :=
        mul_le_mul_of_nonneg_right he (sq_nonneg _)
      _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        norm_num
        ring
  · convert alt_inverse_four_sqrt_scale η (by norm_num : (0 : ℝ) ≤ 16) using 1
    norm_num

end ThomGame.Analysis

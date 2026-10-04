module

public import ThomGame.Quantum.RegularHilbertSpace
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Linarith

/-! The normalized difference of the identity and central-involution delta vectors. -/

@[expose] public section
namespace ThomGame.Quantum.GroupHilbert

open scoped Classical

variable {G : Type*} [Group G]

noncomputable def centralState (J : G) : GroupHilbert G :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (delta 1 - delta J)

theorem centralState_norm_sq (J : G) (hJ : J ≠ 1) : ‖centralState J‖ ^ 2 = 1 := by
  have hn : ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ)‖ = (Real.sqrt 2)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    positivity
  rw [centralState, norm_smul, mul_pow, hn, norm_sub_sq (𝕜 := ℂ), delta_norm,
    delta_norm, delta_inner, ite_eq_right (Ne.symm hJ)]
  simp only [one_pow]
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem centralState_norm (J : G) (hJ : J ≠ 1) : ‖centralState J‖ = 1 := by
  have hs := centralState_norm_sq J hJ
  nlinarith [norm_nonneg (centralState J)]

theorem left_centralState (J : G) (hJ : J * J = 1) : left J (centralState J) = -centralState J := by
  simp only [centralState, map_smul, map_sub, left_delta, mul_one, hJ]
  module

theorem left_right_centralState (J g : G) (hg : g * g = 1) (hc : Commute J g) :
    left g (centralState J) = right g (centralState J) := by
  have hi : g⁻¹ = g := by
    calc
      g⁻¹ = g⁻¹ * (g * g) := by rw [hg, mul_one]
      _ = g := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  simp only [centralState, map_smul, map_sub, left_delta, right_delta, one_mul, mul_one, hi, hc.eq]

end ThomGame.Quantum.GroupHilbert

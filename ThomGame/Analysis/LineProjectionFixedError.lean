module

public import ThomGame.Analysis.LineProjectionPerturbation

/-!
# Replacing an approximate rank-one direction by a nearly fixed vector

The estimate uses the actual line projections. It also covers a zero
projection of the vector onto the original line.
-/

@[expose] public section
namespace ThomGame.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem lineProjection_distance_le_residual (x u : H) (hx : x ≠ 0) :
    ‖(ℂ ∙ x).starProjection - (ℂ ∙ u).starProjection‖ ≤
      4 * ‖x - (ℂ ∙ u).starProjection x‖ / ‖x‖ := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let y := (ℂ ∙ u).starProjection x
  by_cases hy : y = 0
  · have hh := norm_sub_le (ℂ ∙ x).starProjection (ℂ ∙ u).starProjection
    have hpx := (ℂ ∙ x).starProjection_norm_le
    have hpu := (ℂ ∙ u).starProjection_norm_le
    change ‖(ℂ ∙ x).starProjection - (ℂ ∙ u).starProjection‖ ≤ 4 * ‖x - y‖ / ‖x‖
    rw [hy, sub_zero, mul_div_cancel_right₀ 4 hn.ne']
    linarith
  · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ((ℂ ∙ u).starProjection_apply_mem x)
    have hcne : c ≠ 0 := by
      intro hz
      exact hy (by simpa only [hz, zero_smul] using hc.symm)
    have hspan : ℂ ∙ y = ℂ ∙ u := by
      change ℂ ∙ (ℂ ∙ u).starProjection x = _
      rw [← hc]
      exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hcne) u
    have hh := lineProjection_distance_le x y hx hy
    simpa only [hspan] using hh

theorem operator_lineProjection_of_fixed_error (T : H →L[ℂ] H) (u x : H) (hx : x ≠ 0)
    (a b : ℝ) (hT : ‖T - (ℂ ∙ u).starProjection‖ ≤ a) (hfix : ‖T x - x‖ ≤ b * ‖x‖) :
    ‖T - (ℂ ∙ x).starProjection‖ ≤ 5 * a + 4 * b := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hres : ‖x - (ℂ ∙ u).starProjection x‖ ≤ (a + b) * ‖x‖ := by
    have hh := norm_add_le (x - T x) ((T - (ℂ ∙ u).starProjection) x)
    have hop := (T - (ℂ ∙ u).starProjection).le_opNorm x
    rw [sub_apply] at hop
    rw [sub_apply, sub_add_sub_cancel, norm_sub_rev x (T x)] at hh
    have hb := mul_le_mul_of_nonneg_right hT hn.le
    linarith
  have hd := (le_div_iff₀ hn).mp (lineProjection_distance_le_residual x u hx)
  have hd' : ‖(ℂ ∙ x).starProjection - (ℂ ∙ u).starProjection‖ ≤ 4 * (a + b) := by
    nlinarith
  have hh := norm_add_le (T - (ℂ ∙ u).starProjection)
    ((ℂ ∙ u).starProjection - (ℂ ∙ x).starProjection)
  rw [sub_add_sub_cancel, norm_sub_rev (ℂ ∙ u).starProjection (ℂ ∙ x).starProjection] at hh
  linarith

end ThomGame.Analysis

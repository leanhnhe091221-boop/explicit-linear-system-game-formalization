module

public import ThomGame.Analysis.OrthonormalOperatorBounds
public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Quantitative perturbation of actual one-dimensional orthogonal projections

Unit vectors give a direct rank-one formula. Normalization costs at most
twice the relative vector distance, uniformly in the ambient dimension.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped InnerProductSpace

theorem normalized_vectors_distance_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x y : V) (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤ 2 * ‖x - y‖ / ‖x‖ := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have he : ‖x‖ • (NormedSpace.normalize x - NormedSpace.normalize y) =
      (x - y) + (‖y‖ - ‖x‖) • NormedSpace.normalize y := by
    rw [smul_sub, NormedSpace.norm_smul_normalize, sub_smul, NormedSpace.norm_smul_normalize]
    abel
  have hb := norm_add_le (x - y) ((‖y‖ - ‖x‖) • NormedSpace.normalize y)
  rw [← he, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hn, NormedSpace.norm_normalize hy, mul_one] at hb
  have hd := abs_norm_sub_norm_le y x
  rw [norm_sub_rev y x] at hd
  apply (le_div_iff₀ hn).mpr
  nlinarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem unit_lineProjection_distance_le (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖(ℂ ∙ x).starProjection - (ℂ ∙ y).starProjection‖ ≤ 2 * ‖x - y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  have hp (v : H) (hv : ‖v‖ = 1) : (ℂ ∙ v).starProjection z = inner ℂ v z • v := by
    rw [Submodule.starProjection_singleton]
    change (inner ℂ v z / ((‖v‖ ^ 2 : ℝ) : ℂ)) • v = _
    rw [hv]
    norm_num
  rw [sub_apply, hp x hx, hp y hy]
  have he : inner ℂ x z • x - inner ℂ y z • y =
      inner ℂ x z • (x - y) + inner ℂ (x - y) z • y := by
    rw [inner_sub_left, smul_sub, sub_smul]
    abel
  rw [he]
  have h1 : ‖inner ℂ x z‖ ≤ ‖z‖ := by simpa only [hx, one_mul] using norm_inner_le_norm x z
  have h2 := norm_inner_le_norm (𝕜 := ℂ) (x - y) z
  have hb := norm_add_le (inner ℂ x z • (x - y)) (inner ℂ (x - y) z • y)
  rw [norm_smul, norm_smul, hy, mul_one] at hb
  have hc := mul_le_mul_of_nonneg_right h1 (norm_nonneg (x - y))
  nlinarith

theorem lineProjection_distance_le (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖(ℂ ∙ x).starProjection - (ℂ ∙ y).starProjection‖ ≤ 4 * ‖x - y‖ / ‖x‖ := by
  let : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  have hx' : ℂ ∙ NormedSpace.normalize x = ℂ ∙ x := by
    change ℂ ∙ (((‖x‖⁻¹ : ℝ) : ℂ) • x) = ℂ ∙ x
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr
      (Complex.ofReal_ne_zero.mpr (inv_ne_zero (norm_ne_zero_iff.mpr hx)))) x
  have hy' : ℂ ∙ NormedSpace.normalize y = ℂ ∙ y := by
    change ℂ ∙ (((‖y‖⁻¹ : ℝ) : ℂ) • y) = ℂ ∙ y
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr
      (Complex.ofReal_ne_zero.mpr (inv_ne_zero (norm_ne_zero_iff.mpr hy)))) y
  have he := unit_lineProjection_distance_le (NormedSpace.normalize x) (NormedSpace.normalize y)
    (NormedSpace.norm_normalize hx) (NormedSpace.norm_normalize hy)
  simp only [hx', hy'] at he
  have hb := mul_le_mul_of_nonneg_left (normalized_vectors_distance_le x y hx hy) (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ ≤ 2 * ‖NormedSpace.normalize x - NormedSpace.normalize y‖ := he
    _ ≤ 2 * (2 * ‖x - y‖ / ‖x‖) := hb
    _ = _ := by ring

theorem lineProjection_distance_sq (x y : H) (hx : x ≠ 0) (hy : y ≠ 0)
    (epsilon : ℝ) (hdist : ‖x - y‖ ^ 2 ≤ epsilon * ‖x‖ ^ 2) :
    ‖(ℂ ∙ x).starProjection - (ℂ ∙ y).starProjection‖ ^ 2 ≤ 16 * epsilon := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have he := (le_div_iff₀ hn).mp (lineProjection_distance_le x y hx hy)
  have hs := (sq_le_sq₀ (mul_nonneg (norm_nonneg _) hn.le) (by positivity)).mpr he
  have hc : 0 < ‖x‖ ^ 2 := sq_pos_of_pos hn
  nlinarith only [hs, hdist, hc]

end ThomGame.Analysis

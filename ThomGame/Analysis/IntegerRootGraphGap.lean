module

public import ThomGame.Analysis.IntegerRootGraphEnergy
public import ThomGame.Analysis.IntegerRootGraphMean

/-! The exact constant kernel and the dimension-independent gap four of the six-root graph. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis.IntegerRootGraph

open Compressor ThomGame.IntegerRootGraph
open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem laplacian_zero_sum_formula (f : VertexHilbert H) (hf : vertexSum f = 0) :
    laplacian f = (5 : ℂ) • f + opposite f := by
  have ht : total f = 0 := by
    ext r
    change vertexSum f = 0
    exact hf
  rw [laplacian_operator_formula]
  change (5 : ℂ) • f + opposite f - total f = _
  rw [ht, sub_zero]

theorem laplacian_zero_sum_gap (f : VertexHilbert H) (hf : vertexSum f = 0) :
    4 * ‖f‖ ^ 2 ≤ (inner ℂ f (laplacian f)).re := by
  have hs : (inner ℂ f ((5 : ℂ) • f)).re = 5 * ‖f‖ ^ 2 := by
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
    norm_num [Complex.mul_re]
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have h := re_inner_le_norm (𝕜 := ℂ) (-f) (opposite f)
  simp only [inner_neg_left, map_neg, RCLike.re_to_complex, norm_neg, opposite_norm] at h
  rw [laplacian_zero_sum_formula f hf, inner_add_right, Complex.add_re, hs]
  nlinarith

theorem laplacian_zero_sum_norm_le (f : VertexHilbert H) (hf : vertexSum f = 0) :
    4 * ‖f‖ ≤ ‖laplacian f‖ := by
  by_cases hz : f = 0
  · simp [hz]
  have hn := norm_pos_iff.mpr hz
  have h := (laplacian_zero_sum_gap f hf).trans (re_inner_le_norm (𝕜 := ℂ) f (laplacian f))
  apply (mul_le_mul_iff_left₀ hn).mp
  nlinarith

theorem edgeEnergy_residual (f : VertexHilbert H) : edgeEnergy (f - mean f) = edgeEnergy f := by
  simp only [edgeEnergy, mean_eq_constant, PiLp.sub_apply, constant_apply, sub_sub_sub_cancel_right]

theorem graph_residual_gap (f : VertexHilbert H) : 4 * ‖f - mean f‖ ^ 2 ≤ edgeEnergy f := by
  have h := laplacian_zero_sum_gap (f - mean f) (vertexSum_residual f)
  rwa [laplacian_energy, edgeEnergy_residual] at h

theorem laplacian_kernel : (laplacian : VertexHilbert H →L[ℂ] VertexHilbert H).ker = constantSpace := by
  ext f
  constructor
  · intro hf
    change laplacian f = 0 at hf
    have h := laplacian_zero_sum_gap (f - mean f) (vertexSum_residual f)
    rw [laplacian_residual, hf, inner_zero_right, Complex.zero_re] at h
    have hz : ‖f - mean f‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖f - mean f‖]
    have he : f = mean f := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
    rw [he]
    exact mean_mem f
  · intro hf
    obtain ⟨ξ, rfl⟩ := (mem_constantSpace f).mp hf
    exact laplacian_constant ξ

theorem laplacian_gap (f : VertexHilbert H)
    (hf : f ∈ (laplacian : VertexHilbert H →L[ℂ] VertexHilbert H).kerᗮ) :
    4 * ‖f‖ ^ 2 ≤ (inner ℂ f (laplacian f)).re := by
  rw [laplacian_kernel, constantSpace_orthogonal_iff] at hf
  exact laplacian_zero_sum_gap f hf

def green : VertexHilbert H →L[ℂ] VertexHilbert H :=
  (1 / 24 : ℂ) • ((5 : ℂ) • 1 - opposite)

theorem green_apply (f : VertexHilbert H) : green f = (1 / 24 : ℂ) • ((5 : ℂ) • f - opposite f) := rfl

theorem vertexSum_green (f : VertexHilbert H) : vertexSum (green f) = (1 / 6 : ℂ) • vertexSum f := by
  rw [green_apply, map_smul, map_sub, map_smul, vertexSum_opposite]
  module

theorem laplacian_green (f : VertexHilbert H) : laplacian (green f) = f - mean f := by
  have ht : total (green f) = mean f := by
    change constant (vertexSum (green f)) = mean f
    rw [vertexSum_green, mean_eq_constant]
  have ho : opposite (green f) = (1 / 24 : ℂ) • ((5 : ℂ) • opposite f - f) := by
    rw [green_apply, map_smul, map_sub, map_smul, opposite_opposite]
  rw [laplacian_operator_formula]
  change (5 : ℂ) • green f + opposite (green f) - total (green f) = _
  rw [ht, ho, green_apply]
  module

theorem green_laplacian (f : VertexHilbert H) : green (laplacian f) = f - mean f := by
  ext r
  change (1 / 24 : ℂ) • ((5 : ℂ) • laplacian f r - laplacian f (reverse r)) = f r - mean f r
  rw [laplacian_closed_form, laplacian_closed_form, reverse_reverse, mean_eq_constant, constant_apply,
    vertexSum_apply]
  module

theorem green_norm_le (f : VertexHilbert H) : ‖green f‖ ≤ (1 / 4 : ℝ) * ‖f‖ := by
  have h := norm_sub_le ((5 : ℂ) • f) (opposite f)
  rw [norm_smul, opposite_norm] at h
  norm_num at h
  rw [green_apply, norm_smul]
  norm_num
  nlinarith

end ThomGame.Analysis.IntegerRootGraph

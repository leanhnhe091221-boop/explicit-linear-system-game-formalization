module

public import ThomGame.Analysis.IntegerRootGraphComplementGap
public import ThomGame.Analysis.HilbertProjectionLowerDuality

/-! A strict angle gap between constant fields and the actual vertex fixed fields. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis.IntegerRootGraph

open Compressor IntegralShear ThomGame.IntegerRootGraph
open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem decomposition_residual_mem (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (x : VertexHilbert H)
    (hx : x ∈ decompositionSpace ρ) : x - mean x ∈ zeroSumDecomposition ρ :=
  ⟨(decompositionSpace ρ).sub_mem hx (constants_le_decomposition ρ (mean_mem x)), vertexSum_residual x⟩

omit [CompleteSpace H] in
theorem zeroSumDecomposition_le_constant_orthogonal (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) :
    zeroSumDecomposition ρ ≤ (constantSpace : Submodule ℂ (VertexHilbert H))ᗮ := by
  intro x hx
  exact (constantSpace_orthogonal_iff x).mpr hx.2

theorem zeroSumDecomposition_starProjection (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (x : VertexHilbert H)
    (hx : x ∈ decompositionSpace ρ) : (zeroSumDecomposition ρ).starProjection x = x - mean x := by
  apply Submodule.eq_starProjection_of_mem_orthogonal (decomposition_residual_mem ρ x hx)
  have hmean : mean x ∈ (zeroSumDecomposition ρ)ᗮ :=
    Submodule.orthogonal_le (zeroSumDecomposition_le_constant_orthogonal ρ)
      ((constantSpace : Submodule ℂ (VertexHilbert H)).le_orthogonal_orthogonal (mean_mem x))
  have heq : x - (x - mean x) = mean x := by abel
  rwa [heq]

theorem decomposition_orthogonal_zeroSum_mem_constant (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H))
    (x : VertexHilbert H) (hx : x ∈ decompositionSpace ρ) (ho : x ∈ (zeroSumDecomposition ρ)ᗮ) :
    x ∈ constantSpace := by
  have hp := (zeroSumDecomposition ρ).starProjection_apply_eq_zero_iff.mpr ho
  rw [zeroSumDecomposition_starProjection ρ x hx, sub_eq_zero] at hp
  rw [hp]
  exact mean_mem x

theorem fixedFields_inf_zeroSum_orthogonal (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H))
    (hρ : hilbertUnitaryInvariants ρ = ⊥) : fixedFields ρ ⊓ (zeroSumDecomposition ρ)ᗮ = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hc := decomposition_orthogonal_zeroSum_mem_constant ρ x (fixedFields_le_decomposition ρ hx.1) hx.2
  have hm : x ∈ constantSpace ⊓ fixedFields ρ := ⟨hc, hx.1⟩
  rwa [constants_inf_fixedFields ρ hρ] at hm

theorem fixedFields_distance_to_constants (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H))
    (hρ : hilbertUnitaryInvariants ρ = ⊥) (w : VertexHilbert H) (hw : w ∈ fixedFields ρ) :
    (1 / 4 : ℝ) * ‖w‖ ≤ ‖w - mean w‖ := by
  have h := subspaceProjection_lower_dual (zeroSumDecomposition ρ) (fixedFields ρ) (1 / 4 : ℝ)
    (by norm_num)
    (fun a ha => zeroSumDecomposition_fixed_projection_lower ρ a ha.1 ha.2)
    (fixedFields_inf_zeroSum_orthogonal ρ hρ) w hw
  rwa [zeroSumDecomposition_starProjection ρ w (fixedFields_le_decomposition ρ hw)] at h

theorem fixedFields_mean_gap (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H))
    (hρ : hilbertUnitaryInvariants ρ = ⊥) (w : VertexHilbert H) (hw : w ∈ fixedFields ρ) :
    ‖mean w‖ ^ 2 ≤ (15 / 16 : ℝ) * ‖w‖ ^ 2 := by
  have h := fixedFields_distance_to_constants ρ hρ w hw
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ (1 / 4 : ℝ) * ‖w‖) h 2
  have hp := (constantSpace : Submodule ℂ (VertexHilbert H)).norm_sq_eq_add_norm_sq_starProjection w
  rw [Submodule.starProjection_orthogonal_val, constantSpace_starProjection] at hp
  nlinarith

theorem constants_distance_to_fixedFields (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H))
    (hρ : hilbertUnitaryInvariants ρ = ⊥) (u : VertexHilbert H) (hu : u ∈ constantSpace) :
    (1 / 16 : ℝ) * ‖u‖ ^ 2 ≤ ‖u - (fixedFields ρ).starProjection u‖ ^ 2 := by
  let w := (fixedFields ρ).starProjection u
  have hw : w ∈ fixedFields ρ := (fixedFields ρ).starProjection_apply_mem u
  have hm := fixedFields_mean_gap ρ hρ w hw
  have hinner : inner ℂ u (mean w) = inner ℂ w w := by
    rw [← constantSpace_starProjection,
      ← (constantSpace : Submodule ℂ (VertexHilbert H)).inner_starProjection_left_eq_right,
      (constantSpace : Submodule ℂ (VertexHilbert H)).starProjection_eq_self_iff.mpr hu]
    calc
      inner ℂ u w = inner ℂ u ((fixedFields ρ).starProjection w) := by
        rw [(fixedFields ρ).starProjection_eq_self_iff.mpr hw]
      _ = inner ℂ ((fixedFields ρ).starProjection u) w :=
        ((fixedFields ρ).inner_starProjection_left_eq_right _ _).symm
      _ = inner ℂ w w := rfl
  have hcs := re_inner_le_norm (𝕜 := ℂ) u (mean w)
  rw [hinner, inner_self_eq_norm_sq] at hcs
  have hp := (fixedFields ρ).norm_sq_eq_add_norm_sq_starProjection u
  rw [Submodule.starProjection_orthogonal_val] at hp
  change ‖u‖ ^ 2 = ‖w‖ ^ 2 + ‖u - w‖ ^ 2 at hp
  change (1 / 16 : ℝ) * ‖u‖ ^ 2 ≤ ‖u - w‖ ^ 2
  by_cases hz : w = 0
  · rw [hz, sub_zero]
    nlinarith [sq_nonneg ‖u‖]
  have hn := norm_pos_iff.mpr hz
  have hcs₂ := pow_le_pow_left₀ (sq_nonneg ‖w‖) hcs 2
  have hm₂ := mul_le_mul_of_nonneg_left hm (sq_nonneg ‖u‖)
  have hupper : ‖w‖ ^ 2 ≤ (15 / 16 : ℝ) * ‖u‖ ^ 2 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hn)).mp
    nlinarith
  linarith

omit [CompleteSpace H] in
theorem constant_norm_sq (ξ : H) : ‖constant ξ‖ ^ 2 = 6 * ‖ξ‖ ^ 2 := by
  rw [vertex_norm_sq]
  simp only [constant_apply, Finset.sum_const, Finset.card_univ, vertex_card, nsmul_eq_mul, Nat.cast_ofNat]

theorem vertex_invariant_distances_gap (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H))
    (hρ : hilbertUnitaryInvariants ρ = ⊥) (ξ : H) :
    (3 / 8 : ℝ) * ‖ξ‖ ^ 2 ≤ ∑ r : Root, ‖ξ - (vertexInvariants ρ r).starProjection ξ‖ ^ 2 := by
  have h := constants_distance_to_fixedFields ρ hρ (constant ξ) (constant_mem ξ)
  rw [constant_norm_sq, fixedFields_residual_norm_sq] at h
  simpa only [constant_apply, Submodule.starProjection_orthogonal_val, show (1 / 16 : ℝ) * (6 * ‖ξ‖ ^ 2) =
    (3 / 8 : ℝ) * ‖ξ‖ ^ 2 by ring] using h

end ThomGame.Analysis.IntegerRootGraph

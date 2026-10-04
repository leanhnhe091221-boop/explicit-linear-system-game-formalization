module

public import ThomGame.Analysis.IntegerRootGraphGap
public import ThomGame.Analysis.IntegerRootGraphFixedFields
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! The actual compressed Laplacian and the energy estimates of Claim 5.7(b,c). -/

@[expose] public noncomputable section
namespace ThomGame.Analysis.IntegerRootGraph

open Compressor IntegralShear ThomGame.IntegerRootGraph
open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def compressedLaplacian (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) : VertexHilbert H →L[ℂ] VertexHilbert H :=
  (decompositionSpace ρ).starProjection.comp laplacian

theorem compressedLaplacian_mem (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H) :
    compressedLaplacian ρ f ∈ decompositionSpace ρ := (decompositionSpace ρ).starProjection_apply_mem _

theorem decomposition_projection_vertexSum (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H) :
    vertexSum ((decompositionSpace ρ).starProjection f) = vertexSum f := by
  have h := (decompositionSpace ρ).sub_starProjection_mem_orthogonal f
  have hU := Submodule.orthogonal_le (constants_le_decomposition ρ) h
  rw [constantSpace_orthogonal_iff, map_sub, sub_eq_zero] at hU
  exact hU.symm

theorem compressedLaplacian_zero_sum (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H) :
    vertexSum (compressedLaplacian ρ f) = 0 := by
  change vertexSum ((decompositionSpace ρ).starProjection (laplacian f)) = 0
  rw [decomposition_projection_vertexSum, vertexSum_laplacian]

theorem compressedLaplacian_inner (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H)
    (hf : f ∈ decompositionSpace ρ) : inner ℂ f (compressedLaplacian ρ f) = inner ℂ f (laplacian f) := by
  change inner ℂ f ((decompositionSpace ρ).starProjection (laplacian f)) = _
  rw [← (decompositionSpace ρ).inner_starProjection_left_eq_right,
    (decompositionSpace ρ).starProjection_eq_self_iff.mpr hf]

theorem compressedLaplacian_norm_lower (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H)
    (hf : f ∈ decompositionSpace ρ) (hsum : vertexSum f = 0) :
    4 * ‖f‖ ≤ ‖compressedLaplacian ρ f‖ := by
  by_cases hz : f = 0
  · simp [hz]
  have hn := norm_pos_iff.mpr hz
  have hg := laplacian_zero_sum_gap f hsum
  rw [← compressedLaplacian_inner ρ f hf] at hg
  have h := hg.trans (re_inner_le_norm (𝕜 := ℂ) f (compressedLaplacian ρ f))
  apply (mul_le_mul_iff_left₀ hn).mp
  nlinarith

theorem compressedLaplacian_energy_bound (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H)
    (hf : f ∈ decompositionSpace ρ) (hsum : vertexSum f = 0) :
    edgeEnergy f ≤ (1 / 4 : ℝ) * ‖compressedLaplacian ρ f‖ ^ 2 := by
  have hg := compressedLaplacian_norm_lower ρ f hf hsum
  have h := re_inner_le_norm (𝕜 := ℂ) f (compressedLaplacian ρ f)
  rw [compressedLaplacian_inner ρ f hf, RCLike.re_to_complex, laplacian_energy] at h
  have hm := mul_le_mul_of_nonneg_right hg (norm_nonneg (compressedLaplacian ρ f))
  nlinarith

theorem compressedLaplacian_unit_energy (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H)
    (hf : f ∈ decompositionSpace ρ) (hsum : vertexSum f = 0) (hunit : ‖compressedLaplacian ρ f‖ = 1) :
    edgeEnergy f ≤ 1 / 4 := by
  simpa only [hunit, one_pow, mul_one] using compressedLaplacian_energy_bound ρ f hf hsum

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem four_vector_sum_norm_sq_le (v : Fin 4 → H) : ‖∑ i, v i‖ ^ 2 ≤ 4 * ∑ i, ‖v i‖ ^ 2 := by
  have h₁ := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le Finset.univ v) 2
  have h₂ := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i : Fin 4 => ‖v i‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat, mul_one] at h₂
  exact h₁.trans (by simpa only [mul_comm] using h₂)

omit [CompleteSpace H] in
theorem laplacian_sum_edgeDifference (f : VertexHilbert H) (r : Root) :
    laplacian f r = ∑ i : Fin 4, edgeDifference r i f := by
  rw [laplacian_apply]
  simp only [edgeDifference_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  module

def vertexEdgeEnergy (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H) : ℝ :=
  (1 / 2 : ℝ) * ∑ r : Root, ∑ i : Fin 4, ‖(vertexInvariants ρ r).starProjection (edgeDifference r i f)‖ ^ 2

theorem fixedFields_laplacian_norm_sq_le (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H) :
    ‖(fixedFields ρ).starProjection (laplacian f)‖ ^ 2 ≤ 8 * vertexEdgeEnergy ρ f := by
  rw [fixedFields_starProjection, vertex_norm_sq]
  simp only [fixedFieldProjection_apply]
  calc
    (∑ r : Root, ‖(vertexInvariants ρ r).starProjection (laplacian f r)‖ ^ 2) ≤
        ∑ r : Root, 4 * ∑ i : Fin 4, ‖(vertexInvariants ρ r).starProjection (edgeDifference r i f)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro r _
      rw [laplacian_sum_edgeDifference, map_sum]
      exact four_vector_sum_norm_sq_le _
    _ = 8 * vertexEdgeEnergy ρ f := by rw [← Finset.mul_sum]; unfold vertexEdgeEnergy; ring

theorem fixedFields_project_compressed (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H) :
    (fixedFields ρ).starProjection (compressedLaplacian ρ f) = (fixedFields ρ).starProjection (laplacian f) :=
  congrArg (fun T : VertexHilbert H →L[ℂ] VertexHilbert H => T (laplacian f))
    (Submodule.starProjection_comp_starProjection_of_le (fixedFields_le_decomposition ρ))

theorem compressedLaplacian_vertex_energy_lower (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H) :
    (‖compressedLaplacian ρ f‖ ^ 2 -
      ‖compressedLaplacian ρ f - (fixedFields ρ).starProjection (compressedLaplacian ρ f)‖ ^ 2) / 8 ≤
      vertexEdgeEnergy ρ f := by
  have h := fixedFields_laplacian_norm_sq_le ρ f
  rw [← fixedFields_project_compressed] at h
  have hp := (fixedFields ρ).norm_sq_eq_add_norm_sq_starProjection (compressedLaplacian ρ f)
  rw [Submodule.starProjection_orthogonal_val] at hp
  linarith

theorem compressedLaplacian_unit_vertex_energy_lower (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H)
    (hunit : ‖compressedLaplacian ρ f‖ = 1) :
    (1 - ‖compressedLaplacian ρ f - (fixedFields ρ).starProjection (compressedLaplacian ρ f)‖ ^ 2) / 8 ≤
      vertexEdgeEnergy ρ f := by
  simpa only [hunit, one_pow] using compressedLaplacian_vertex_energy_lower ρ f

end ThomGame.Analysis.IntegerRootGraph

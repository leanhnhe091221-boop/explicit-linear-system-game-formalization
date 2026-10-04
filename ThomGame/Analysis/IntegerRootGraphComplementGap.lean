module

public import ThomGame.Analysis.IntegerRootGraphLocalGap
public import ThomGame.Analysis.IntegerRootGraphSolvability

/-! The strict global bound in the direction orthogonal to the vertex fixed fields. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis.IntegerRootGraph

open Compressor IntegralShear ThomGame.IntegerRootGraph
open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem fixedFields_residual_norm_sq (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H) :
    ‖f - (fixedFields ρ).starProjection f‖ ^ 2 =
      ∑ r : Root, ‖(vertexInvariants ρ r)ᗮ.starProjection (f r)‖ ^ 2 := by
  rw [fixedFields_starProjection, vertex_norm_sq]
  apply Finset.sum_congr rfl
  intro r _
  rw [Submodule.starProjection_orthogonal_val]
  rfl

theorem compressedLaplacian_residual_projection (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H) :
    compressedLaplacian ρ f - (fixedFields ρ).starProjection (compressedLaplacian ρ f) =
      (decompositionSpace ρ).starProjection (laplacian f - (fixedFields ρ).starProjection (laplacian f)) := by
  rw [map_sub, fixedFields_project_compressed,
    (decompositionSpace ρ).starProjection_eq_self_iff.mpr
      (fixedFields_le_decomposition ρ ((fixedFields ρ).starProjection_apply_mem _))]
  rfl

theorem compressedLaplacian_refined_bound (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H)
    (hf : f ∈ decompositionSpace ρ) :
    ‖compressedLaplacian ρ f - (fixedFields ρ).starProjection (compressedLaplacian ρ f)‖ ^ 2 ≤
      4 * edgeEnergy f - (1 / 2 : ℝ) * rootEdgeEnergy ρ f - 4 * vertexEdgeEnergy ρ f := by
  have hn := pow_le_pow_left₀ (norm_nonneg _)
    ((decompositionSpace ρ).norm_starProjection_apply_le
      (laplacian f - (fixedFields ρ).starProjection (laplacian f))) 2
  rw [← compressedLaplacian_residual_projection, fixedFields_residual_norm_sq ρ (laplacian f)] at hn
  have h := Finset.sum_le_sum (fun (r : Root) (_ : r ∈ Finset.univ) => vertex_laplacian_refined_bound ρ f hf r)
  have ht := hn.trans h
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at ht
  change _ ≤ 4 * ((1 / 2 : ℝ) * ∑ r : Root, ∑ i : Fin 4, ‖edgeDifference r i f‖ ^ 2) -
    (1 / 2 : ℝ) * rootEdgeEnergy ρ f - 4 * vertexEdgeEnergy ρ f
  unfold rootEdgeEnergy vertexEdgeEnergy
  linarith

theorem zeroSumDecomposition_complement_gap (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (x : VertexHilbert H)
    (hx : x ∈ decompositionSpace ρ) (hsum : vertexSum x = 0) :
    ‖x - (fixedFields ρ).starProjection x‖ ^ 2 ≤ (27 / 29 : ℝ) * ‖x‖ ^ 2 := by
  obtain ⟨g, ⟨hg, heq⟩, _⟩ := compressedLaplacian_exists_unique ρ x hx hsum
  have hlocal := compressedLaplacian_refined_bound ρ g hg.1
  have htech := technical_energy_bound ρ g hg.1
  have henergy := compressedLaplacian_energy_bound ρ g hg.1 hg.2
  have hvertex := compressedLaplacian_vertex_energy_lower ρ g
  rw [heq] at hlocal henergy hvertex
  linarith

theorem zeroSumDecomposition_fixed_projection_lower_sq (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (x : VertexHilbert H)
    (hx : x ∈ decompositionSpace ρ) (hsum : vertexSum x = 0) :
    (2 / 29 : ℝ) * ‖x‖ ^ 2 ≤ ‖(fixedFields ρ).starProjection x‖ ^ 2 := by
  have h := zeroSumDecomposition_complement_gap ρ x hx hsum
  have hp := (fixedFields ρ).norm_sq_eq_add_norm_sq_starProjection x
  rw [Submodule.starProjection_orthogonal_val] at hp
  linarith

theorem zeroSumDecomposition_fixed_projection_lower (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (x : VertexHilbert H)
    (hx : x ∈ decompositionSpace ρ) (hsum : vertexSum x = 0) :
    (1 / 4 : ℝ) * ‖x‖ ≤ ‖(fixedFields ρ).starProjection x‖ := by
  have h := zeroSumDecomposition_fixed_projection_lower_sq ρ x hx hsum
  nlinarith [norm_nonneg x, norm_nonneg ((fixedFields ρ).starProjection x), sq_nonneg ‖x‖]

end ThomGame.Analysis.IntegerRootGraph

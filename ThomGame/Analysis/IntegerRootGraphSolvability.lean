module

public import ThomGame.Analysis.IntegerRootGraphCompression
public import ThomGame.Analysis.HilbertCoerciveSurjectivity
public import ThomGame.Analysis.IntegerRootGraphTechnicalEnergy

/-! Solving the actual compressed Laplacian on the closed zero-sum decomposition space. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis.IntegerRootGraph

open Compressor IntegralShear ThomGame.IntegerRootGraph

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def zeroSumDecomposition (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) : Submodule ℂ (VertexHilbert H) :=
  decompositionSpace ρ ⊓ (vertexSum : VertexHilbert H →L[ℂ] H).ker

theorem mem_zeroSumDecomposition (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H) :
    f ∈ zeroSumDecomposition ρ ↔ f ∈ decompositionSpace ρ ∧ vertexSum f = 0 := Iff.rfl

theorem zeroSumDecomposition_closed (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) :
    IsClosed (zeroSumDecomposition ρ : Set (VertexHilbert H)) :=
  (decompositionSpace_closed ρ).inter (vertexSum : VertexHilbert H →L[ℂ] H).isClosed_ker

variable [CompleteSpace H]

instance zeroSumDecomposition_complete (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) :
    CompleteSpace (zeroSumDecomposition ρ) := (zeroSumDecomposition_closed ρ).completeSpace_coe

def reducedLaplacian (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) :
    zeroSumDecomposition ρ →L[ℂ] zeroSumDecomposition ρ :=
  ((compressedLaplacian ρ).comp (zeroSumDecomposition ρ).subtypeL).codRestrict
    (zeroSumDecomposition ρ)
    (fun f => ⟨compressedLaplacian_mem ρ f, compressedLaplacian_zero_sum ρ f⟩)

theorem reducedLaplacian_apply (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : zeroSumDecomposition ρ) :
    (reducedLaplacian ρ f : VertexHilbert H) = compressedLaplacian ρ f := rfl

theorem reducedLaplacian_coercive (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : zeroSumDecomposition ρ) :
    4 * ‖f‖ ^ 2 ≤ (inner ℂ f (reducedLaplacian ρ f)).re := by
  change 4 * ‖(f : VertexHilbert H)‖ ^ 2 ≤
    (inner ℂ (f : VertexHilbert H) (compressedLaplacian ρ f)).re
  rw [compressedLaplacian_inner ρ f f.property.1]
  exact laplacian_zero_sum_gap (H := H) (f : VertexHilbert H) f.property.2

theorem reducedLaplacian_bijective (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) :
    Function.Bijective (reducedLaplacian ρ) :=
  hilbert_coercive_bijective (reducedLaplacian ρ) 4 (by norm_num) (reducedLaplacian_coercive ρ)

theorem compressedLaplacian_exists_unique (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (x : VertexHilbert H)
    (hx : x ∈ decompositionSpace ρ) (hsum : vertexSum x = 0) :
    ∃! g : VertexHilbert H, g ∈ zeroSumDecomposition ρ ∧ compressedLaplacian ρ g = x := by
  obtain ⟨g, hg⟩ := (reducedLaplacian_bijective ρ).surjective ⟨x, hx, hsum⟩
  have hval : compressedLaplacian ρ g = x := congrArg Subtype.val hg
  refine ⟨g, ⟨g.property, hval⟩, ?_⟩
  intro y hy
  have heq : reducedLaplacian ρ ⟨y, hy.1⟩ = reducedLaplacian ρ g := by
    apply Subtype.ext
    exact hy.2.trans hval.symm
  exact congrArg Subtype.val ((reducedLaplacian_bijective ρ).injective heq)

theorem compressedLaplacian_solution_bounds (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (x : VertexHilbert H)
    (hx : x ∈ decompositionSpace ρ) (hsum : vertexSum x = 0) :
    ∃ g : VertexHilbert H, g ∈ decompositionSpace ρ ∧ vertexSum g = 0 ∧
      compressedLaplacian ρ g = x ∧ ‖g‖ ≤ (1 / 4 : ℝ) * ‖x‖ ∧
      edgeEnergy g ≤ (1 / 4 : ℝ) * ‖x‖ ^ 2 := by
  obtain ⟨g, ⟨hg, heq⟩, _⟩ := compressedLaplacian_exists_unique ρ x hx hsum
  have hn := compressedLaplacian_norm_lower ρ g hg.1 hg.2
  have he := compressedLaplacian_energy_bound ρ g hg.1 hg.2
  rw [heq] at hn he
  exact ⟨g, hg.1, hg.2, heq, by linarith, he⟩

theorem compressedLaplacian_unit_solution (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (x : VertexHilbert H)
    (hx : x ∈ decompositionSpace ρ) (hsum : vertexSum x = 0) (hunit : ‖x‖ = 1) :
    ∃ g : VertexHilbert H, g ∈ decompositionSpace ρ ∧ vertexSum g = 0 ∧
      compressedLaplacian ρ g = x ∧ ‖g‖ ≤ 1 / 4 ∧ edgeEnergy g ≤ 1 / 4 ∧
      (1 - ‖x - (fixedFields ρ).starProjection x‖ ^ 2) / 8 ≤ vertexEdgeEnergy ρ g := by
  obtain ⟨g, hg, hs, heq, hn, he⟩ := compressedLaplacian_solution_bounds ρ x hx hsum
  have hvertex := compressedLaplacian_unit_vertex_energy_lower ρ g ((congrArg norm heq).trans hunit)
  rw [heq] at hvertex
  simp only [hunit, one_pow, mul_one] at hn he
  exact ⟨g, hg, hs, heq, hn, he, hvertex⟩

theorem compressedLaplacian_three_energy_bounds (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (x : VertexHilbert H)
    (hx : x ∈ decompositionSpace ρ) (hsum : vertexSum x = 0) (hunit : ‖x‖ = 1) :
    ∃ g : VertexHilbert H, g ∈ decompositionSpace ρ ∧ vertexSum g = 0 ∧
      compressedLaplacian ρ g = x ∧ ‖g‖ ≤ 1 / 4 ∧
      edgeEnergy g ≤ 3 * rootEdgeEnergy ρ g + 5 * vertexEdgeEnergy ρ g ∧
      edgeEnergy g ≤ 1 / 4 ∧
      (1 - ‖x - (fixedFields ρ).starProjection x‖ ^ 2) / 8 ≤ vertexEdgeEnergy ρ g := by
  obtain ⟨g, hg, hs, heq, hn, he, hv⟩ := compressedLaplacian_unit_solution ρ x hx hsum hunit
  exact ⟨g, hg, hs, heq, hn, technical_energy_bound ρ g hg, he, hv⟩

end ThomGame.Analysis.IntegerRootGraph

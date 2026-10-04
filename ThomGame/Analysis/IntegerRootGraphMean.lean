module

public import ThomGame.Analysis.IntegerRootGraphOperators
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! The actual constant subspace, arithmetic mean, and zero-sum orthogonal complement. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis.IntegerRootGraph

open Compressor ThomGame.IntegerRootGraph
open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def constantSpace : Submodule ℂ (VertexHilbert H) where
  carrier := {f | ∀ r, f r = f root12}
  zero_mem' := by intro r; rfl
  add_mem' := by intro f g hf hg r; change f r + g r = f root12 + g root12; rw [hf r, hg r]
  smul_mem' := by intro c f hf r; change c • f r = c • f root12; rw [hf r]

theorem constant_mem (ξ : H) : constant ξ ∈ (constantSpace : Submodule ℂ (VertexHilbert H)) := by
  intro r
  rfl

theorem mem_constantSpace (f : VertexHilbert H) :
    f ∈ constantSpace ↔ ∃ ξ : H, f = constant ξ := by
  constructor
  · intro hf
    refine ⟨f root12, ?_⟩
    ext r
    exact hf r
  · rintro ⟨ξ, rfl⟩
    exact constant_mem ξ

theorem constantSpace_closed :
    IsClosed ((constantSpace : Submodule ℂ (VertexHilbert H)) : Set (VertexHilbert H)) := by
  change IsClosed {f : VertexHilbert H | ∀ r, f r = f root12}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro r
  exact isClosed_eq (PiLp.proj (p := 2) (𝕜 := ℂ) (β := fun _ : Root => H) r).continuous
    (PiLp.proj (p := 2) (𝕜 := ℂ) (β := fun _ : Root => H) root12).continuous

def mean : VertexHilbert H →L[ℂ] VertexHilbert H := (1 / 6 : ℂ) • total

theorem mean_eq_constant (f : VertexHilbert H) : mean f = constant ((1 / 6 : ℂ) • vertexSum f) := by
  change (1 / 6 : ℂ) • constant (vertexSum f) = constant ((1 / 6 : ℂ) • vertexSum f)
  rw [map_smul]

theorem mean_mem (f : VertexHilbert H) : mean f ∈ (constantSpace : Submodule ℂ (VertexHilbert H)) := by
  rw [mean_eq_constant]
  exact constant_mem _

theorem vertexSum_mean (f : VertexHilbert H) : vertexSum (mean f) = vertexSum f := by
  rw [mean_eq_constant, vertexSum_constant]
  module

theorem mean_constant (ξ : H) : mean (constant ξ) = constant ξ := by
  rw [mean_eq_constant, vertexSum_constant]
  congr 1
  module

theorem vertexSum_residual (f : VertexHilbert H) : vertexSum (f - mean f) = 0 := by
  rw [map_sub, vertexSum_mean, sub_self]

theorem constant_inner (ξ : H) (f : VertexHilbert H) :
    inner ℂ (constant ξ) f = inner ℂ ξ (vertexSum f) := by
  simp only [PiLp.inner_apply, constant_apply, vertexSum_apply, inner_sum]

theorem constantSpace_orthogonal_iff (f : VertexHilbert H) :
    f ∈ (constantSpace : Submodule ℂ (VertexHilbert H))ᗮ ↔ vertexSum f = 0 := by
  constructor
  · intro hf
    have h := (Submodule.mem_orthogonal _ _).mp hf (constant (vertexSum f)) (constant_mem _)
    rw [constant_inner, inner_self_eq_zero] at h
    exact h
  · intro hf
    apply (Submodule.mem_orthogonal _ _).mpr
    intro g hg
    obtain ⟨ξ, rfl⟩ := (mem_constantSpace g).mp hg
    rw [constant_inner, hf, inner_zero_right]

variable [CompleteSpace H]

instance constantSpace_complete : CompleteSpace (constantSpace : Submodule ℂ (VertexHilbert H)) :=
  constantSpace_closed.completeSpace_coe

theorem constantSpace_starProjection (f : VertexHilbert H) :
    (constantSpace : Submodule ℂ (VertexHilbert H)).starProjection f = mean f := by
  apply Submodule.eq_starProjection_of_mem_orthogonal (mean_mem f)
  exact (constantSpace_orthogonal_iff _).mpr (vertexSum_residual f)

omit [CompleteSpace H] in
theorem laplacian_mean (f : VertexHilbert H) : laplacian (mean f) = 0 := by
  rw [mean_eq_constant, laplacian_constant]

omit [CompleteSpace H] in
theorem laplacian_residual (f : VertexHilbert H) : laplacian (f - mean f) = laplacian f := by
  rw [map_sub, laplacian_mean, sub_zero]

end ThomGame.Analysis.IntegerRootGraph

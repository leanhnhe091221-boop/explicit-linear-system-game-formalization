module

public import ThomGame.Groups.IntegerRootGraph
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Tactic.Module

/-! Actual bounded operators on the six-vertex Hilbert direct sum. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis.IntegerRootGraph

open Compressor ThomGame.IntegerRootGraph
open scoped BigOperators

abbrev VertexHilbert (H : Type*) := PiLp 2 (fun _ : Root => H)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def pullback (σ : Root → Root) : VertexHilbert H →L[ℂ] VertexHilbert H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Root => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun r => PiLp.proj (p := 2) (𝕜 := ℂ) (β := fun _ : Root => H) (σ r))

theorem pullback_apply (σ : Root → Root) (f : VertexHilbert H) (r : Root) :
    pullback σ f r = f (σ r) := rfl

def vertexSum : VertexHilbert H →L[ℂ] H :=
  ∑ r : Root, PiLp.proj (p := 2) (𝕜 := ℂ) (β := fun _ : Root => H) r

theorem vertexSum_apply (f : VertexHilbert H) : vertexSum f = ∑ r : Root, f r := by
  simp only [vertexSum, sum_apply, PiLp.proj_apply]

theorem vertex_sum_apply {ι : Type*} [Fintype ι] (f : ι → VertexHilbert H) (r : Root) :
    (∑ i, f i) r = ∑ i, f i r :=
  map_sum (PiLp.proj (p := 2) (𝕜 := ℂ) (β := fun _ : Root => H) r) f Finset.univ

def constant : H →L[ℂ] VertexHilbert H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Root => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℂ H)

theorem constant_apply (ξ : H) (r : Root) : constant ξ r = ξ := rfl

def opposite : VertexHilbert H →L[ℂ] VertexHilbert H := pullback reverse

def total : VertexHilbert H →L[ℂ] VertexHilbert H := constant.comp vertexSum

def laplacian : VertexHilbert H →L[ℂ] VertexHilbert H :=
  (4 : ℂ) • 1 - ∑ i : Fin 4, pullback (fun r => neighbor r i)

theorem opposite_apply (f : VertexHilbert H) (r : Root) : opposite f r = f (reverse r) := rfl

theorem total_apply (f : VertexHilbert H) (r : Root) : total f r = ∑ s : Root, f s := by
  exact vertexSum_apply f

theorem laplacian_apply (f : VertexHilbert H) (r : Root) :
    laplacian f r = (4 : ℂ) • f r - ∑ i : Fin 4, f (neighbor r i) := by
  change ((4 : ℂ) • f - (∑ i : Fin 4, pullback (fun r => neighbor r i)) f) r = _
  simp only [sum_apply, PiLp.sub_apply, PiLp.smul_apply, vertex_sum_apply, pullback_apply]

theorem laplacian_closed_form (f : VertexHilbert H) (r : Root) :
    laplacian f r = (5 : ℂ) • f r + f (reverse r) - ∑ s : Root, f s := by
  rw [laplacian_apply, ← sum_neighbors_complement (fun s => f s) r]
  module

theorem laplacian_operator_formula : (laplacian : VertexHilbert H →L[ℂ] VertexHilbert H) =
    (5 : ℂ) • 1 + opposite - total := by
  ext f r
  exact laplacian_closed_form f r

theorem vertexSum_opposite (f : VertexHilbert H) : vertexSum (opposite f) = vertexSum f := by
  simp only [vertexSum_apply, opposite_apply, sum_opposites_reindex]

theorem opposite_opposite (f : VertexHilbert H) : opposite (opposite f) = f := by
  ext r
  simp only [opposite_apply, reverse_reverse]

theorem vertexSum_constant (ξ : H) : vertexSum (constant ξ) = (6 : ℂ) • ξ := by
  simp only [vertexSum_apply, constant_apply, Finset.sum_const, Finset.card_univ, vertex_card]
  module

theorem vertexSum_laplacian (f : VertexHilbert H) : vertexSum (laplacian f) = 0 := by
  rw [laplacian_operator_formula]
  change vertexSum ((5 : ℂ) • f + opposite f - constant (vertexSum f)) = 0
  simp only [map_sub, map_add, map_smul, vertexSum_opposite, vertexSum_constant]
  module

theorem laplacian_constant (ξ : H) : laplacian (constant ξ) = 0 := by
  ext r
  rw [laplacian_closed_form]
  simp only [constant_apply, Finset.sum_const, Finset.card_univ, vertex_card]
  change (5 : ℂ) • ξ + ξ - 6 • ξ = 0
  module

omit [InnerProductSpace ℂ H] in
theorem vertex_norm_sq (f : VertexHilbert H) : ‖f‖ ^ 2 = ∑ r : Root, ‖f r‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ f

theorem opposite_norm (f : VertexHilbert H) : ‖opposite f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [vertex_norm_sq, opposite_apply]
  exact sum_opposites_reindex (fun r => ‖f r‖ ^ 2)

theorem opposite_inner (f g : VertexHilbert H) :
    inner ℂ (opposite f) g = inner ℂ f (opposite g) := by
  simp only [PiLp.inner_apply, opposite_apply]
  have h := sum_opposites_reindex (fun r => inner ℂ (f r) (g (reverse r)))
  simpa only [reverse_reverse] using h

theorem total_inner (f g : VertexHilbert H) : inner ℂ (total f) g = inner ℂ f (total g) := by
  simp only [PiLp.inner_apply, total_apply, ← inner_sum, ← sum_inner]

end ThomGame.Analysis.IntegerRootGraph

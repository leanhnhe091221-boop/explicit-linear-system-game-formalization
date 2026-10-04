module

public import ThomGame.Analysis.IntegerRootGraphMean
public import ThomGame.Analysis.HilbertUnitaryInvariants
public import ThomGame.Groups.IntegerRootGraphGroups

/-! Actual vertex fixed fields and the closed space of constants plus fixed fields. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis.IntegerRootGraph

open Compressor IntegralShear ThomGame.IntegerRootGraph
open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def vertexInvariants (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (r : Root) : Submodule ℂ H :=
  hilbertUnitaryInvariants (ρ.comp (graphVertexGroup r).subtype)

def edgeInvariants (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (r : Root) (i : Fin 4) : Submodule ℂ H :=
  hilbertUnitaryInvariants (ρ.comp (graphEdgeGroup r i).subtype)

theorem vertexInvariants_le_edge (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (r : Root) (i : Fin 4) :
    vertexInvariants ρ r ≤ edgeInvariants ρ r i := by
  intro ξ hξ g
  exact hξ ⟨g.val, graphEdgeGroup_le_vertex r i g.property⟩

theorem neighborInvariants_le_edge (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (r : Root) (i : Fin 4) :
    vertexInvariants ρ (neighbor r i) ≤ edgeInvariants ρ r i := by
  intro ξ hξ g
  exact hξ ⟨g.val, graphEdgeGroup_le_neighbor r i g.property⟩

def fixedFields (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) : Submodule ℂ (VertexHilbert H) where
  carrier := {f | ∀ r, f r ∈ vertexInvariants ρ r}
  zero_mem' := by intro r; exact (vertexInvariants ρ r).zero_mem
  add_mem' := by intro f g hf hg r; exact (vertexInvariants ρ r).add_mem (hf r) (hg r)
  smul_mem' := by intro c f hf r; exact (vertexInvariants ρ r).smul_mem c (hf r)

theorem fixedFields_closed (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) : IsClosed (fixedFields ρ : Set (VertexHilbert H)) := by
  change IsClosed {f : VertexHilbert H | ∀ r, f r ∈ vertexInvariants ρ r}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro r
  exact (hilbertUnitaryInvariants_isClosed (ρ.comp (graphVertexGroup r).subtype)).preimage
    (PiLp.proj (p := 2) (𝕜 := ℂ) (β := fun _ : Root => H) r).continuous

def decompositionSpace (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) : Submodule ℂ (VertexHilbert H) :=
  (constantSpace ⊔ fixedFields ρ).topologicalClosure

theorem decompositionSpace_closed (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) :
    IsClosed (decompositionSpace ρ : Set (VertexHilbert H)) := Submodule.isClosed_topologicalClosure _

theorem constants_le_decomposition (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) : constantSpace ≤ decompositionSpace ρ :=
  (show constantSpace ≤ constantSpace ⊔ fixedFields ρ from le_sup_left).trans (Submodule.le_topologicalClosure _)

theorem fixedFields_le_decomposition (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) : fixedFields ρ ≤ decompositionSpace ρ :=
  (show fixedFields ρ ≤ constantSpace ⊔ fixedFields ρ from le_sup_right).trans (Submodule.le_topologicalClosure _)

def edgeDifference (r : Root) (i : Fin 4) : VertexHilbert H →L[ℂ] H :=
  PiLp.proj (p := 2) (𝕜 := ℂ) (β := fun _ : Root => H) r -
    PiLp.proj (p := 2) (𝕜 := ℂ) (β := fun _ : Root => H) (neighbor r i)

theorem edgeDifference_apply (r : Root) (i : Fin 4) (f : VertexHilbert H) :
    edgeDifference r i f = f r - f (neighbor r i) := rfl

theorem fixedFields_edge_mem (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H)
    (hf : f ∈ fixedFields ρ) (r : Root) (i : Fin 4) : edgeDifference r i f ∈ edgeInvariants ρ r i :=
  (edgeInvariants ρ r i).sub_mem (vertexInvariants_le_edge ρ r i (hf r))
    (neighborInvariants_le_edge ρ r i (hf (neighbor r i)))

theorem decompositionSpace_edge_mem (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H)
    (hf : f ∈ decompositionSpace ρ) (r : Root) (i : Fin 4) : edgeDifference r i f ∈ edgeInvariants ρ r i := by
  let T := (edgeInvariants ρ r i).comap (edgeDifference r i : VertexHilbert H →L[ℂ] H).toLinearMap
  have hclosed : IsClosed (T : Set (VertexHilbert H)) :=
    (hilbertUnitaryInvariants_isClosed (ρ.comp (graphEdgeGroup r i).subtype)).preimage (edgeDifference r i).continuous
  have hc : constantSpace ≤ T := by
    intro g hg
    obtain ⟨ξ, rfl⟩ := (mem_constantSpace g).mp hg
    change edgeDifference r i (constant ξ) ∈ edgeInvariants ρ r i
    rw [edgeDifference_apply, constant_apply, constant_apply, sub_self]
    exact (edgeInvariants ρ r i).zero_mem
  have hw : fixedFields ρ ≤ T := by
    intro g hg
    exact fixedFields_edge_mem ρ g hg r i
  exact ((constantSpace ⊔ fixedFields ρ).topologicalClosure_minimal (sup_le hc hw) hclosed) hf

theorem vertexInvariants_iInf (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) :
    hilbertUnitaryInvariants ρ = ⨅ r : Root, vertexInvariants ρ r :=
  hilbertUnitaryInvariants_of_iSup ρ graphVertexGroup graphVertexGroups_generate

theorem constant_mem_fixedFields_iff (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (ξ : H) :
    constant ξ ∈ fixedFields ρ ↔ ξ ∈ hilbertUnitaryInvariants ρ := by
  rw [vertexInvariants_iInf, Submodule.mem_iInf]
  rfl

theorem constants_inf_fixedFields (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H))
    (hρ : hilbertUnitaryInvariants ρ = ⊥) : constantSpace ⊓ fixedFields ρ = ⊥ := by
  apply eq_bot_iff.mpr
  intro f hf
  obtain ⟨ξ, rfl⟩ := (mem_constantSpace f).mp hf.1
  have hξ := (constant_mem_fixedFields_iff ρ ξ).mp hf.2
  rw [hρ, Submodule.mem_bot] at hξ
  simp [hξ]

variable [CompleteSpace H]

instance vertexInvariants_complete (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (r : Root) : CompleteSpace (vertexInvariants ρ r) :=
  inferInstanceAs (CompleteSpace (hilbertUnitaryInvariants (ρ.comp (graphVertexGroup r).subtype)))

instance fixedFields_complete (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) : CompleteSpace (fixedFields ρ) :=
  (fixedFields_closed ρ).completeSpace_coe

instance decompositionSpace_complete (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) : CompleteSpace (decompositionSpace ρ) :=
  (decompositionSpace_closed ρ).completeSpace_coe

theorem projected_edgeDifference_mem (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H)
    (hf : f ∈ decompositionSpace ρ) (r : Root) (i : Fin 4) :
    edgeDifference r i f - (vertexInvariants ρ r).starProjection (edgeDifference r i f) ∈ edgeInvariants ρ r i :=
  (edgeInvariants ρ r i).sub_mem (decompositionSpace_edge_mem ρ f hf r i)
    (vertexInvariants_le_edge ρ r i ((vertexInvariants ρ r).starProjection_apply_mem _))

def fixedFieldProjection (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) : VertexHilbert H →L[ℂ] VertexHilbert H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Root => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun r => (vertexInvariants ρ r).starProjection.comp
      (PiLp.proj (p := 2) (𝕜 := ℂ) (β := fun _ : Root => H) r))

theorem fixedFieldProjection_apply (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H) (r : Root) :
    fixedFieldProjection ρ f r = (vertexInvariants ρ r).starProjection (f r) := rfl

theorem fixedFields_starProjection (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H) :
    (fixedFields ρ).starProjection f = fixedFieldProjection ρ f := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · intro r
    exact (vertexInvariants ρ r).starProjection_apply_mem (f r)
  · apply (Submodule.mem_orthogonal _ _).mpr
    intro g hg
    rw [PiLp.inner_apply]
    apply Finset.sum_eq_zero
    intro r _
    change inner ℂ (g r) (f r - (vertexInvariants ρ r).starProjection (f r)) = 0
    exact (Submodule.mem_orthogonal _ _).mp ((vertexInvariants ρ r).sub_starProjection_mem_orthogonal (f r)) (g r) (hg r)

end ThomGame.Analysis.IntegerRootGraph

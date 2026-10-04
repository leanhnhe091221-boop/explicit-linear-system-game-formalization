module

public import ThomGame.Finite.Hypergraph

/-! # The partial endomorphism associated to a hypergraph retraction -/

@[expose] public section
namespace ThomGame.Hypergraph

variable {V E W F X Y : Type*} {H : Hypergraph V E} {K : Hypergraph W F} {L : Hypergraph X Y}

def GeneralizedHom.postcomposeEmbedding (φ : H.GeneralizedHom K) (ι : K.OpenEmbedding L) :
    H.GeneralizedHom L where
  vertex v := (φ.vertex v).map ι.vertex
  edge e := (φ.edge e).map ι.edge
  retained v x hv := by
    cases hw : φ.vertex v with
    | none => simp [hw] at hv
    | some w =>
      have hx : ι.vertex w = x := by simpa [hw] using hv
      subst x
      rw [← Multiset.map_filterMap, φ.retained v w hw]
      exact ι.incidence w
  deleted v hv := by
    have hv' : φ.vertex v = none := by
      cases hw : φ.vertex v <;> simp_all
    obtain ⟨he, hm⟩ := φ.deleted v hv'
    rw [← Multiset.map_filterMap, Multiset.card_map]
    refine ⟨he, ?_⟩
    intro e he f hf
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp he
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp hf
    exact congrArg ι.edge (hm a ha b hb)

def Retraction.endomorphism (ρ : H.Retraction K) : H.GeneralizedHom H :=
  ρ.retract.postcomposeEmbedding ρ.inclusion

theorem Retraction.endomorphism_vertex (ρ : H.Retraction K) (w : W) :
    ρ.endomorphism.vertex (ρ.inclusion.vertex w) = some (ρ.inclusion.vertex w) := by
  change (ρ.retract.vertex (ρ.inclusion.vertex w)).map ρ.inclusion.vertex = _
  rw [ρ.vertex_leftInverse]
  rfl

theorem Retraction.endomorphism_edge (ρ : H.Retraction K) (f : F) :
    ρ.endomorphism.edge (ρ.inclusion.edge f) = some (ρ.inclusion.edge f) := by
  change (ρ.retract.edge (ρ.inclusion.edge f)).map ρ.inclusion.edge = _
  rw [ρ.edge_leftInverse]
  rfl

theorem Retraction.endomorphism_vertex_range (ρ : H.Retraction K) {v w : V}
    (hv : ρ.endomorphism.vertex v = some w) : w ∈ Set.range ρ.inclusion.vertex := by
  change (ρ.retract.vertex v).map ρ.inclusion.vertex = some w at hv
  cases he : ρ.retract.vertex v with
  | none => simp [he] at hv
  | some x => exact ⟨x, by simpa [he] using hv⟩

end ThomGame.Hypergraph

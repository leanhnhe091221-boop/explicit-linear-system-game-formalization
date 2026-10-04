module

public import ThomGame.Finite.Hypergraph

/-! # Open embeddings as generalized hypergraph maps -/

@[expose] public section
namespace ThomGame.Hypergraph

variable {V E W F : Type*} {H : Hypergraph V E} {K : Hypergraph W F}

def OpenEmbedding.toGeneralizedHom (ι : H.OpenEmbedding K) : H.GeneralizedHom K where
  vertex v := some (ι.vertex v)
  edge e := some (ι.edge e)
  retained v w hw := by
    have h : ι.vertex v = w := Option.some.inj hw
    subst w
    change (H.incidence v).filterMap (some ∘ ι.edge) = _
    rw [Multiset.filterMap_eq_map]
    exact ι.incidence v
  deleted v hv := by cases hv

end ThomGame.Hypergraph

module

public import ThomGame.Finite.Hypergraph
public import ThomGame.Finite.Reindex

/-! # Reindexing the source of a generalized hypergraph retraction -/

@[expose] public section
namespace ThomGame

namespace Hypergraph

variable {V E W F V' E' : Type*}

/-- Transport incidence proofs while keeping both maps definitionally
unchanged. Casting the whole record would hide them behind equality recursors. -/
def Retraction.congrSource {H H' : Hypergraph V E} {K : Hypergraph W F}
    (ρ : Retraction H K) (h : H = H') : Retraction H' K where
  inclusion := {
    vertex := ρ.inclusion.vertex
    edge := ρ.inclusion.edge
    incidence v := by rw [← h]; exact ρ.inclusion.incidence v }
  retract := {
    vertex := ρ.retract.vertex
    edge := ρ.retract.edge
    retained v w hv := by rw [← h]; exact ρ.retract.retained v w hv
    deleted v hv := by rw [← h]; exact ρ.retract.deleted v hv }
  vertex_leftInverse := ρ.vertex_leftInverse
  edge_leftInverse := ρ.edge_leftInverse

def reindex (H : Hypergraph V E) (vertices : V ≃ V') (edges : E ≃ E') : Hypergraph V' E' where
  incidence v := (H.incidence (vertices.symm v)).map edges

theorem reindex_incidence (H : Hypergraph V E) (vertices : V ≃ V') (edges : E ≃ E') (v : V) :
    (H.reindex vertices edges).incidence (vertices v) = (H.incidence v).map edges := by
  simp [reindex]

def OpenEmbedding.congrTarget {H : Hypergraph V E} {K K' : Hypergraph W F}
    (ι : OpenEmbedding H K) (h : K = K') : OpenEmbedding H K' where
  vertex := ι.vertex
  edge := ι.edge
  incidence v := by rw [← h]; exact ι.incidence v

def OpenEmbedding.reindexTarget {H : Hypergraph W F} {K : Hypergraph V E}
    (ι : OpenEmbedding H K) (vertices : V ≃ V') (edges : E ≃ E') :
    OpenEmbedding H (K.reindex vertices edges) where
  vertex := ι.vertex.trans vertices.toEmbedding
  edge := ι.edge.trans edges.toEmbedding
  incidence v := by
    change (H.incidence v).map (fun e => edges (ι.edge e)) =
      (K.reindex vertices edges).incidence (vertices (ι.vertex v))
    rw [reindex_incidence, ← ι.incidence, Multiset.map_map]
    rfl

def Retraction.reindexSource {H : Hypergraph V E} {K : Hypergraph W F}
    (ρ : Retraction H K) (vertices : V ≃ V') (edges : E ≃ E') :
    Retraction (H.reindex vertices edges) K where
  inclusion := {
    vertex := ρ.inclusion.vertex.trans vertices.toEmbedding
    edge := ρ.inclusion.edge.trans edges.toEmbedding
    incidence := by
      intro v
      change (K.incidence v).map (fun e => edges (ρ.inclusion.edge e)) =
        (H.reindex vertices edges).incidence (vertices (ρ.inclusion.vertex v))
      rw [reindex_incidence, ← ρ.inclusion.incidence, Multiset.map_map]
      rfl }
  retract := {
    vertex := fun v => ρ.retract.vertex (vertices.symm v)
    edge := fun e => ρ.retract.edge (edges.symm e)
    retained := by
      intro v w hv
      change ((H.incidence (vertices.symm v)).map edges).filterMap
        (fun e => ρ.retract.edge (edges.symm e)) = _
      rw [Multiset.filterMap_map]
      simpa only [Function.comp_def, Equiv.symm_apply_apply] using ρ.retract.retained _ w hv
    deleted := by
      intro v hv
      have he : ((H.reindex vertices edges).incidence v).filterMap
          (fun e => ρ.retract.edge (edges.symm e)) = (H.incidence (vertices.symm v)).filterMap ρ.retract.edge := by
        simp only [reindex, Multiset.filterMap_map, Function.comp_def, Equiv.symm_apply_apply]
      rw [he]
      exact ρ.retract.deleted _ hv }
  vertex_leftInverse v := by
    change ρ.retract.vertex (vertices.symm (vertices (ρ.inclusion.vertex v))) = some v
    rw [Equiv.symm_apply_apply, ρ.vertex_leftInverse]
  edge_leftInverse e := by
    change ρ.retract.edge (edges.symm (edges (ρ.inclusion.edge e))) = some e
    rw [Equiv.symm_apply_apply, ρ.edge_leftInverse]

end Hypergraph

namespace SparseSystem

theorem hypergraph_reindex {R C R' C' : Type*} (S : SparseSystem R C) (rows : R ≃ R') (cols : C ≃ C') :
    (S.reindex rows cols).hypergraph = S.hypergraph.reindex rows cols := by
  apply congrArg (Hypergraph.mk : (R' → Multiset C') → Hypergraph R' C')
  funext r
  simp [hypergraph, reindex]

end SparseSystem
end ThomGame

module

public import ThomGame.Finite.HypergraphCycles
public import ThomGame.Finite.HypergraphMultiplicity
public import ThomGame.Finite.HypergraphReindex

/-! # Indexed hypergraph cycles under sparse-system renumbering -/

@[expose] public section
namespace ThomGame.Hypergraph.Cycle

variable {R S R' S' : Type*} [DecidableEq R] [DecidableEq S]
  [DecidableEq R'] [DecidableEq S'] {A : SparseSystem R S}

def reindexRows (C : Cycle A.hypergraph) (rows : R ≃ R') (cols : S ≃ S') :
    Cycle (A.reindex rows cols).hypergraph where
  length := C.length
  length_ge_three := C.length_ge_three
  vertex := C.vertex.trans rows.toEmbedding
  edge := C.edge.trans cols.toEmbedding
  edge_multiplicity row j := by
    obtain ⟨r, rfl⟩ := rows.surjective row
    rw [SparseSystem.hypergraph_multiplicity_eq_ite]
    apply ite_cond_congr
    apply propext
    simpa only [SparseSystem.hypergraph_reindex, Hypergraph.reindex_incidence,
      Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Multiset.mem_map,
      cols.injective.eq_iff, exists_eq_right, rows.injective.eq_iff] using C.incident_iff r j

end ThomGame.Hypergraph.Cycle

module

public import ThomGame.Pictures.RowGraphEmbeddingInvariants
public import ThomGame.Pictures.CircuitEmbedding
public import ThomGame.Pictures.SunRimCover

/-!
# Actual circuit and facial-cover images under a row embedding

The port equivalence transports each original simple circuit with its
specified indexing and side. Distinct relation labels remain distinct
because the hypergraph vertex map is injective. Exact face orbits are
preserved by the proved conjugacy of the full face permutations.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {R S T U : Type*} {A : SparseSystem R S} {B : SparseSystem T U}
  {u v : List S} {G : SolutionGroup.RowGraph A u v}
  (ι : A.hypergraph.OpenEmbedding B.hypergraph)

theorem embedRows_noJoints [IsEmpty G.Joint] : IsEmpty (G.embedRows ι).Joint :=
  inferInstanceAs (IsEmpty G.Joint)

namespace SimpleCircuit

variable (C : G.SimpleCircuit)

@[reducible] noncomputable def embedRowsCircuit : (G.embedRows ι).SimpleCircuit :=
  C.map (G.rowEmbeddingPorts ι).toEmbedding (G.rowEmbeddingPorts_vertex_iff ι)
    (G.rowEmbeddingPorts_twin ι)

theorem embedRowsCircuit_port (x : Fin C.length × Bool) :
    (C.embedRowsCircuit ι).port x = G.rowEmbeddingPorts ι (C.port x) := C.map_port _ _ _ x

theorem embedRowsCircuit_label (x : Fin C.length × Bool) :
    Port.label (G.embedRows ι).jointLabel ((C.embedRowsCircuit ι).port x) =
      ι.edge (Port.label G.jointLabel (C.port x)) := by
  rw [C.embedRowsCircuit_port]
  exact G.rowEmbeddingPorts_label ι _

theorem embedRowsCircuit_isLabelCover (hc : C.IsLabelCover) : (C.embedRowsCircuit ι).IsLabelCover := by
  intro i
  obtain ⟨h, k, p, q, hi, ht, hn, hl⟩ := hc i
  refine ⟨h, k, ι.slotEquiv (G.hubLabel h) p, ι.slotEquiv (G.hubLabel k) q,
    congrArg (G.rowEmbeddingPorts ι) hi, ?_, hn, fun he => hl (ι.vertex.injective he)⟩
  exact (G.rowEmbeddingPorts_twin ι (C.dart i)).trans (congrArg (G.rowEmbeddingPorts ι) ht)

theorem embedRowsCircuit_boundsFaceOrbit (side : Bool) (hf : C.BoundsFaceOrbit side) :
    (C.embedRowsCircuit ι).BoundsFaceOrbit side :=
  C.boundsFaceOrbit_map (G.rowEmbeddingPorts ι).toEmbedding (G.rowEmbeddingPorts_vertex_iff ι)
    (G.rowEmbeddingPorts_twin ι) side hf (fun i => G.rowEmbeddingPorts_circuitStep ι (C.port (i, side)))

end SimpleCircuit
end ThomGame.Pictures.PortGraph

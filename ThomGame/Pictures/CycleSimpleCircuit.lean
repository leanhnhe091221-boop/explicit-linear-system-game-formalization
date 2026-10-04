module

public import ThomGame.Pictures.CycleWalk
public import ThomGame.Pictures.PairingCycleEnumeration
public import ThomGame.Pictures.SimpleCircuit

/-!
# Every nonempty restricted rim component is an actual simple circuit

The indexed circuit uses the original graph's darts, vertices and edges.
It traverses every vertex and edge of the restricted component exactly
once. This is the finite combinatorial cycle conclusion needed for
Slofstra Lemma 9.2; no disk-bounding assertion is inferred.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  {u v : List S} (G : SolutionGroup.RowGraph A u v) (C : Hypergraph.Cycle A.hypergraph)
  (hu : ∀ s ∈ u, s ∉ Set.range C.edge) (hv : ∀ s ∈ v, s ∉ Set.range C.edge)

noncomputable def rimSimpleCircuit (a : G.RimDart C) : G.SimpleCircuit := by
  let e := OrbitEnumeration.dart (G.rimWalk C hu hv) a
  refine {
    length := OrbitEnumeration.length (G.rimWalk C hu hv) a
    length_pos := OrbitEnumeration.length_pos _ _
    dart := e.trans (Function.Embedding.subtype _)
    vertex_injective := ?_
    edge_injective := ?_
    next_vertex := ?_
    next_ne_twin := ?_ }
  · intro i j hij
    apply e.injective
    apply PairingCycles.vertex_injective_on_orbit (G.rimPairing C) (G.rimVertexPairing C hu hv)
      (OrbitEnumeration.dart_sameCycle _ _ i) (OrbitEnumeration.dart_sameCycle _ _ j)
    exact (G.rimVertexPairing_eq_iff C hu hv _ _).mpr hij
  · intro i j hij
    apply e.injective
    apply PairingCycles.edge_injective_on_orbit (G.rimPairing C) (G.rimVertexPairing C hu hv)
      (OrbitEnumeration.dart_sameCycle _ _ i) (OrbitEnumeration.dart_sameCycle _ _ j)
    exact G.rimEdgeToEdge_injective C hij
  · intro i
    change (OrbitEnumeration.dart (G.rimWalk C hu hv) a (finRotate _ i)).val.vertex = _
    rw [OrbitEnumeration.dart_next]
    exact G.rimWalk_vertex C hu hv (e i)
  · intro i hi
    apply G.rimSwitch_ne_self C hu hv ((G.rimPairing C).twin (e i))
    apply Subtype.ext
    change (G.rimWalk C hu hv (e i)).val = (G.pairing.twin (e i).val)
    rw [← OrbitEnumeration.dart_next]
    exact hi

theorem rimSimpleCircuit_dart (a : G.RimDart C)
    (i : Fin (G.rimSimpleCircuit C hu hv a).length) :
    (G.rimSimpleCircuit C hu hv a).dart i = (OrbitEnumeration.dart (G.rimWalk C hu hv) a i).val := rfl

theorem rimSimpleCircuit_rim (a : G.RimDart C)
    (i : Fin (G.rimSimpleCircuit C hu hv a).length) :
    Port.label G.jointLabel ((G.rimSimpleCircuit C hu hv a).dart i) ∈ Set.range C.edge :=
  (OrbitEnumeration.dart (G.rimWalk C hu hv) a i).property

theorem rimSimpleCircuit_component_darts (a b : G.RimDart C)
    (hab : G.rimComponent C hu hv a = G.rimComponent C hu hv b) :
    ∃ i : Fin (G.rimSimpleCircuit C hu hv a).length,
      b.val = (G.rimSimpleCircuit C hu hv a).dart i ∨
        b.val = G.pairing.twin ((G.rimSimpleCircuit C hu hv a).dart i) := by
  have hc : RibbonConnectivity.Connected (G.rimPairing C).perm (G.rimVertexPairing C hu hv).perm a b :=
    (RibbonConnectivity.component_eq_iff _ _ a b).mp hab
  obtain ⟨⟨i, side⟩, hi⟩ := (PairingCycles.connected_iff_pairedDart
    (G.rimPairing C) (G.rimVertexPairing C hu hv) a b).mp hc
  refine ⟨i, ?_⟩
  cases side
  · exact Or.inl (congrArg Subtype.val hi).symm
  · exact Or.inr (congrArg Subtype.val hi).symm

theorem rimSimpleCircuit_vertex_complete (a b : G.RimDart C)
    (hab : G.rimComponent C hu hv a = G.rimComponent C hu hv b) :
    ∃! i : Fin (G.rimSimpleCircuit C hu hv a).length,
      ((G.rimSimpleCircuit C hu hv a).dart i).vertex = b.val.vertex := by
  let γ := G.rimSimpleCircuit C hu hv a
  obtain ⟨i, hi | hi⟩ := G.rimSimpleCircuit_component_darts C hu hv a b hab
  · refine ⟨i, congrArg Port.vertex hi.symm, fun j hj => ?_⟩
    exact γ.vertex_injective (hj.trans (congrArg Port.vertex hi))
  · have hn : (γ.dart (finRotate γ.length i)).vertex = b.val.vertex :=
      (γ.next_vertex i).trans (congrArg Port.vertex hi.symm)
    exact ⟨finRotate γ.length i, hn, fun j hj => γ.vertex_injective (hj.trans hn.symm)⟩

theorem rimSimpleCircuit_edge_complete (a b : G.RimDart C)
    (hab : G.rimComponent C hu hv a = G.rimComponent C hu hv b) :
    ∃! i : Fin (G.rimSimpleCircuit C hu hv a).length,
      G.pairing.edge ((G.rimSimpleCircuit C hu hv a).dart i) = G.pairing.edge b.val := by
  let γ := G.rimSimpleCircuit C hu hv a
  obtain ⟨i, hi | hi⟩ := G.rimSimpleCircuit_component_darts C hu hv a b hab
  · have he := congrArg G.pairing.edge hi.symm
    exact ⟨i, he, fun j hj => γ.edge_injective (hj.trans he.symm)⟩
  · have he : G.pairing.edge (γ.dart i) = G.pairing.edge b.val := by
      rw [hi, G.pairing.edge_twin]
    exact ⟨i, he, fun j hj => γ.edge_injective (hj.trans he.symm)⟩

end ThomGame.Pictures.PortGraph

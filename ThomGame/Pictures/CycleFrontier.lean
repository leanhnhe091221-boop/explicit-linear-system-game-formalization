module

public import ThomGame.Pictures.CycleSimpleCircuit
public import ThomGame.Pictures.CircuitFrontier

/-!
# A rim frontier contains no rim labels

At a vertex of one lifted rim component, every port bearing a rim label
belongs to that same component and is one of its two marked ports.
Consequently the ordered frontier word has no letters from the original
hypergraph cycle, as required for the sun-region arguments.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  {u v : List S} (G : SolutionGroup.RowGraph A u v) (C : Hypergraph.Cycle A.hypergraph)
  (hu : ∀ s ∈ u, s ∉ Set.range C.edge) (hv : ∀ s ∈ v, s ∉ Set.range C.edge)

theorem rimSimpleCircuit_component_of_vertex (a b : G.RimDart C)
    (hb : (G.rimSimpleCircuit C hu hv a).OnCircuitVertex b.val.vertex) :
    G.rimComponent C hu hv a = G.rimComponent C hu hv b := by
  obtain ⟨i, hi⟩ := hb
  let d := OrbitEnumeration.dart (G.rimWalk C hu hv) a i
  have hd : G.rimComponent C hu hv a = G.rimComponent C hu hv d := by
    apply (component_eq_iff _ _ _ _).mpr
    apply (PairingCycles.connected_iff (G.rimPairing C) (G.rimVertexPairing C hu hv) a d).mpr
    exact Or.inl (OrbitEnumeration.dart_sameCycle _ _ i)
  exact hd.trans (G.rimComponent_vertex C hu hv hi)

theorem rimSimpleCircuit_marked_of_component (a b : G.RimDart C)
    (hb : G.rimComponent C hu hv a = G.rimComponent C hu hv b) :
    (G.rimSimpleCircuit C hu hv a).Marked b.val := by
  let γ := G.rimSimpleCircuit C hu hv a
  obtain ⟨i, hi | hi⟩ := G.rimSimpleCircuit_component_darts C hu hv a b hb
  · exact ⟨(i, false), hi.symm⟩
  · rw [hi]
    exact (γ.marked_twin_iff (γ.dart i)).mpr ⟨(i, false), rfl⟩

theorem rimSimpleCircuit_marked_iff (a b : G.RimDart C) :
    (G.rimSimpleCircuit C hu hv a).Marked b.val ↔
      G.rimComponent C hu hv a = G.rimComponent C hu hv b := by
  constructor
  · intro hb
    exact G.rimSimpleCircuit_component_of_vertex C hu hv a b
      ((G.rimSimpleCircuit C hu hv a).marked_onCircuitVertex hb)
  · exact G.rimSimpleCircuit_marked_of_component C hu hv a b

theorem rimSimpleCircuit_frontier_not_rim (a : G.RimDart C) (s : Bool) (b : G.Dart)
    (hb : (G.rimSimpleCircuit C hu hv a).Frontier s b) :
    Port.label G.jointLabel b ∉ Set.range C.edge := by
  intro hm
  have hvb := ((G.rimSimpleCircuit C hu hv a).exists_frontier_iff b).mp ⟨s, hb⟩
  exact hb.2 (G.rimSimpleCircuit_marked_of_component C hu hv a ⟨b, hm⟩
    (G.rimSimpleCircuit_component_of_vertex C hu hv a ⟨b, hm⟩ hvb.1))

theorem rimSimpleCircuit_frontierWord_no_rim (a : G.RimDart C) (s : Bool) :
    ∀ z ∈ (G.rimSimpleCircuit C hu hv a).frontierWord s, z ∉ Set.range C.edge := by
  intro z hz
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
  exact G.rimSimpleCircuit_frontier_not_rim C hu hv a s _
    ((G.rimSimpleCircuit C hu hv a).frontierEnumeration s i).property

end ThomGame.Pictures.PortGraph

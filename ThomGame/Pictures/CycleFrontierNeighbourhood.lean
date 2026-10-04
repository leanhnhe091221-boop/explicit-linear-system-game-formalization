module

public import ThomGame.Pictures.CycleGermCharge

/-!
# The actual rim frontier lies in every open neighbourhood of the rim

Circuit hubs are labelled by cycle vertices, so all their incident
labels lie in an open neighbourhood. A subdivision joint on the rim has
only rim-labelled ports and cannot contribute an unmarked frontier.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {R S T U : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
    (G : SolutionGroup.RowGraph A [] []) (C : Hypergraph.Cycle A.hypergraph)

theorem rimSimpleCircuit_joint_label (a : G.RimDart C) (j : G.Joint)
    (hj : (G.rimSimpleCircuit C (by simp) (by simp) a).OnCircuitVertex (.inr (.inr j))) :
    G.jointLabel j ∈ Set.range C.edge := by
  obtain ⟨i, hi⟩ := hj
  have hr := G.rimSimpleCircuit_rim C (by simp) (by simp) a i
  cases he : (G.rimSimpleCircuit C (by simp) (by simp) a).dart i with
  | top k => exact k.elim0
  | bottom k => exact k.elim0
  | hub h k => rw [he] at hi; cases hi
  | joint k b =>
    rw [he] at hi hr
    have hk : k = j := Sum.inr.inj (Sum.inr.inj hi)
    subst k
    exact hr

theorem rimSimpleCircuit_frontier_in_open {K : Hypergraph T U}
    (f : Hypergraph.OpenEmbedding K A.hypergraph)
    (hc : ∀ r ∈ Set.range C.vertex, r ∈ Set.range f.vertex)
    (a : G.RimDart C) (s : Bool) (b : G.Dart)
    (hb : (G.rimSimpleCircuit C (by simp) (by simp) a).Frontier s b) :
    Port.label G.jointLabel b ∈ Set.range f.edge := by
  have hv := ((G.rimSimpleCircuit C (by simp) (by simp) a).exists_frontier_iff b).mp ⟨s, hb⟩
  cases b with
  | top i => exact i.elim0
  | bottom i => exact i.elim0
  | hub h i =>
    obtain ⟨v, he⟩ := hc _ (G.rimSimpleCircuit_hub_label C a h hv.1)
    have hin : Port.label G.jointLabel (.hub h i : G.Dart) ∈ A.hypergraph.incidence (G.hubLabel h) :=
      (A.mem_hypergraph_incidence _ _).mpr ⟨i, (SolutionGroup.rowGraph_port_label A G h i).symm⟩
    rw [← he, ← f.incidence] at hin
    obtain ⟨e, _, he⟩ := Multiset.mem_map.mp hin
    exact ⟨e, he⟩
  | joint j b =>
    exact (G.rimSimpleCircuit_frontier_not_rim C (by simp) (by simp) a s _ hb
      (G.rimSimpleCircuit_joint_label C a j hv.1)).elim

theorem rimSimpleCircuit_frontierWord_in_open {K : Hypergraph T U}
    (f : Hypergraph.OpenEmbedding K A.hypergraph)
    (hc : ∀ r ∈ Set.range C.vertex, r ∈ Set.range f.vertex)
    (a : G.RimDart C) (s : Bool) :
    ∀ z ∈ (G.rimSimpleCircuit C (by simp) (by simp) a).frontierWord s, z ∈ Set.range f.edge := by
  intro z hz
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
  exact G.rimSimpleCircuit_frontier_in_open C f hc a s _
    ((G.rimSimpleCircuit C (by simp) (by simp) a).frontierEnumeration s i).property

end ThomGame.Pictures.PortGraph

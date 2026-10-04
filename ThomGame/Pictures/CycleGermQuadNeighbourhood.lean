module

public import ThomGame.Pictures.CircuitGermQuadrilaterals
public import ThomGame.Pictures.CycleFrontierNeighbourhood

/-!
# Original germ quadrilateral labels lie in an open cycle neighbourhood

Both quadrilateral hubs are circuit hubs. Openness therefore includes
every incident edge, including the middle edge of the quadrilateral.
The boundary edge is included by the exact frontier-word theorem.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open RibbonConnectivity

variable {R S T U : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  (G : SolutionGroup.RowGraph A [] []) (C : Hypergraph.Cycle A.hypergraph)
  {K : Hypergraph T U} (f : K.OpenEmbedding A.hypergraph)
  (hc : ∀ r ∈ Set.range C.vertex, r ∈ Set.range f.vertex)
  (a : G.RimDart C)

include hc in
theorem rimSimpleCircuit_hub_port_in_open (h : G.Hub)
    (hh : (G.rimSimpleCircuit C (by simp) (by simp) a).OnCircuitVertex (.inr (.inl h)))
    (j : Fin 3) : Port.label G.jointLabel (.hub h j : G.Dart) ∈ Set.range f.edge := by
  obtain ⟨v, he⟩ := hc _ (G.rimSimpleCircuit_hub_label C a h hh)
  have hin : Port.label G.jointLabel (.hub h j : G.Dart) ∈ A.hypergraph.incidence (G.hubLabel h) :=
    (A.mem_hypergraph_incidence _ _).mpr ⟨j, (SolutionGroup.rowGraph_port_label A G h j).symm⟩
  rw [← he, ← f.incidence] at hin
  obtain ⟨e, _, he⟩ := Multiset.mem_map.mp hin
  exact ⟨e, he⟩

variable (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (Component G.circuitStep G.pairing.perm)) (s : Bool)
  (q : ((G.rimSimpleCircuit C (by simp) (by simp) a).germGraph hEuler s).swapBoundary.BoundaryQuadPath)

include hc in
theorem rimGermQuad_labels_in_open
    (x : ((G.rimSimpleCircuit C (by simp) (by simp) a).germGraph hEuler s).swapBoundary.Dart)
    (hx : x ∈ [q.firstDart, q.middleDart, q.lastDart]) :
    Port.label ((G.rimSimpleCircuit C (by simp) (by simp) a).germGraph hEuler s).swapBoundary.jointLabel x ∈
      Set.range f.edge := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · change Port.label _ (((G.rimSimpleCircuit C (by simp) (by simp) a).germGraph hEuler s).swapBoundary.boundaryDart
      q.start) ∈ _
    cases he : q.start with
    | inl j =>
      exact G.rimSimpleCircuit_frontierWord_in_open C f hc a (!s) _ (List.get_mem _ j)
    | inr j => exact j.elim0
  · exact G.rimSimpleCircuit_hub_port_in_open C f hc a q.firstHub.val
      ((G.rimSimpleCircuit C (by simp) (by simp) a).germQuad_firstHub_onCircuit hEuler s q) q.firstSlot
  · exact G.rimSimpleCircuit_hub_port_in_open C f hc a q.secondHub.val
      ((G.rimSimpleCircuit C (by simp) (by simp) a).germQuad_secondHub_onCircuit hEuler s q) q.secondSlot

end ThomGame.Pictures.PortGraph

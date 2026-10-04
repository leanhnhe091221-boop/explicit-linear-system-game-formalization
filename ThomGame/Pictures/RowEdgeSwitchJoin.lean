module

public import ThomGame.Pictures.RowEdgeSwitchRims
public import ThomGame.Pictures.CircuitCopyEdges

/-!
# Joining two copied rims creates an actual noncopy

The switched graph keeps its two selected edges distinct, but places
them in the same rim component. Equal labels then contradict the copy
predicate. The component count decreases by exactly one.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.RowEdgeSwitch

open Equiv RibbonConnectivity
open scoped Classical

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  {G : SolutionGroup.RowGraph A [] []} (s : G.RowEdgeSwitch)
  (γ : Hypergraph.Cycle A.hypergraph)

omit [DecidableEq R] [DecidableEq S] in
theorem graph_different_edges : s.graph.pairing.edge s.first ≠ s.graph.pairing.edge s.second := by
  intro he
  rcases (s.graph.pairing.edge_eq_iff _ _).mp he with he | he
  · exact s.first_ne_second he
  · rw [s.twin_second] at he
    exact G.pairing.ne_self s.first he.symm

variable (ha : Port.label G.jointLabel s.first ∈ Set.range γ.edge)
  (hsep : G.rimComponent γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim ⟨s.first, ha⟩ ≠
    G.rimComponent γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim ⟨s.second, s.label_eq ▸ ha⟩)

include hsep in
theorem rim_components_join :
    s.graph.rimComponent γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim ⟨s.first, ha⟩ =
      s.graph.rimComponent γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim ⟨s.second, s.label_eq ▸ ha⟩ := by
  apply (component_eq_iff _ _ _ _).mpr
  rw [s.rimPairing_perm γ ha, s.rimVertexPairing_eq]
  exact PairingCycles.switchedEdge_connected (G.rimPairing γ) (G.rimVertexPairing γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim)
    (fun hc => hsep ((component_eq_iff _ _ _ _).mpr hc))

include hsep in
theorem rimCount_join : s.graph.rimCount γ + 1 = G.rimCount γ := by
  have he := PairingCycles.switchedEdge_component_card_join
    (G.rimPairing γ) (G.rimVertexPairing γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim)
    (fun hc => hsep ((component_eq_iff _ _ _ _).mpr hc))
  unfold rimCount RimComponent
  rw [s.rimPairing_perm γ ha, s.rimVertexPairing_eq]
  exact he

include hsep in
theorem joined_rim_not_copy :
    ¬ (s.graph.rimSimpleCircuit γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim ⟨s.first, ha⟩).IsLabelCopy := by
  intro hc
  let C := s.graph.rimSimpleCircuit γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim ⟨s.first, ha⟩
  exact s.graph_different_edges (C.copy_edge_eq_of_marked_label hc
    (s.graph.rimSimpleCircuit_marked_of_component γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim _ _ rfl)
    (s.graph.rimSimpleCircuit_marked_of_component γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim _ _
      (s.rim_components_join γ ha hsep)) s.label_eq)

theorem totalRimCount_split_join {I : Type*} [Fintype I]
    (Φ : I → Hypergraph.Cycle A.hypergraph) (i j : I) (hij : i ≠ j)
    (hsplit : s.graph.rimCount (Φ i) = G.rimCount (Φ i) + 1)
    (hjoin : s.graph.rimCount (Φ j) + 1 = G.rimCount (Φ j))
    (hother : ∀ k : I, k ≠ i → k ≠ j → Port.label G.jointLabel s.first ∉ Set.range (Φ k).edge) :
    s.graph.totalRimCount Φ = G.totalRimCount Φ := by
  have he (k : I) : s.graph.rimCount (Φ k) + (if k = j then 1 else 0) =
      G.rimCount (Φ k) + (if k = i then 1 else 0) := by
    by_cases hki : k = i
    · subst k
      rw [ite_eq_right hij, ite_eq_left rfl, Nat.add_zero]
      exact hsplit
    · by_cases hkj : k = j
      · subst k
        rw [ite_eq_left rfl, ite_eq_right hij.symm, Nat.add_zero]
        exact hjoin
      · rw [ite_eq_right hki, ite_eq_right hkj, Nat.add_zero, Nat.add_zero]
        exact s.rimCount_of_avoids (Φ k) (hother k hki hkj)
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun k _ => he k)
  simp only [Finset.sum_add_distrib] at hsum
  simp at hsum
  exact hsum

end ThomGame.Pictures.PortGraph.RowEdgeSwitch

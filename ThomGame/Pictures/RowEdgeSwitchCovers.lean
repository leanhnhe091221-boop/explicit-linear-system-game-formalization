module

public import ThomGame.Pictures.RowEdgeSwitchRims

/-!
# Same-row reconnection preserves label covering

The exchanged ports remain at hubs with the same row label. Transporting
either end of any covered edge therefore preserves the two distinct hub
labels, including edges in other constellation cycles.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.RowEdgeSwitch

open Equiv
open scoped Classical

variable {R S : Type*} {A : SparseSystem R S} {u v : List S}
  {G : SolutionGroup.RowGraph A u v} (s : G.RowEdgeSwitch)

theorem portSwap_hub (h : G.Hub) (p : Fin 3) :
    ∃ (h' : G.Hub) (p' : Fin 3),
      s.portSwap (.hub h p) = .hub h' p' ∧ G.hubLabel h' = G.hubLabel h := by
  by_cases ha : (Port.hub h p : G.Dart) = s.first
  · have hh := (G.row_hub_eq_iff.mp ha).1
    refine ⟨s.right, s.slot, ?_, s.same_row.symm.trans (congrArg G.hubLabel hh).symm⟩
    rw [ha]
    exact swap_apply_left _ _
  · by_cases hb : (Port.hub h p : G.Dart) = s.second
    · have hh := (G.row_hub_eq_iff.mp hb).1
      refine ⟨s.left, s.slot, ?_, s.same_row.trans (congrArg G.hubLabel hh).symm⟩
      rw [hb]
      exact swap_apply_right _ _
    · exact ⟨h, p, swap_apply_of_ne_of_ne ha hb, rfl⟩

theorem twin_portSwap (x : G.Dart) :
    s.graph.pairing.twin (s.portSwap x) = s.portSwap (G.pairing.twin x) := by
  rw [s.twin]
  change _ = swap s.first s.second (G.pairing.twin x)
  rw [show s.portSwap (s.portSwap x) = x from swap_apply_self _ _ x]
  rfl

theorem edgeHasDistinctHubLabels_portSwap {x : G.Dart} (hx : G.EdgeHasDistinctHubLabels x) :
    s.graph.EdgeHasDistinctHubLabels (s.portSwap x) := by
  obtain ⟨h, k, p, q, hp, hq, _, hl⟩ := hx
  obtain ⟨h', p', hh, hhl⟩ := s.portSwap_hub h p
  obtain ⟨k', q', hk, hkl⟩ := s.portSwap_hub k q
  have hn : G.hubLabel h' ≠ G.hubLabel k' := fun he => hl (hhl.symm.trans (he.trans hkl))
  refine ⟨h', k', p', q', ?_, ?_, fun he => hn (congrArg G.hubLabel he), hn⟩
  · exact (congrArg s.portSwap hp).trans hh
  · exact (s.twin_portSwap x).trans ((congrArg s.portSwap hq).trans hk)

variable [DecidableEq R] [DecidableEq S] {G : SolutionGroup.RowGraph A [] []}
  (s : G.RowEdgeSwitch) (γ : Hypergraph.Cycle A.hypergraph)

theorem rim_covers (hc : ∀ a : G.RimDart γ,
    (G.rimSimpleCircuit γ (by simp) (by simp) a).IsLabelCover) :
    ∀ a : s.graph.RimDart γ, (s.graph.rimSimpleCircuit γ (by simp) (by simp) a).IsLabelCover := by
  intro a i
  let x := (s.graph.rimSimpleCircuit γ (by simp) (by simp) a).dart i
  have hx : Port.label G.jointLabel (s.portSwap x) ∈ Set.range γ.edge := by
    rw [s.portSwap_label]
    exact s.graph.rimSimpleCircuit_rim γ (by simp) (by simp) a i
  have he := s.edgeHasDistinctHubLabels_portSwap (rim_cover_edge γ hc (s.portSwap x) hx)
  rw [show s.portSwap (s.portSwap x) = x from swap_apply_self _ _ x] at he
  exact he

end ThomGame.Pictures.PortGraph.RowEdgeSwitch

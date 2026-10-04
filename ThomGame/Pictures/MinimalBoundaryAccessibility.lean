module

public import ThomGame.Pictures.DiagramComponentExtraction
public import ThomGame.Pictures.ComponentSmoothingTrace

/-!
# Hubs of a minimum-size diagram reach the boundary

Deleting a whole boundaryless component retains the ordered boundary.
If the component contains a relation hub, the resulting genuine diagram
is smaller. Thus a diagram that minimizes size among all diagrams with
its boundary has no such component. Accessibility survives smoothing,
including steps that record isolated circles.
-/

@[expose] public section
namespace ThomGame.Pictures

open RibbonConnectivity
open scoped BigOperators Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}

namespace PortGraph

def HubsReachBoundary (G : PortGraph P u v) : Prop :=
  ∀ h : G.Hub, ∃ i : BoundaryIndex u v,
    G.Reachable (.inr (.inl h)) (G.boundaryVertex i)

theorem connected_boundary_of_hubsReachBoundary (G : PortGraph P u v) [IsEmpty G.Joint]
    (hb : G.HubsReachBoundary) (x : G.Dart) :
    ∃ i : BoundaryIndex u v, Connected G.pairing.perm G.circuitStep x (G.boundaryDart i) := by
  cases x with
  | top i => exact ⟨.inl i, Connected.refl _⟩
  | bottom i => exact ⟨.inr i, Connected.refl _⟩
  | hub h j =>
    obtain ⟨i, hi⟩ := hb h
    exact ⟨i, G.reachable_connects_darts hi (.hub h j) (G.boundaryDart i) rfl
      (G.boundaryDart_vertex i)⟩
  | joint j _ => exact isEmptyElim j

theorem smooth_hubsReachBoundary (G : PortGraph P u v) (j : G.Joint)
    (hn : ∀ h : G.Hub, 0 < (P.word (G.hubLabel h)).length)
    (hb : G.HubsReachBoundary) : (G.smooth j).HubsReachBoundary := by
  intro h
  obtain ⟨i, hi⟩ := hb h
  refine ⟨i, ?_⟩
  let a : (G.smooth j).Dart := .hub h ⟨0, hn h⟩
  have hc : Connected G.pairing.perm G.circuitStep
      (G.smoothPortEmbedding j a) (G.boundaryDart i) := by
    apply G.reachable_connects_darts hi
    · rfl
    · exact G.boundaryDart_vertex i
  have hs := (G.smooth_connected_iff j a ((G.smooth j).boundaryDart i)).mpr
    (by rw [G.smooth_boundaryDart]; exact hc)
  have hr := (G.smooth j).connected_vertex_reachable hs
  rw [(G.smooth j).boundaryDart_vertex] at hr
  exact hr

end PortGraph

namespace Diagram

theorem hubsReachBoundary_of_minimum_size (d : Diagram P u v)
    (hmin : ∀ e : Diagram P u v, d.size ≤ e.size) : d.graph.HubsReachBoundary := by
  intro h
  by_contra hno
  let c : d.graph.Selection := {
    pick x := decide (d.graph.graphComponent x ≠ d.graph.hubComponent h)
    edge a := by
      have he := (d.graph.graphComponent_eq_iff _ _).mpr (d.graph.reachable_edge a)
      rw [he] }
  have hb (i : PortGraph.BoundaryIndex u v) :
      d.graph.graphComponent (d.graph.boundaryVertex i) ≠ d.graph.hubComponent h := by
    intro he
    exact hno ⟨i, (d.graph.graphComponent_eq_iff _ _).mp he.symm⟩
  have htop : selectPositions u c.top = u := by
    have ht (i : Fin u.length) : c.top i = true := by
      change decide (d.graph.graphComponent (d.graph.boundaryVertex (.inl i)) ≠
        d.graph.hubComponent h) = true
      exact decide_eq_true (hb (.inl i))
    exact (selectPositions_congr u ht).trans (selectPositions_true u)
  have hbottom : selectPositions v c.bottom = v := by
    have ht (i : Fin v.length) : c.bottom i = true := by
      change decide (d.graph.graphComponent (d.graph.boundaryVertex (.inr i)) ≠
        d.graph.hubComponent h) = true
      exact decide_eq_true (hb (.inr i))
    exact (selectPositions_congr v ht).trans (selectPositions_true v)
  have hle := hmin ((d.select c).cast htop hbottom)
  rw [size_cast, d.size_select, ← d.graph_hub_card] at hle
  have hlt : (∑ x : d.graph.Hub, if c.hub x then 1 else 0) < Fintype.card d.graph.Hub := by
    calc
      (∑ x : d.graph.Hub, if c.hub x then 1 else 0) < ∑ _ : d.graph.Hub, (1 : Nat) := by
        apply Finset.sum_lt_sum
        · intro x _; split <;> omega
        · refine ⟨h, Finset.mem_univ _, ?_⟩
          simp [c, PortGraph.Selection.hub, PortGraph.hubComponent]
      _ = Fintype.card d.graph.Hub := by simp
  exact (Nat.not_lt_of_ge hle) hlt

end Diagram

namespace Smoothing

theorem hubsReachBoundary {G H : PortGraph P u v} {circles : List S}
    (t : Smoothing G H circles)
    (hn : ∀ h : G.Hub, 0 < (P.word (G.hubLabel h)).length)
    (hb : G.HubsReachBoundary) : H.HubsReachBoundary := by
  induction t with
  | refl _ => exact hb
  | @step G H circles j tail ih => exact ih hn (G.smooth_hubsReachBoundary j hn hb)

end Smoothing
end ThomGame.Pictures

module

public import ThomGame.Pictures.MinimalCircuitGerm

/-! # The minimal odd germ conclusion through genuine smoothing traces -/

@[expose] public section
namespace ThomGame.Pictures

open RibbonConnectivity
open scoped BigOperators Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}

namespace PortGraph

theorem smooth_hubs_reachable (G : PortGraph P u v) (j : G.Joint)
    (hn : ∀ h : G.Hub, 0 < (P.word (G.hubLabel h)).length)
    (hc : ∀ h k : G.Hub, G.Reachable (.inr (.inl h)) (.inr (.inl k))) :
    ∀ h k : (G.smooth j).Hub, (G.smooth j).Reachable (.inr (.inl h)) (.inr (.inl k)) := by
  intro h k
  let a : (G.smooth j).Dart := .hub h ⟨0, hn h⟩
  let b : (G.smooth j).Dart := .hub k ⟨0, hn k⟩
  apply (G.smooth j).connected_vertex_reachable (a := a) (b := b)
  apply (G.smooth_connected_iff j a b).mpr
  exact (G.connected_iff_vertex_reachable _ _).mpr (hc h k)

end PortGraph

namespace Smoothing

theorem hubs_reachable {G H : PortGraph P u v} {circles : List S} (t : Smoothing G H circles)
    (hn : ∀ h : G.Hub, 0 < (P.word (G.hubLabel h)).length)
    (hc : ∀ h k : G.Hub, G.Reachable (.inr (.inl h)) (.inr (.inl k))) :
    ∀ h k : H.Hub, H.Reachable (.inr (.inl h)) (.inr (.inl k)) := by
  induction t with
  | refl _ => exact hc
  | @step G H circles j tail ih => exact ih hn (G.smooth_hubs_reachable j hn hc)

theorem minimal_odd_hubs_reachable {d : Diagram P [] []} {H : PortGraph P [] []} {circles : List S}
    (t : Smoothing d.graph H circles) (hmin : d.Minimal) (hs : d.sign = 1)
    (hn : ∀ h : d.graph.Hub, 0 < (P.word (d.graph.hubLabel h)).length) :
    ∀ h k : H.Hub, H.Reachable (.inr (.inl h)) (.inr (.inl k)) :=
  t.hubs_reachable hn (d.minimal_odd_hubs_reachable hmin hs)

theorem minimal_odd_circuit_exists_germ_sign_zero
    {d : Diagram P [] []} {H : PortGraph P [] []} {circles : List S}
    (t : Smoothing d.graph H circles) (hmin : d.Minimal) (hs : d.sign = 1)
    (hn : ∀ h : d.graph.Hub, 0 < (P.word (d.graph.hubLabel h)).length)
    (C : H.SimpleCircuit)
    (hCircuit : (∑ h : C.CircuitHub, P.parity (H.hubLabel h.val)) = 0) :
    ∃ s, (C.germGraph (t.diagram_dualEuler hn) s).sign = 0 :=
  C.exists_germ_sign_zero_of_hubs_reachable (t.diagram_dualEuler hn)
    (t.minimal_odd_hubs_reachable hmin hs hn) (t.sign.trans (d.graph_sign.trans hs)) hCircuit

end Smoothing
end ThomGame.Pictures

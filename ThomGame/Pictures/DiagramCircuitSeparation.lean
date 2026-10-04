module

public import ThomGame.Pictures.SimpleCircuitSeparation
public import ThomGame.Pictures.SmoothingEuler

/-! # Circuit separation for diagrams and their smoothed graphs -/

@[expose] public section
namespace ThomGame.Pictures

open RibbonConnectivity
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}

theorem PortGraph.dualEuler_eq_twice_components (G : PortGraph P u v)
    (h : eulerDefect G.pairing.perm G.circuitStep = 0) :
    RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm) := by
  have hc := Nat.card_congr (componentEquiv G.pairing.perm G.circuitStep G.circuitStep G.pairing.perm
    (RotationEuler.connected_swap_iff G.pairing.perm G.circuitStep))
  rw [G.dualEuler_eq_eulerCount]
  unfold eulerDefect at h
  omega

theorem Diagram.graph_dualEuler (d : Diagram P u v) :
    RotationEuler.count d.graph.circuitStep d.graph.pairing.perm =
      2 * Nat.card (Component d.graph.circuitStep d.graph.pairing.perm) :=
  d.graph.dualEuler_eq_twice_components d.graph_eulerDefect

theorem Diagram.cut_component_card (d : Diagram P u v) (C : d.graph.SimpleCircuit) :
    Nat.card (Component d.graph.circuitStep C.cutPairing) =
      Nat.card (Component d.graph.circuitStep d.graph.pairing.perm) + 1 :=
  C.cut_component_card d.graph_dualEuler

theorem Smoothing.diagram_dualEuler {d : Diagram P u v} {H : PortGraph P u v} {circles : List S}
    (h : Smoothing d.graph H circles)
    (hn : ∀ g : d.graph.Hub, 0 < (P.word (d.graph.hubLabel g)).length) :
    RotationEuler.count H.circuitStep H.pairing.perm =
      2 * Nat.card (Component H.circuitStep H.pairing.perm) :=
  H.dualEuler_eq_twice_components (h.diagram_eulerDefect hn)

theorem Smoothing.diagram_cut_component_card {d : Diagram P u v} {H : PortGraph P u v} {circles : List S}
    (h : Smoothing d.graph H circles)
    (hn : ∀ g : d.graph.Hub, 0 < (P.word (d.graph.hubLabel g)).length) (C : H.SimpleCircuit) :
    Nat.card (Component H.circuitStep C.cutPairing) =
      Nat.card (Component H.circuitStep H.pairing.perm) + 1 :=
  C.cut_component_card (h.diagram_dualEuler hn)

end ThomGame.Pictures

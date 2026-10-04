module

public import ThomGame.Pictures.SmoothingComponentCounts
public import ThomGame.Pictures.ComponentSmoothingTrace
public import ThomGame.Pictures.DiagramEuler

/-!
# Component counts and the Euler identity through smoothing traces

Every discarded circle accounts for one missing component and two
missing circuits. Thus the actual vertex Euler defect is preserved.
Nonempty hub words are an explicit hypothesis where dart components
are identified with components of all vertices.
-/

@[expose] public section
namespace ThomGame.Pictures.Smoothing

open RibbonConnectivity

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
variable {G H : PortGraph P u v} {circles : List S}

theorem hub_word_nonempty (d : Smoothing G H circles)
    (hn : ∀ h : G.Hub, 0 < (P.word (G.hubLabel h)).length) :
    ∀ h : H.Hub, 0 < (P.word (H.hubLabel h)).length := by
  intro h
  obtain ⟨g, rfl⟩ := d.hubEquiv.surjective h
  rw [d.hubLabel]
  exact hn g

theorem dartComponent_card (d : Smoothing G H circles) :
    Nat.card H.DartComponent + circles.length = Nat.card G.DartComponent := by
  induction d with
  | refl _ => rfl
  | @step G H circles j tail ih =>
    have hj := G.smooth_dartComponent_card j
    rw [List.length_append]
    omega

theorem graphComponent_card (d : Smoothing G H circles)
    (hn : ∀ h : G.Hub, 0 < (P.word (G.hubLabel h)).length) :
    Nat.card H.GraphComponent + circles.length = Nat.card G.GraphComponent := by
  have hc := d.dartComponent_card
  rw [Nat.card_congr (G.dartComponentEquiv hn),
    Nat.card_congr (H.dartComponentEquiv (d.hub_word_nonempty hn))] at hc
  exact hc

theorem graphEulerDefect (d : Smoothing G H circles)
    (hn : ∀ h : G.Hub, 0 < (P.word (G.hubLabel h)).length) :
    H.ribbonEuler - 2 * (Nat.card H.GraphComponent : Int) =
      G.ribbonEuler - 2 * (Nat.card G.GraphComponent : Int) := by
  have he := d.ribbonEuler
  have hc := d.graphComponent_card hn
  omega

theorem eulerDefect (d : Smoothing G H circles)
    (hn : ∀ h : G.Hub, 0 < (P.word (G.hubLabel h)).length) :
    RibbonConnectivity.eulerDefect H.pairing.perm H.circuitStep =
      RibbonConnectivity.eulerDefect G.pairing.perm G.circuitStep := by
  rw [H.eulerDefect_eq_ribbonEuler (d.hub_word_nonempty hn), G.eulerDefect_eq_ribbonEuler hn]
  exact d.graphEulerDefect hn

theorem diagram_ribbonEuler {d : Diagram P u v}
    (h : Smoothing d.graph H circles)
    (hn : ∀ g : d.graph.Hub, 0 < (P.word (d.graph.hubLabel g)).length) :
    H.ribbonEuler = 2 * (Nat.card H.GraphComponent : Int) := by
  have he := h.graphEulerDefect hn
  rw [d.graph_ribbonEuler hn] at he
  omega

theorem diagram_eulerDefect {d : Diagram P u v}
    (h : Smoothing d.graph H circles)
    (hn : ∀ g : d.graph.Hub, 0 < (P.word (d.graph.hubLabel g)).length) :
    RibbonConnectivity.eulerDefect H.pairing.perm H.circuitStep = 0 := by
  rw [h.eulerDefect hn]
  exact d.graph_eulerDefect

end ThomGame.Pictures.Smoothing

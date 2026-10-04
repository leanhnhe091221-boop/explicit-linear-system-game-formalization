module

public import ThomGame.Pictures.SmoothedCircuitCovers
public import ThomGame.Pictures.CompositionEuler
public import ThomGame.Pictures.BottomGraphRealization
public import ThomGame.Pictures.DisconnectedClosedGraph

/-!
# Closed gluing with an actual reduced graph and retained facial covers

Glue two prescribed boundaries and fully smooth the resulting graph.
The certificate records the actual trace and every lost circle. Every
facial label cover wholly in either input has a specified surviving
circuit, with its exact original ports and labels. Euler saturation of
the inputs gives saturation and a genuine diagram witness of the glued
graph, preserving the entire relation multiset.

The diagram witness is used for size/sign bookkeeping; no isomorphism
between its extracted graph and the glued graph is asserted here.
-/

@[expose] public section
namespace ThomGame.Pictures

open RibbonConnectivity
open scoped BigOperators

variable {R S : Type*} {P : InvolutionPresentation R S} {w : List S}
  (G : PortGraph P [] w) (H : PortGraph P w [])

structure ClosedGluingReduction where
  graph : PortGraph P [] []
  circles : List S
  trace : Smoothing (G.comp H) graph circles
  noJoints : IsEmpty graph.Joint

attribute [instance] ClosedGluingReduction.noJoints

noncomputable def PortGraph.reduceClosedGluing : ClosedGluingReduction G H :=
  Classical.choice (by
    obtain ⟨K, cs, ⟨t⟩, hj⟩ := Smoothing.exists_without_junctions (G.comp H)
    exact ⟨⟨K, cs, t, hj⟩⟩)

namespace ClosedGluingReduction

variable {G H} (d : ClosedGluingReduction G H)

theorem hub_relations : (∑ h : d.graph.Hub, ([d.graph.hubLabel h] : Multiset R)) =
    (∑ g : G.Hub, ([G.hubLabel g] : Multiset R)) +
      ∑ h : H.Hub, ([H.hubLabel h] : Multiset R) := by
  rw [d.trace.hub_relations]
  exact Fintype.sum_sum_type _

theorem hub_card : Fintype.card d.graph.Hub = Fintype.card G.Hub + Fintype.card H.Hub :=
  d.trace.hub_card.trans (G.comp_hub_card H)

theorem sign : d.graph.sign = G.sign + H.sign := d.trace.sign.trans (G.sign_comp H)

@[reducible] noncomputable def leftCircuit (C : G.SimpleCircuit) (hc : C.IsLabelCover) :
    d.graph.SimpleCircuit :=
  (C.compLeft G H).reducedCover (C.isLabelCover_compLeft G H hc) d.trace

@[reducible] noncomputable def rightCircuit (C : H.SimpleCircuit) (hc : C.IsLabelCover) :
    d.graph.SimpleCircuit :=
  (C.compRight G H).reducedCover (C.isLabelCover_compRight G H hc) d.trace

theorem leftCircuit_port (C : G.SimpleCircuit) (hc : C.IsLabelCover) (x : Fin C.length × Bool) :
    d.trace.portEmbedding ((d.leftCircuit C hc).port x) =
      PortGraph.compLeftEmbedding G H (C.port x) :=
  ((C.compLeft G H).portEmbedding_reducedCover_port _ d.trace x).trans (C.compLeft_port G H x)

theorem rightCircuit_port (C : H.SimpleCircuit) (hc : C.IsLabelCover) (x : Fin C.length × Bool) :
    d.trace.portEmbedding ((d.rightCircuit C hc).port x) =
      PortGraph.compRightEmbedding G H (C.port x) :=
  ((C.compRight G H).portEmbedding_reducedCover_port _ d.trace x).trans (C.compRight_port G H x)

theorem leftCircuit_label (C : G.SimpleCircuit) (hc : C.IsLabelCover) (x : Fin C.length × Bool) :
    Port.label d.graph.jointLabel ((d.leftCircuit C hc).port x) = Port.label G.jointLabel (C.port x) := by
  rw [← d.trace.portLabel, d.leftCircuit_port]
  exact PortGraph.compLeftEmbedding_label G H _

theorem rightCircuit_label (C : H.SimpleCircuit) (hc : C.IsLabelCover) (x : Fin C.length × Bool) :
    Port.label d.graph.jointLabel ((d.rightCircuit C hc).port x) = Port.label H.jointLabel (C.port x) := by
  rw [← d.trace.portLabel, d.rightCircuit_port]
  exact PortGraph.compRightEmbedding_label G H _

theorem leftCircuit_isLabelCover (C : G.SimpleCircuit) (hc : C.IsLabelCover) :
    (d.leftCircuit C hc).IsLabelCover := (C.compLeft G H).reducedCover_isLabelCover _ d.trace

theorem rightCircuit_isLabelCover (C : H.SimpleCircuit) (hc : C.IsLabelCover) :
    (d.rightCircuit C hc).IsLabelCover := (C.compRight G H).reducedCover_isLabelCover _ d.trace

theorem leftCircuit_boundsFaceOrbit (C : G.SimpleCircuit) (hc : C.IsLabelCover) (side : Bool)
    (hf : C.BoundsFaceOrbit side) : (d.leftCircuit C hc).BoundsFaceOrbit side :=
  (C.compLeft G H).boundsFaceOrbit_reducedCover _ d.trace side (C.boundsFaceOrbit_compLeft G H side hf)

theorem rightCircuit_boundsFaceOrbit (C : H.SimpleCircuit) (hc : C.IsLabelCover) (side : Bool)
    (hf : C.BoundsFaceOrbit side) : (d.rightCircuit C hc).BoundsFaceOrbit side :=
  (C.compRight G H).boundsFaceOrbit_reducedCover _ d.trace side (C.boundsFaceOrbit_compRight G H side hf)

variable
  (hnG : ∀ g, 0 < (P.word (G.hubLabel g)).length)
  (hnH : ∀ h, 0 < (P.word (H.hubLabel h)).length)
  (heG : eulerDefect G.pairing.perm G.circuitStep = 0)
  (heH : eulerDefect H.pairing.perm H.circuitStep = 0)
  (hbG : G.BoundaryNoncrossing) (hbH : H.BoundaryNoncrossing)
  (hsG : G.BoundarySeesComponents) (hsH : H.BoundarySeesComponents)

include hnG hnH in
theorem hub_word_nonempty (h : d.graph.Hub) : 0 < (P.word (d.graph.hubLabel h)).length := by
  obtain ⟨g, rfl⟩ := d.trace.hubEquiv.surjective h
  rw [d.trace.hubLabel]
  cases g with
  | inl g => exact hnG g
  | inr h => exact hnH h

include hnG hnH heG heH hbG hbH hsG hsH in
theorem euler : eulerDefect d.graph.pairing.perm d.graph.circuitStep = 0 := by
  have hn : ∀ h : (G.comp H).Hub, 0 < (P.word ((G.comp H).hubLabel h)).length := by
    rintro (g | h)
    · exact hnG g
    · exact hnH h
  rw [d.trace.eulerDefect hn, G.eulerDefect_comp H hsG hsH hbG hbH, heG, heH, add_zero]

include d hnG hnH heG heH hbG hbH hsG hsH in
theorem exists_diagram : ∃ e : Diagram P [] [],
    (e.labels : Multiset R) =
      (∑ g : G.Hub, ([G.hubLabel g] : Multiset R)) +
        (∑ h : H.Hub, ([H.hubLabel h] : Multiset R)) ∧
    e.size = Fintype.card G.Hub + Fintype.card H.Hub ∧ e.sign = G.sign + H.sign := by
  obtain ⟨e, he⟩ := PortGraph.exists_closed_diagram_of_saturated d.graph (d.hub_word_nonempty hnG hnH)
    (d.graph.rotationEuler_saturated_iff.mpr (d.euler hnG hnH heG heH hbG hbH hsG hsH))
  exact ⟨e, he.trans d.hub_relations,
    (d.graph.diagram_size_of_hub_labels he).trans d.hub_card,
    (d.graph.diagram_sign_of_hub_labels he).trans d.sign⟩

end ClosedGluingReduction
end ThomGame.Pictures

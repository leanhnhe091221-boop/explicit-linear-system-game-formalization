module

public import ThomGame.Pictures.DisconnectedBlockFamily
public import ThomGame.Pictures.ConnectedGraphRealization

/-!
# Realizing closed graphs with any number of components

Every closed Euler-saturating port graph whose hub words are nonempty
has a diagram with exactly the same relation multiset. Actual smoothing
first removes subdivision joints; terminal blocks close independently.
This asserts a diagram witness, not a graph isomorphism or a placement of
the original components inside prescribed open boundaries.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open RibbonConnectivity
open scoped BigOperators

variable {R S : Type*} {P : InvolutionPresentation R S} (G : PortGraph P [] [])

theorem exists_closed_diagram_of_saturated_reduced [IsEmpty G.Joint]
    (hn : ∀ h, 0 < (P.word (G.hubLabel h)).length)
    (hEuler : RotationEuler.count G.rotation G.pairing.perm =
      2 * Nat.card (Component G.rotation G.pairing.perm)) :
    ∃ d : Diagram P [] [], (d.labels : Multiset R) =
      ∑ h : G.Hub, ([G.hubLabel h] : Multiset R) := by
  classical
  obtain ⟨d, hd⟩ := (G.closedBlockFamily hn).exists_closed_diagram_of_saturated
    G.pairing.involutive G.pairing.label_twin hEuler
  exact ⟨d, hd.trans (G.closedBlockFamily_relations hn)⟩

theorem exists_closed_diagram_of_saturated
    (hn : ∀ h, 0 < (P.word (G.hubLabel h)).length)
    (hEuler : RotationEuler.count G.rotation G.pairing.perm =
      2 * Nat.card (Component G.rotation G.pairing.perm)) :
    ∃ d : Diagram P [] [], (d.labels : Multiset R) =
      ∑ h : G.Hub, ([G.hubLabel h] : Multiset R) := by
  obtain ⟨H, circles, ⟨t⟩, hJ⟩ := Smoothing.exists_without_junctions G
  let : IsEmpty H.Joint := hJ
  obtain ⟨d, hd⟩ := H.exists_closed_diagram_of_saturated_reduced
    (t.hub_word_nonempty hn) (t.rotationEuler_saturated hn hEuler)
  exact ⟨d, hd.trans t.hub_relations⟩

theorem exists_closed_diagram_of_saturated_preserving
    (hn : ∀ h, 0 < (P.word (G.hubLabel h)).length)
    (hEuler : RotationEuler.count G.rotation G.pairing.perm =
      2 * Nat.card (Component G.rotation G.pairing.perm)) :
    ∃ d : Diagram P [] [],
      (d.labels : Multiset R) = (∑ h : G.Hub, ([G.hubLabel h] : Multiset R)) ∧
      d.size = Fintype.card G.Hub ∧ d.sign = G.sign := by
  obtain ⟨d, hd⟩ := G.exists_closed_diagram_of_saturated hn hEuler
  exact ⟨d, hd, G.diagram_size_of_hub_labels hd, G.diagram_sign_of_hub_labels hd⟩

end ThomGame.Pictures.PortGraph

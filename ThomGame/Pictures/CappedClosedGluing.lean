module

public import ThomGame.Pictures.CappedCompositionEuler
public import ThomGame.Pictures.ClosedGluingCovers

/-! # Smoothing and realizing a closed gluing from its actual capped maps -/

@[expose] public section
namespace ThomGame.Pictures

open RibbonConnectivity RotationEuler
open scoped BigOperators

variable {R S : Type*} {P : InvolutionPresentation R S} {w : List S}

theorem PortGraph.cappedRotation_saturated_of_boundary_invariants (H : PortGraph P w [])
    (hn : ∀ h, 0 < (P.word (H.hubLabel h)).length)
    (he : eulerDefect H.pairing.perm H.circuitStep = 0)
    (hb : H.BoundaryNoncrossing) (hs : H.BoundarySeesComponents) :
    count H.cappedRotation H.pairing.perm =
      2 * Nat.card (Component H.cappedRotation H.pairing.perm) := by
  by_cases hw : 0 < w.length
  · exact H.cappedRotation_saturated_general hw hn he hb hs
  · have hw : w = [] := List.length_eq_zero_iff.mp (by omega)
    subst w
    have hc : H.cappedRotation = H.rotation := by
      ext a
      cases a with
      | top i => exact i.elim0
      | bottom i => exact i.elim0
      | hub h i => exact H.cappingTargets_unmarked (.hub h (H.hubRotation h i)) id
      | joint j b => exact H.cappingTargets_unmarked (.joint j (!b)) id
    rw [hc]
    exact H.rotationEuler_saturated_iff.mpr he

namespace ClosedGluingReduction

variable {G : PortGraph P [] w} {H : PortGraph P w []}
  (d : ClosedGluingReduction G H)
  (hnG : ∀ g, 0 < (P.word (G.hubLabel g)).length)
  (hnH : ∀ h, 0 < (P.word (H.hubLabel h)).length)
  (heG : count G.cappedRotation G.pairing.perm =
    2 * Nat.card (Component G.cappedRotation G.pairing.perm))
  (heH : count H.cappedRotation H.pairing.perm =
    2 * Nat.card (Component H.cappedRotation H.pairing.perm))

include hnG hnH heG heH in
theorem saturated_of_capped :
    count d.graph.rotation d.graph.pairing.perm =
      2 * Nat.card (Component d.graph.rotation d.graph.pairing.perm) := by
  apply d.trace.rotationEuler_saturated _ (G.comp_saturated_of_capped H heG heH)
  rintro (g | h)
  · exact hnG g
  · exact hnH h

include hnG hnH heG heH in
theorem euler_of_capped : eulerDefect d.graph.pairing.perm d.graph.circuitStep = 0 :=
  d.graph.rotationEuler_saturated_iff.mp (d.saturated_of_capped hnG hnH heG heH)

include d hnG hnH heG heH in
theorem exists_diagram_of_capped : ∃ e : Diagram P [] [],
    (e.labels : Multiset R) =
      (∑ g : G.Hub, ([G.hubLabel g] : Multiset R)) +
        (∑ h : H.Hub, ([H.hubLabel h] : Multiset R)) ∧
      e.size = Fintype.card G.Hub + Fintype.card H.Hub ∧ e.sign = G.sign + H.sign := by
  obtain ⟨e, he⟩ := d.graph.exists_closed_diagram_of_saturated
    (d.hub_word_nonempty hnG hnH) (d.saturated_of_capped hnG hnH heG heH)
  exact ⟨e, he.trans d.hub_relations,
    (d.graph.diagram_size_of_hub_labels he).trans d.hub_card,
    (d.graph.diagram_sign_of_hub_labels he).trans d.sign⟩

end ClosedGluingReduction
end ThomGame.Pictures

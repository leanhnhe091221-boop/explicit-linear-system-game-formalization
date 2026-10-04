module

public import ThomGame.Pictures.SunCancellationBottom
public import ThomGame.Pictures.SunSwitchQuadrilateral

/-!
# Minimal sun graphs stable under actual switches and smoothing

These are proved invariants of the actual graph on which surgery acts.
The minimum-size condition compares its hub count with genuine diagrams
having the specified boundary; it follows from character minimality of
the starting diagram. The boundary and Euler invariants guarantee a
diagram with the exact hub-label multiset at every stage.

An opposite-orientation spoke gives a smaller genuine diagram and is
therefore impossible. The resulting equal orientation justifies the
next switch, without requiring graph isomorphism of a diagram witness.
-/

@[expose] public section
namespace ThomGame.Pictures

open RibbonConnectivity
open scoped BigOperators

variable {n : Nat} {b : Fin n → ZMod 2} {w : List (Fin n ⊕ Fin n)}

namespace PortGraph

structure SunMinimalState (G : PortGraph (sunPresentation n b) [] w) : Prop where
  euler : eulerDefect G.pairing.perm G.circuitStep = 0
  noncrossing : G.BoundaryNoncrossing
  sees : G.BoundarySeesComponents
  minimal : ∀ d : Diagram (sunPresentation n b) [] w, Fintype.card G.Hub ≤ d.size

namespace SunMinimalState

variable {G : PortGraph (sunPresentation n b) [] w} (h : G.SunMinimalState)

include h

theorem exists_minimal_diagram :
    ∃ d : Diagram (sunPresentation n b) [] w,
      (d.labels : Multiset (Fin n)) = (∑ x : G.Hub, ([G.hubLabel x] : Multiset (Fin n))) ∧
      d.size = Fintype.card G.Hub ∧ d.sign = G.sign ∧ d.Minimal ∧ d.CharacterMinimal := by
  obtain ⟨d, hd, hn, hs⟩ := G.exists_diagram_of_bottom_invariants_preserving
    (fun _ => by change 0 < 3; decide +kernel) h.euler h.noncrossing h.sees
  have hm : d.Minimal := by
    intro e _
    rw [hn]
    exact h.minimal e
  exact ⟨d, hd, hn, hs, hm, hm.characterMinimal⟩

theorem same_flip (s : G.SunSpoke) : G.hubFlip s.left = G.hubFlip s.right := by
  by_contra hf
  by_cases hw : 0 < w.length
  · obtain ⟨d, hd, _, _⟩ := s.exists_cancelled_bottom_diagram hw hf h.euler h.noncrossing h.sees
    have hm := h.minimal d
    omega
  · have hw0 : w = [] := List.length_eq_zero_iff.mp (by omega)
    subst w
    have hm := h.minimal (.identity [])
    have hp : 0 < Fintype.card G.Hub := Fintype.card_pos_iff.mpr ⟨s.left⟩
    change Fintype.card G.Hub ≤ 0 at hm
    omega

theorem switch (s : G.SunSpoke) : s.switch.SunMinimalState where
  euler := s.switch.rotationEuler_saturated_iff.mp
    (s.switch_saturated (h.same_flip s) (G.rotationEuler_saturated_iff.mpr h.euler))
  noncrossing := s.switch_boundaryNoncrossing (h.same_flip s) h.noncrossing
  sees := s.switch_boundarySeesComponents (h.same_flip s) h.sees
  minimal := h.minimal

theorem smoothing {H : PortGraph (sunPresentation n b) [] w} {cs : List (Fin n ⊕ Fin n)}
    (t : Smoothing G H cs) : H.SunMinimalState where
  euler := (t.eulerDefect (fun _ => by change 0 < 3; decide +kernel)).trans h.euler
  noncrossing := t.boundaryNoncrossing_iff.mpr h.noncrossing
  sees := t.boundarySeesComponents_iff.mpr h.sees
  minimal := by intro d; rw [t.hub_card]; exact h.minimal d

end SunMinimalState
end PortGraph

namespace Smoothing

variable {d : Diagram (sunPresentation n b) [] w} {G : PortGraph (sunPresentation n b) [] w}
  {cs : List (Fin n ⊕ Fin n)} (t : Smoothing d.graph G cs)

include t in
theorem sunMinimalState (hm : d.CharacterMinimal) : G.SunMinimalState where
  euler := t.diagram_eulerDefect (fun _ => by change 0 < 3; decide +kernel)
  noncrossing := t.boundaryNoncrossing_iff.mpr d.graph_boundaryNoncrossing
  sees := t.diagram_boundarySeesComponents
  minimal := by
    intro e
    rw [t.hub_card, d.graph_hub_card]
    exact (d.sun_characterMinimal_iff.mp hm) e

end Smoothing
end ThomGame.Pictures

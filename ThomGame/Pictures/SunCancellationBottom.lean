module

public import ThomGame.Pictures.SunCancellationMinimal
public import ThomGame.Pictures.BottomGraphRealization

/-!
# The cancellation contradiction for lower-boundary sun diagrams

The actual wheel germs produce lower-boundary diagrams. Reindexing that
boundary into its reversed top word preserves the graph rotations.
After cancellation and realization, boundary bending and reflection
restore the original lower word, without changing the relation count.
-/

@[expose] public section
namespace ThomGame.Pictures

open RibbonConnectivity

variable {n : Nat} {b : Fin n → ZMod 2} {w : List (Fin n ⊕ Fin n)}

namespace PortGraph.SunSpoke

variable {G : PortGraph (sunPresentation n b) [] w} (s : G.SunSpoke)

def bottomTopSpoke : G.bottomTopGraph.SunSpoke where
  left := s.left
  right := s.right
  paired := (G.bottomTop_pairing (.hub s.left (0 : Fin 3))).trans
    (congrArg G.bottomTopPorts s.paired)

theorem exists_cancelled_bottom_diagram (hw : 0 < w.length)
    (hf : G.hubFlip s.left ≠ G.hubFlip s.right)
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
    (hnc : G.BoundaryNoncrossing) (hsees : G.BoundarySeesComponents) :
    ∃ d : Diagram (sunPresentation n b) [] w,
      d.size + 2 = Fintype.card G.Hub ∧ d.sign = G.sign ∧
      (∀ j, d.character j = G.character j) := by
  obtain ⟨e, he, _, _⟩ := s.bottomTopSpoke.exists_cancelled_diagram
    (by simpa only [List.length_reverse] using hw) hf (G.bottomTop_eulerDefect.trans hEuler)
    (G.bottomTop_boundaryNoncrossing hnc) (G.bottomTop_boundarySeesComponents hsees)
  have hc : ∀ j, e.fromReversedTop.character j = G.character j := by
    intro j
    rw [e.fromReversedTop.sun_character, G.sun_character]
  refine ⟨e.fromReversedTop, ?_, ?_, hc⟩
  · rw [e.size_fromReversedTop]
    exact he
  · rw [e.fromReversedTop.sign_eq_character, G.sign_eq_character]
    simp only [hc]

end PortGraph.SunSpoke

namespace Smoothing

variable {d : Diagram (sunPresentation n b) [] w} {G : PortGraph (sunPresentation n b) [] w}
  {circles : List (Fin n ⊕ Fin n)} (t : Smoothing d.graph G circles)

include t in
theorem characterMinimal_sun_bottom_spoke_same_flip (hmin : d.CharacterMinimal) (s : G.SunSpoke) :
    G.hubFlip s.left = G.hubFlip s.right := by
  by_contra hf
  have hsize : Fintype.card G.Hub = d.size := t.hub_card.trans d.graph_hub_card
  by_cases hw : 0 < w.length
  · obtain ⟨e, he, _, _⟩ := s.exists_cancelled_bottom_diagram hw hf
      (t.diagram_eulerDefect (fun _ => by change 0 < 3; decide +kernel))
      (t.boundaryNoncrossing_iff.mpr d.graph_boundaryNoncrossing) t.diagram_boundarySeesComponents
    have hm := (d.sun_characterMinimal_iff.mp hmin) e
    omega
  · have hw0 : w = [] := List.length_eq_zero_iff.mp (by omega)
    subst w
    have hd0 := d.closed_sun_characterMinimal_size_zero hmin
    have hp : 0 < Fintype.card G.Hub := Fintype.card_pos_iff.mpr ⟨s.left⟩
    omega

include t in
theorem minimal_sun_bottom_spoke_same_flip (hmin : d.Minimal) (s : G.SunSpoke) :
    G.hubFlip s.left = G.hubFlip s.right :=
  t.characterMinimal_sun_bottom_spoke_same_flip hmin.characterMinimal s

end Smoothing

namespace Diagram

theorem characterMinimal_sun_bottom_spoke_same_flip (d : Diagram (sunPresentation n b) [] w)
    (hmin : d.CharacterMinimal) (s : d.graph.SunSpoke) :
    d.graph.hubFlip s.left = d.graph.hubFlip s.right :=
  (Smoothing.refl d.graph).characterMinimal_sun_bottom_spoke_same_flip hmin s

end Diagram
end ThomGame.Pictures

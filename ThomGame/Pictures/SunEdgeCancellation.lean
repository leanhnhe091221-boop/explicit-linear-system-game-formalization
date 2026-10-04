module

public import ThomGame.Pictures.SunTriangleBlocks
public import ThomGame.Pictures.DistinguishedCancellation
public import ThomGame.Pictures.SunCancellationBottom
public import ThomGame.Pictures.SunMinimalState

/-!
# Cancelling equally labelled opposite sun hubs along any slot

The edge may be a spoke or either rim port. A genuine capped block
family is contracted along that edge, its merged triangle block is
filled by caps, and the unique boundary block is punctured. The result
has the same prescribed boundary and exactly two fewer relation vertices.
No connectedness or circle-placement premise is used for this minimum-
size contradiction.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity
open scoped Classical BigOperators

variable {n : Nat} {b : Fin n → ZMod 2} {w : List (Fin n ⊕ Fin n)}

theorem exists_sun_edge_cancelled_top {G : PortGraph (sunPresentation n b) w []}
    (hw : 0 < w.length) (h k : G.Hub) (i : Fin 3)
    (he : G.pairing.twin (.hub h i) = .hub k i)
    (hl : G.hubLabel h = G.hubLabel k) (hf : G.hubFlip h ≠ G.hubFlip k)
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
    (hnc : G.BoundaryNoncrossing) (hsees : G.BoundarySeesComponents) :
    ∃ d : Diagram (sunPresentation n b) w [],
      (d.labels : Multiset (Fin n)) + [G.hubLabel h, G.hubLabel h] =
        (∑ j : G.Hub, ([G.hubLabel j] : Multiset (Fin n))) ∧
      d.size + 2 = Fintype.card G.Hub ∧ d.sign = G.sign := by
  have hn (j : G.Hub) : 0 < ((sunPresentation n b).word (G.hubLabel j)).length := by
    change 0 < 3
    decide +kernel
  have hne : h ≠ k := by
    intro hh
    subst k
    exact G.pairing.ne_self (.hub h i) he
  have hsep : ¬ G.cappedRotation.SameCycle (.hub h i) (G.pairing.twin (.hub h i)) := by
    intro hc
    rw [he] at hc
    have hv := (G.rotation_sameCycle_iff _ _).mp ((G.cappedRotation_sameCycle_hub_iff h i _).mp hc)
    exact hne (Sum.inl.inj (Sum.inr.inj hv))
  obtain ⟨B, ha, hb⟩ := G.exists_sun_triangle_cancel_block
    ((sunPresentation n b).adjoinRelation w 0) G.cappedRotation
    (fun j i => G.cappedRotation_hub j i) h k i he hl hf hsep
  let F := G.cappedAllBlockFamily hw hn
  obtain ⟨d, hd⟩ := F.exists_closed_diagram_cancel_merge G.pairing.involutive G.pairing.label_twin
    (G.cappedRotation_saturated_general hw hn hEuler hnc hsees) (.hub h i) hsep B ha hb
  have hL : (F.block (F.owner (.hub h i))).diagram.labels = [some (G.hubLabel h)] :=
    G.cappedHubBlock_labels h (hn h)
  have hR : (F.block (F.owner (G.pairing.twin (.hub h i)))).diagram.labels = [some (G.hubLabel k)] := by
    rw [he]
    exact G.cappedHubBlock_labels k (hn k)
  have hLR := congrArg₂ (fun x y : List (Option (Fin n)) =>
    (d.labels : Multiset (Option (Fin n))) + (x : Multiset _) + (y : Multiset _)) hL hR
  have hd' := hLR.symm.trans hd
  rw [← hl, add_assoc] at hd'
  have hrel := hd'.trans (G.cappedAllBlockFamily_relations hw hn)
  obtain ⟨e, he⟩ := d.exists_punctured_after_cancel
    (∑ j : G.Hub, ([G.hubLabel j] : Multiset (Fin n))) (G.hubLabel h) hrel
  refine ⟨e, he, ?_, ?_⟩
  · have hc := congrArg Multiset.card he
    simpa [Diagram.size] using hc
  · rw [e.sign_eq_character, G.sign_eq_character]
    simp_rw [e.sun_character, G.sun_character]

theorem exists_sun_edge_cancelled_bottom {G : PortGraph (sunPresentation n b) [] w}
    (hw : 0 < w.length) (h k : G.Hub) (i : Fin 3)
    (he : G.pairing.twin (.hub h i) = .hub k i)
    (hl : G.hubLabel h = G.hubLabel k) (hf : G.hubFlip h ≠ G.hubFlip k)
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
    (hnc : G.BoundaryNoncrossing) (hsees : G.BoundarySeesComponents) :
    ∃ d : Diagram (sunPresentation n b) [] w,
      (d.labels : Multiset (Fin n)) + [G.hubLabel h, G.hubLabel h] =
        (∑ j : G.Hub, ([G.hubLabel j] : Multiset (Fin n))) ∧
      d.size + 2 = Fintype.card G.Hub ∧ d.sign = G.sign := by
  have he' : G.bottomTopGraph.pairing.twin (.hub h i) = .hub k i :=
    (G.bottomTop_pairing (.hub h i)).trans (congrArg G.bottomTopPorts he)
  obtain ⟨e, he, hc, _⟩ := exists_sun_edge_cancelled_top
    (by simpa only [List.length_reverse] using hw) h k i he' hl hf
    (G.bottomTop_eulerDefect.trans hEuler) (G.bottomTop_boundaryNoncrossing hnc)
    (G.bottomTop_boundarySeesComponents hsees)
  refine ⟨e.fromReversedTop, ?_, ?_, ?_⟩
  · rw [Multiset.coe_eq_coe.mpr e.labels_fromReversedTop_perm]
    exact he
  · rw [e.size_fromReversedTop]
    exact hc
  · rw [e.fromReversedTop.sign_eq_character, G.sign_eq_character]
    simp_rw [e.fromReversedTop.sun_character, G.sun_character]

namespace SunMinimalState

theorem same_flip_of_same_label_edge {G : PortGraph (sunPresentation n b) [] w}
    (H : G.SunMinimalState) (h k : G.Hub) (i : Fin 3)
    (he : G.pairing.twin (.hub h i) = .hub k i) (hl : G.hubLabel h = G.hubLabel k) :
    G.hubFlip h = G.hubFlip k := by
  by_contra hf
  by_cases hw : 0 < w.length
  · obtain ⟨d, _, hc, _⟩ := exists_sun_edge_cancelled_bottom hw h k i he hl hf H.euler H.noncrossing H.sees
    have hm := H.minimal d
    omega
  · have hw0 : w = [] := List.length_eq_zero_iff.mp (by omega)
    subst w
    have hm := H.minimal (.identity [])
    have hp : 0 < Fintype.card G.Hub := Fintype.card_pos_iff.mpr ⟨h⟩
    change Fintype.card G.Hub ≤ 0 at hm
    omega

end SunMinimalState
end ThomGame.Pictures.PortGraph

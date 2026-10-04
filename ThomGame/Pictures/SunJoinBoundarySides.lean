module

public import ThomGame.Pictures.SunBoundarySides
public import ThomGame.Pictures.SunSwitchInvolution

/-!
# Boundary sides when two distinct sun rims join

The inverse split identifies the new spoke side with the two old
opposite-spoke sides. If the selected spoke points away from the boundary
of the left rim, an actual boundary witness lies on the spoke side of
both the old right rim and the new joined rim. Thus the boundary determines
the sides used in the join formula without assuming a nesting diagram.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SunSpoke

open Equiv RibbonConnectivity
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} (s : G.SunSpoke) (hn : 3 ≤ n)
  (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)
  (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
  (hf : G.hubFlip s.left = G.hubFlip s.right)
  (hc : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
    (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true))

private theorem twice_left_side (x : G.Dart) :
    (s.switchedSpoke.switchedSpoke.leftRim hn hu hv).OnSide
        (s.switchedSpoke.switch.hubFlip s.left) x ↔
      (s.leftRim hn hu hv).OnSide (G.hubFlip s.left) x := by
  exact (s.switch_twice_onSide hn hu hv (G.sunRimPort hn s.left true)
    (s.switchedSpoke.switch.hubFlip s.left) x).trans (by rw [s.switch_twice_flip]; rfl)

private theorem twice_right_side (x : G.Dart) :
    (s.switchedSpoke.switchedSpoke.rightRim hn hu hv).OnSide
        (s.switchedSpoke.switch.hubFlip s.right) x ↔
      (s.rightRim hn hu hv).OnSide (G.hubFlip s.right) x := by
  exact (s.switch_twice_onSide hn hu hv (G.sunRimPort hn s.right true)
    (s.switchedSpoke.switch.hubFlip s.right) x).trans (by rw [s.switch_twice_flip]; rfl)

include hEuler hf hc in
theorem join_spoke_side_union (x : Subtype s.Kept) :
    (s.switchedSpoke.leftRim hn hu hv).OnSide (!s.switch.hubFlip s.left) x.val ↔
      (s.leftRim hn hu hv).OnSide (G.hubFlip s.left) (s.portSwap x.val) ∨
      (s.rightRim hn hu hv).OnSide (G.hubFlip s.right) (s.portSwap x.val) := by
  have he := s.switch.rotationEuler_saturated_iff.mp
    (s.switch_saturated hf (G.rotationEuler_saturated_iff.mpr hEuler))
  have hflip : s.switch.hubFlip s.left = s.switch.hubFlip s.right := by
    rw [s.switch_flip_left, s.switch_flip_right, hf]
  exact (s.switchedSpoke.split_opposite_sides_union hn hu hv he hflip
    (s.switch_rim_joins hn hu hv hc) x).trans
      (or_congr (s.twice_left_side hn hu hv (s.portSwap x.val))
        (s.twice_right_side hn hu hv (s.portSwap x.val)))

include hEuler hf hc in
theorem join_old_opposite_sides_disjoint (x : Subtype s.Kept) :
    ¬ ((s.leftRim hn hu hv).OnSide (G.hubFlip s.left) (s.portSwap x.val) ∧
      (s.rightRim hn hu hv).OnSide (G.hubFlip s.right) (s.portSwap x.val)) := by
  have he := s.switch.rotationEuler_saturated_iff.mp
    (s.switch_saturated hf (G.rotationEuler_saturated_iff.mpr hEuler))
  have hflip : s.switch.hubFlip s.left = s.switch.hubFlip s.right := by
    rw [s.switch_flip_left, s.switch_flip_right, hf]
  intro hx
  exact s.switchedSpoke.split_opposite_sides_disjoint hn hu hv he hflip
    (s.switch_rim_joins hn hu hv hc) x
    ⟨(s.twice_left_side hn hu hv (s.portSwap x.val)).mpr hx.1,
      (s.twice_right_side hn hu hv (s.portSwap x.val)).mpr hx.2⟩

include hEuler hf hc in
theorem join_boundary_side_witnesses
    (hOuter : (s.leftRim hn hu hv).HasBoundarySide (G.hubFlip s.left)) :
    (s.rightRim hn hu hv).HasBoundarySide (!G.hubFlip s.right) ∧
      (s.switchedSpoke.leftRim hn hu hv).HasBoundarySide (!s.switch.hubFlip s.left) := by
  obtain ⟨x, hx, hs⟩ := hOuter
  have hdis := s.join_old_opposite_sides_disjoint hn hu hv hEuler hf hc ⟨x, s.boundary_kept hx⟩
  have hunion := s.join_spoke_side_union hn hu hv hEuler hf hc ⟨x, s.boundary_kept hx⟩
  change ¬ ((s.leftRim hn hu hv).OnSide (G.hubFlip s.left) (s.portSwap x) ∧
    (s.rightRim hn hu hv).OnSide (G.hubFlip s.right) (s.portSwap x)) at hdis
  change (s.switchedSpoke.leftRim hn hu hv).OnSide (!s.switch.hubFlip s.left) x ↔
    (s.leftRim hn hu hv).OnSide (G.hubFlip s.left) (s.portSwap x) ∨
    (s.rightRim hn hu hv).OnSide (G.hubFlip s.right) (s.portSwap x) at hunion
  rw [s.portSwap_boundary hx] at hdis hunion
  have hcomponent := ((s.leftRim hn hu hv).onSide_union_iff_connected (G.hubFlip s.left) x).mp
    (Or.inl hs)
  have hright : Connected G.circuitStep G.pairing.perm x (s.rightRim hn hu hv).cutBase :=
    hcomponent.trans (s.rim_ports_dual_connected (2 : Fin 3) (2 : Fin 3))
  refine ⟨⟨x, hx, ?_⟩, x, (s.switch_isBoundary_iff x).mpr hx, hunion.mpr (Or.inl hs)⟩
  rcases ((s.rightRim hn hu hv).onSide_union_iff_connected (G.hubFlip s.right) x).mpr hright with h | h
  · exact (hdis ⟨hs, h⟩).elim
  · exact h

include hEuler hf hc in
theorem join_boundarySide_values (hsees : G.BoundarySeesComponents)
    (hOuter : (s.leftRim hn hu hv).HasBoundarySide (G.hubFlip s.left))
    (hR : (s.rightRim hn hu hv).MeetsBoundary)
    (hNew : (s.switchedSpoke.leftRim hn hu hv).MeetsBoundary) :
    (s.rightRim hn hu hv).boundarySide hR = (!G.hubFlip s.right) ∧
      (s.switchedSpoke.leftRim hn hu hv).boundarySide hNew = (!s.switch.hubFlip s.left) := by
  have hs := s.join_boundary_side_witnesses hn hu hv hEuler hf hc hOuter
  exact ⟨(s.rightRim hn hu hv).boundarySide_eq_of_witness
      (G.dualEuler_eq_twice_components hEuler) hsees hR hs.1,
    (s.switchedSpoke.leftRim hn hu hv).boundarySide_eq_of_witness
      (s.switch_dualEuler hEuler hf) (s.switch_boundarySeesComponents hf hsees) hNew hs.2⟩

end ThomGame.Pictures.PortGraph.SunSpoke

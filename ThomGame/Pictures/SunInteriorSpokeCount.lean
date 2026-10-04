module

public import ThomGame.Pictures.SunJoinBoundarySides
public import ThomGame.Pictures.SunJoinSpokeCount

/-!
# Spoke counts on the side opposite the actual boundary

For a rim whose ambient component reaches the boundary, count actual
spoke edges on the other side. The split and join formulas now use these
boundary-determined counts. They do not count edges of other ambient
components or circles recorded by smoothing, so no global NE theorem
is asserted here.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  (G : PortGraph (sunPresentation n b) u v) (hn : 3 ≤ n)
  (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)

noncomputable def sunInteriorSpokeCount (a : G.SunRimDart hn)
    (h : (G.sunRimSimpleCircuit hn hu hv a).MeetsBoundary) : Nat :=
  G.sunSideSpokeCount hn hu hv a (!(G.sunRimSimpleCircuit hn hu hv a).boundarySide h)

theorem sunInteriorSpokeCount_eq_of_boundarySide (a : G.SunRimDart hn)
    (h : (G.sunRimSimpleCircuit hn hu hv a).MeetsBoundary) {side : Bool}
    (hs : (G.sunRimSimpleCircuit hn hu hv a).boundarySide h = side) :
    G.sunInteriorSpokeCount hn hu hv a h = G.sunSideSpokeCount hn hu hv a (!side) := by
  unfold sunInteriorSpokeCount
  rw [hs]

theorem sunInteriorSpokeCount_eq_of_opposite_boundarySide (a : G.SunRimDart hn)
    (h : (G.sunRimSimpleCircuit hn hu hv a).MeetsBoundary) {side : Bool}
    (hs : (G.sunRimSimpleCircuit hn hu hv a).boundarySide h = (!side)) :
    G.sunInteriorSpokeCount hn hu hv a h = G.sunSideSpokeCount hn hu hv a side :=
  (G.sunInteriorSpokeCount_eq_of_boundarySide hn hu hv a h hs).trans
    (congrArg (G.sunSideSpokeCount hn hu hv a) (Bool.not_not side))

namespace SunSpoke

variable {G} (s : G.SunSpoke)
  (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
  (hf : G.hubFlip s.left = G.hubFlip s.right) (hsees : G.BoundarySeesComponents)

include hEuler in
theorem boundarySide_eq_of_interior_spoke (h : (s.leftRim hn hu hv).MeetsBoundary)
    (hi : (s.leftRim hn hu hv).OnSide (!(s.leftRim hn hu hv).boundarySide h)
      (.hub s.left (0 : Fin 3))) :
    (s.leftRim hn hu hv).boundarySide h = G.hubFlip s.left := by
  have he := (s.leftRim hn hu hv).onSide_unique (G.dualEuler_eq_twice_components hEuler)
    hi (s.leftRim_spoke_onSide_left hn hu hv)
  simpa only [Bool.not_not] using congrArg Bool.not he

include hEuler hf hsees in
theorem switch_interior_spoke_count_away (a : G.SunRimDart hn)
    (ha : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      a (G.sunRimPort hn s.left true))
    (hb : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      a (G.sunRimPort hn s.right true))
    (hOld : (G.sunRimSimpleCircuit hn hu hv a).MeetsBoundary)
    (hNew : (s.switch.sunRimSimpleCircuit hn hu hv a).MeetsBoundary) :
    s.switch.sunInteriorSpokeCount hn hu hv a hNew = G.sunInteriorSpokeCount hn hu hv a hOld := by
  unfold sunInteriorSpokeCount
  rw [s.switch_rim_boundarySide_away hn hu hv hEuler hf hsees a ha hb hOld hNew]
  exact s.switch_rim_spoke_count_away hn hu hv a ha hb hf _

include hEuler hf hsees in
theorem split_interior_spoke_count
    (hc : Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true))
    (hOld : (s.leftRim hn hu hv).MeetsBoundary)
    (hi : (s.leftRim hn hu hv).OnSide (!(s.leftRim hn hu hv).boundarySide hOld)
      (.hub s.left (0 : Fin 3)))
    (hL : (s.switchedSpoke.leftRim hn hu hv).MeetsBoundary)
    (hR : (s.switchedSpoke.rightRim hn hu hv).MeetsBoundary) :
    G.sunInteriorSpokeCount hn hu hv (G.sunRimPort hn s.left true) hOld =
      s.switch.sunInteriorSpokeCount hn hu hv (G.sunRimPort hn s.left true) hL +
      s.switch.sunInteriorSpokeCount hn hu hv (G.sunRimPort hn s.right true) hR + 1 := by
  have hold := s.boundarySide_eq_of_interior_spoke hn hu hv hEuler hOld hi
  have hout : (s.leftRim hn hu hv).HasBoundarySide (G.hubFlip s.left) :=
    hold ▸ (s.leftRim hn hu hv).boundarySide_spec hOld
  have hnew := s.split_boundarySide_values hn hu hv hEuler hf hsees hc hout hL hR
  have ho := G.sunInteriorSpokeCount_eq_of_boundarySide hn hu hv
    (G.sunRimPort hn s.left true) hOld hold
  have hl := s.switch.sunInteriorSpokeCount_eq_of_opposite_boundarySide hn hu hv
    (G.sunRimPort hn s.left true) hL hnew.1
  have hr := s.switch.sunInteriorSpokeCount_eq_of_opposite_boundarySide hn hu hv
    (G.sunRimPort hn s.right true) hR hnew.2
  exact ho.trans ((s.split_spoke_count hn hu hv hEuler hf hc).trans
    (congrArg₂ (fun l r => l + r + 1) hl hr).symm)

include hEuler hf hsees in
theorem split_interior_spoke_count_lt
    (hc : Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true))
    (hOld : (s.leftRim hn hu hv).MeetsBoundary)
    (hi : (s.leftRim hn hu hv).OnSide (!(s.leftRim hn hu hv).boundarySide hOld)
      (.hub s.left (0 : Fin 3)))
    (hL : (s.switchedSpoke.leftRim hn hu hv).MeetsBoundary)
    (hR : (s.switchedSpoke.rightRim hn hu hv).MeetsBoundary) :
    s.switch.sunInteriorSpokeCount hn hu hv (G.sunRimPort hn s.left true) hL +
      s.switch.sunInteriorSpokeCount hn hu hv (G.sunRimPort hn s.right true) hR <
      G.sunInteriorSpokeCount hn hu hv (G.sunRimPort hn s.left true) hOld := by
  rw [s.split_interior_spoke_count hn hu hv hEuler hf hsees hc hOld hi hL hR]
  omega

include hEuler hf hsees in
theorem join_interior_spoke_count_add
    (hc : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true))
    (hOld : (s.leftRim hn hu hv).MeetsBoundary)
    (hi : (s.leftRim hn hu hv).OnSide (!(s.leftRim hn hu hv).boundarySide hOld)
      (.hub s.left (0 : Fin 3)))
    (hR : (s.rightRim hn hu hv).MeetsBoundary)
    (hNew : (s.switchedSpoke.leftRim hn hu hv).MeetsBoundary) :
    G.sunInteriorSpokeCount hn hu hv (G.sunRimPort hn s.left true) hOld =
      s.switch.sunInteriorSpokeCount hn hu hv (G.sunRimPort hn s.left true) hNew +
      G.sunInteriorSpokeCount hn hu hv (G.sunRimPort hn s.right true) hR + 1 := by
  have hold := s.boundarySide_eq_of_interior_spoke hn hu hv hEuler hOld hi
  have hout : (s.leftRim hn hu hv).HasBoundarySide (G.hubFlip s.left) :=
    hold ▸ (s.leftRim hn hu hv).boundarySide_spec hOld
  have hnew := s.join_boundarySide_values hn hu hv hEuler hf hc hsees hout hR hNew
  have ho := G.sunInteriorSpokeCount_eq_of_boundarySide hn hu hv
    (G.sunRimPort hn s.left true) hOld hold
  have hl := s.switch.sunInteriorSpokeCount_eq_of_opposite_boundarySide hn hu hv
    (G.sunRimPort hn s.left true) hNew hnew.2
  have hr := G.sunInteriorSpokeCount_eq_of_opposite_boundarySide hn hu hv
    (G.sunRimPort hn s.right true) hR hnew.1
  exact ho.trans ((s.join_spoke_count_add hn hu hv hEuler hf hc).trans
    (congrArg₂ (fun l r => l + r + 1) hl hr).symm)

include hEuler hf hsees in
theorem join_interior_spoke_count
    (hc : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true))
    (hOld : (s.leftRim hn hu hv).MeetsBoundary)
    (hi : (s.leftRim hn hu hv).OnSide (!(s.leftRim hn hu hv).boundarySide hOld)
      (.hub s.left (0 : Fin 3)))
    (hR : (s.rightRim hn hu hv).MeetsBoundary)
    (hNew : (s.switchedSpoke.leftRim hn hu hv).MeetsBoundary) :
    s.switch.sunInteriorSpokeCount hn hu hv (G.sunRimPort hn s.left true) hNew =
      G.sunInteriorSpokeCount hn hu hv (G.sunRimPort hn s.left true) hOld -
      G.sunInteriorSpokeCount hn hu hv (G.sunRimPort hn s.right true) hR - 1 := by
  have h := s.join_interior_spoke_count_add hn hu hv hEuler hf hsees hc hOld hi hR hNew
  omega

include hEuler hf hsees in
theorem join_interior_spoke_count_lt
    (hc : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true))
    (hOld : (s.leftRim hn hu hv).MeetsBoundary)
    (hi : (s.leftRim hn hu hv).OnSide (!(s.leftRim hn hu hv).boundarySide hOld)
      (.hub s.left (0 : Fin 3)))
    (hR : (s.rightRim hn hu hv).MeetsBoundary)
    (hNew : (s.switchedSpoke.leftRim hn hu hv).MeetsBoundary) :
    s.switch.sunInteriorSpokeCount hn hu hv (G.sunRimPort hn s.left true) hNew <
      G.sunInteriorSpokeCount hn hu hv (G.sunRimPort hn s.left true) hOld +
      G.sunInteriorSpokeCount hn hu hv (G.sunRimPort hn s.right true) hR := by
  have h := s.join_interior_spoke_count_add hn hu hv hEuler hf hsees hc hOld hi hR hNew
  omega

end SunSpoke
end ThomGame.Pictures.PortGraph

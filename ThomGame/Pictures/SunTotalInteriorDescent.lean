module

public import ThomGame.Pictures.SunUnselectedInteriorSum

/-!
# Strict descent of the sum over all actual rim components

Each rim contributes the number of spoke edges in its boundary-opposite
region within its own ambient component. The sum is independent of roots
and orientations. Switching a spoke in the selected rim's interior lowers
this sum: by one for a split, and by twice the old right contribution plus
one for a join. Circles recorded by smoothing and the placement of other
ambient components are separate from this port-graph measure.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SunSpoke

open Equiv RibbonConnectivity
open scoped Classical BigOperators

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} (s : G.SunSpoke) (hn : 3 ≤ n)
  (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)
  (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
  (hf : G.hubFlip s.left = G.hubFlip s.right) (hsees : G.BoundarySeesComponents)
  (hNewEuler : eulerDefect s.switch.pairing.perm s.switch.circuitStep = 0)
  (hNewSees : s.switch.BoundarySeesComponents)
  (hb : ∀ a : G.SunRimDart hn, (G.sunRimSimpleCircuit hn hu hv a).MeetsBoundary)
  (hbNew : ∀ a : s.switch.SunRimDart hn, (s.switch.sunRimSimpleCircuit hn hu hv a).MeetsBoundary)

include hf in
theorem split_total_interior_spoke_count
    (hc : Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true))
    (hi : (s.leftRim hn hu hv).OnSide
      (!(s.leftRim hn hu hv).boundarySide (hb (G.sunRimPort hn s.left true)))
      (.hub s.left (0 : Fin 3))) :
    G.sunTotalInteriorSpokeCount hn hu hv hEuler hsees hb =
      s.switch.sunTotalInteriorSpokeCount hn hu hv hNewEuler hNewSees hbNew + 1 := by
  have hs := (component_eq_iff _ _ _ _).mpr hc
  have hd := mt (component_eq_iff _ _ _ _).mp (s.switch_rim_separates hn hu hv hEuler hf hc)
  have hold := Finite.sum_except_two_of_eq (G.sunRimInteriorCount hn hu hv hEuler hsees hb)
    (component (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm (G.sunRimPort hn s.left true))
    (component (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm (G.sunRimPort hn s.right true)) hs
  have hnew := Finite.sum_except_two_of_ne (s.switch.sunRimInteriorCount hn hu hv hNewEuler hNewSees hbNew)
    (component (s.switch.sunRimPairing hn).perm (s.switch.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true))
    (component (s.switch.sunRimPairing hn).perm (s.switch.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.right true)) hd
  change (∑ c : s.UnselectedRimComponent hn hu hv,
      G.sunRimInteriorCount hn hu hv hEuler hsees hb c.val) +
    G.sunInteriorSpokeCount hn hu hv (G.sunRimPort hn s.left true) (hb _) =
      G.sunTotalInteriorSpokeCount hn hu hv hEuler hsees hb at hold
  change (∑ c : s.switchedSpoke.UnselectedRimComponent hn hu hv,
      s.switch.sunRimInteriorCount hn hu hv hNewEuler hNewSees hbNew c.val) +
    s.switch.sunInteriorSpokeCount hn hu hv (G.sunRimPort hn s.left true) (hbNew _) +
    s.switch.sunInteriorSpokeCount hn hu hv (G.sunRimPort hn s.right true) (hbNew _) =
      s.switch.sunTotalInteriorSpokeCount hn hu hv hNewEuler hNewSees hbNew at hnew
  have haway := s.unselected_rim_interior_sum hn hu hv hEuler hf hsees hNewEuler hNewSees hb hbNew
  have hcount := s.split_interior_spoke_count hn hu hv hEuler hf hsees hc (hb _) hi (hbNew _) (hbNew _)
  omega

include hf in
theorem join_total_interior_spoke_count
    (hc : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true))
    (hi : (s.leftRim hn hu hv).OnSide
      (!(s.leftRim hn hu hv).boundarySide (hb (G.sunRimPort hn s.left true)))
      (.hub s.left (0 : Fin 3))) :
    G.sunTotalInteriorSpokeCount hn hu hv hEuler hsees hb =
      s.switch.sunTotalInteriorSpokeCount hn hu hv hNewEuler hNewSees hbNew +
      2 * G.sunInteriorSpokeCount hn hu hv (G.sunRimPort hn s.right true) (hb _) + 1 := by
  have hd := mt (component_eq_iff _ _ _ _).mp hc
  have hs := (component_eq_iff _ _ _ _).mpr (s.switch_rim_joins hn hu hv hc)
  have hold := Finite.sum_except_two_of_ne (G.sunRimInteriorCount hn hu hv hEuler hsees hb)
    (component (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm (G.sunRimPort hn s.left true))
    (component (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm (G.sunRimPort hn s.right true)) hd
  have hnew := Finite.sum_except_two_of_eq (s.switch.sunRimInteriorCount hn hu hv hNewEuler hNewSees hbNew)
    (component (s.switch.sunRimPairing hn).perm (s.switch.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true))
    (component (s.switch.sunRimPairing hn).perm (s.switch.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.right true)) hs
  change (∑ c : s.UnselectedRimComponent hn hu hv,
      G.sunRimInteriorCount hn hu hv hEuler hsees hb c.val) +
    G.sunInteriorSpokeCount hn hu hv (G.sunRimPort hn s.left true) (hb _) +
    G.sunInteriorSpokeCount hn hu hv (G.sunRimPort hn s.right true) (hb _) =
      G.sunTotalInteriorSpokeCount hn hu hv hEuler hsees hb at hold
  change (∑ c : s.switchedSpoke.UnselectedRimComponent hn hu hv,
      s.switch.sunRimInteriorCount hn hu hv hNewEuler hNewSees hbNew c.val) +
    s.switch.sunInteriorSpokeCount hn hu hv (G.sunRimPort hn s.left true) (hbNew _) =
      s.switch.sunTotalInteriorSpokeCount hn hu hv hNewEuler hNewSees hbNew at hnew
  have haway := s.unselected_rim_interior_sum hn hu hv hEuler hf hsees hNewEuler hNewSees hb hbNew
  have hcount := s.join_interior_spoke_count_add hn hu hv hEuler hf hsees hc (hb _) hi (hb _) (hbNew _)
  omega

include hf in
theorem total_interior_spoke_count_lt
    (hi : (s.leftRim hn hu hv).OnSide
      (!(s.leftRim hn hu hv).boundarySide (hb (G.sunRimPort hn s.left true)))
      (.hub s.left (0 : Fin 3))) :
    s.switch.sunTotalInteriorSpokeCount hn hu hv hNewEuler hNewSees hbNew <
      G.sunTotalInteriorSpokeCount hn hu hv hEuler hsees hb := by
  by_cases hc : Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true)
  · have h := s.split_total_interior_spoke_count hn hu hv hEuler hf hsees hNewEuler hNewSees hb hbNew hc hi
    omega
  · have h := s.join_total_interior_spoke_count hn hu hv hEuler hf hsees hNewEuler hNewSees hb hbNew hc hi
    omega

end ThomGame.Pictures.PortGraph.SunSpoke

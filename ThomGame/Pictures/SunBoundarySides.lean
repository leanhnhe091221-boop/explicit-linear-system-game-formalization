module

public import ThomGame.Pictures.CircuitBoundarySide
public import ThomGame.Pictures.SunSplitSpokeCount

/-!
# Boundary sides under a sun switch

Boundary visibility is preserved for every rim base. Unaffected rims
keep their uniquely determined boundary side. If a same-rim spoke lies
opposite the boundary side, the two new rims both have the spoke on
their boundary side. All statements use actual boundary witnesses.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SunSpoke

open Equiv RibbonConnectivity
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} (s : G.SunSpoke) (hn : 3 ≤ n)
  (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)

theorem switch_isBoundary_iff (x : G.Dart) : s.switch.IsBoundary x ↔ G.IsBoundary x := by
  cases x <;> rfl

theorem rim_ports_dual_connected (i j : Fin 3) :
    Connected G.circuitStep G.pairing.perm (.hub s.left i) (.hub s.right j) := by
  have h := (RotationEuler.connected_rotation_iff G.rotation G.pairing.perm G.pairing.involutive
    (.hub s.left i) (.hub s.right j)).mp
      ((RotationEuler.connected_swap_iff _ _ _ _).mp (s.rim_ports_connected i j))
  rw [G.rotation_mul_pairing] at h
  exact (RotationEuler.connected_swap_iff _ _ _ _).mp h

theorem switch_rim_meetsBoundary_iff (a : G.SunRimDart hn) :
    (s.switch.sunRimSimpleCircuit hn hu hv a).MeetsBoundary ↔
      (G.sunRimSimpleCircuit hn hu hv a).MeetsBoundary := by
  constructor
  · rintro ⟨x, hx, hc⟩
    exact ⟨x, (s.switch_isBoundary_iff x).mp hx, (s.switch_dual_connected x a.val).mp hc⟩
  · rintro ⟨x, hx, hc⟩
    exact ⟨x, (s.switch_isBoundary_iff x).mpr hx, (s.switch_dual_connected x a.val).mpr hc⟩

theorem switch_rim_boundarySide_away
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
    (hf : G.hubFlip s.left = G.hubFlip s.right) (hsees : G.BoundarySeesComponents)
    (a : G.SunRimDart hn)
    (ha : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      a (G.sunRimPort hn s.left true))
    (hb : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      a (G.sunRimPort hn s.right true))
    (hOld : (G.sunRimSimpleCircuit hn hu hv a).MeetsBoundary)
    (hNew : (s.switch.sunRimSimpleCircuit hn hu hv a).MeetsBoundary) :
    (s.switch.sunRimSimpleCircuit hn hu hv a).boundarySide hNew =
      (G.sunRimSimpleCircuit hn hu hv a).boundarySide hOld := by
  obtain ⟨x, hx, hs⟩ := (G.sunRimSimpleCircuit hn hu hv a).boundarySide_spec hOld
  exact (s.switch.sunRimSimpleCircuit hn hu hv a).boundarySide_eq_of_witness
    (s.switch_dualEuler hEuler hf) (s.switch_boundarySeesComponents hf hsees) hNew
    ⟨x, (s.switch_isBoundary_iff x).mpr hx,
      (s.switch_rim_onSide_away hn hu hv a ha hb hf _ x).mpr hs⟩

theorem split_boundary_side_witnesses
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
    (hf : G.hubFlip s.left = G.hubFlip s.right)
    (hc : Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true))
    (hOuter : (s.leftRim hn hu hv).HasBoundarySide (G.hubFlip s.left)) :
    (s.switchedSpoke.leftRim hn hu hv).HasBoundarySide (!s.switch.hubFlip s.left) ∧
      (s.switchedSpoke.rightRim hn hu hv).HasBoundarySide (!s.switch.hubFlip s.right) := by
  obtain ⟨x, hx, hs⟩ := hOuter
  have hnot : ¬ (s.leftRim hn hu hv).OnSide (!G.hubFlip s.left) x := by
    intro h
    have he := (s.leftRim hn hu hv).onSide_unique (G.dualEuler_eq_twice_components hEuler) hs h
    cases hh : G.hubFlip s.left <;> simp only [hh] at he <;> cases he
  have hnotNew := mt (s.split_opposite_sides_union hn hu hv hEuler hf hc
    ⟨x, s.boundary_kept hx⟩).mpr hnot
  change ¬ ((s.switchedSpoke.leftRim hn hu hv).OnSide (s.switch.hubFlip s.left) (s.portSwap x) ∨
    (s.switchedSpoke.rightRim hn hu hv).OnSide (s.switch.hubFlip s.right) (s.portSwap x)) at hnotNew
  rw [s.portSwap_boundary hx] at hnotNew
  have hOldComponent := ((s.leftRim hn hu hv).onSide_union_iff_connected (G.hubFlip s.left) x).mp
    (Or.inl hs)
  have hLeftComponent : Connected s.switch.circuitStep s.switch.pairing.perm x
      (s.switchedSpoke.leftRim hn hu hv).cutBase :=
    (s.switch_dual_connected x (.hub s.left (2 : Fin 3))).mpr hOldComponent
  have hRightComponent : Connected s.switch.circuitStep s.switch.pairing.perm x
      (s.switchedSpoke.rightRim hn hu hv).cutBase :=
    hLeftComponent.trans (s.switchedSpoke.rim_ports_dual_connected (2 : Fin 3) (2 : Fin 3))
  constructor
  · refine ⟨x, (s.switch_isBoundary_iff x).mpr hx, ?_⟩
    rcases ((s.switchedSpoke.leftRim hn hu hv).onSide_union_iff_connected
      (s.switch.hubFlip s.left) x).mpr hLeftComponent with h | h
    · exact (hnotNew (Or.inl h)).elim
    · exact h
  · refine ⟨x, (s.switch_isBoundary_iff x).mpr hx, ?_⟩
    rcases ((s.switchedSpoke.rightRim hn hu hv).onSide_union_iff_connected
      (s.switch.hubFlip s.right) x).mpr hRightComponent with h | h
    · exact (hnotNew (Or.inr h)).elim
    · exact h

theorem split_boundarySide_values
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
    (hf : G.hubFlip s.left = G.hubFlip s.right) (hsees : G.BoundarySeesComponents)
    (hc : Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true))
    (hOuter : (s.leftRim hn hu hv).HasBoundarySide (G.hubFlip s.left))
    (hL : (s.switchedSpoke.leftRim hn hu hv).MeetsBoundary)
    (hR : (s.switchedSpoke.rightRim hn hu hv).MeetsBoundary) :
    (s.switchedSpoke.leftRim hn hu hv).boundarySide hL = (!s.switch.hubFlip s.left) ∧
      (s.switchedSpoke.rightRim hn hu hv).boundarySide hR = (!s.switch.hubFlip s.right) := by
  have hs := s.split_boundary_side_witnesses hn hu hv hEuler hf hc hOuter
  exact ⟨(s.switchedSpoke.leftRim hn hu hv).boundarySide_eq_of_witness
      (s.switch_dualEuler hEuler hf) (s.switch_boundarySeesComponents hf hsees) hL hs.1,
    (s.switchedSpoke.rightRim hn hu hv).boundarySide_eq_of_witness
      (s.switch_dualEuler hEuler hf) (s.switch_boundarySeesComponents hf hsees) hR hs.2⟩

end ThomGame.Pictures.PortGraph.SunSpoke

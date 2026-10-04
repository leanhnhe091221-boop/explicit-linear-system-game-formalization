module

public import ThomGame.Pictures.SunSelectedRimSides
public import ThomGame.Pictures.SunSpokeSideSeparation

/-!
# Individual sides of the two rims produced by a same-rim switch

The side opposite the spoke in each new rim is precisely one of the
two old deleted-spoke regions. The correspondence uses the actual port
exchange, and explicitly identifies which old endpoint represents each
new side. No global outer-side choice is part of this statement.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SunSpoke

open Equiv RibbonConnectivity
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} (s : G.SunSpoke) (hn : 3 ≤ n)
  (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)

theorem leftRim_basePort (side : Bool) :
    (s.leftRim hn hu hv).port (0, side) =
      if side then .hub s.left (1 : Fin 3) else .hub s.left (2 : Fin 3) := by
  cases side
  · rfl
  · exact G.sunRimCircuit_incoming_at_hub hn hu hv (G.sunRimPort hn s.left true) 0 s.left true rfl

theorem rightRim_basePort (side : Bool) :
    (s.rightRim hn hu hv).port (0, side) =
      if side then .hub s.right (1 : Fin 3) else .hub s.right (2 : Fin 3) :=
  s.reverse.leftRim_basePort hn hu hv side

def splitLeftRoot : G.Dart :=
  if G.hubFlip s.left then .hub s.left (0 : Fin 3) else .hub s.right (0 : Fin 3)

def splitRightRoot : G.Dart :=
  if G.hubFlip s.left then .hub s.right (0 : Fin 3) else .hub s.left (0 : Fin 3)

theorem splitLeftRoot_step_kept : s.Kept (G.circuitStep s.splitLeftRoot) := by
  unfold splitLeftRoot
  split_ifs
  · exact s.step_spoke_left_kept
  · exact s.step_spoke_right_kept

theorem splitRightRoot_step_kept : s.Kept (G.circuitStep s.splitRightRoot) := by
  unfold splitRightRoot
  split_ifs
  · exact s.step_spoke_right_kept
  · exact s.step_spoke_left_kept

theorem splitLeftRoot_step_base (hf : G.hubFlip s.left = G.hubFlip s.right) :
    s.portSwap (G.circuitStep s.splitLeftRoot) =
      (s.switchedSpoke.leftRim hn hu hv).port (0, s.switch.hubFlip s.left) := by
  rw [s.switchedSpoke.leftRim_basePort]
  change s.portSwap (G.circuitStep s.splitLeftRoot) =
    if s.switch.hubFlip s.left then .hub s.left (1 : Fin 3) else .hub s.left (2 : Fin 3)
  rw [s.switch_flip_left]
  cases hh : G.hubFlip s.left
  · simp only [splitLeftRoot, hh, Bool.false_eq_true, ite_false, Bool.not_false, ite_true]
    rw [s.portSwap_step_spoke_right, hh]
    rfl
  · simp only [splitLeftRoot, hh, ite_true, Bool.not_true, Bool.false_eq_true, ite_false]
    rw [s.portSwap_step_spoke_left hf, hh]
    rfl

theorem splitRightRoot_step_base (hf : G.hubFlip s.left = G.hubFlip s.right) :
    s.portSwap (G.circuitStep s.splitRightRoot) =
      (s.switchedSpoke.rightRim hn hu hv).port (0, s.switch.hubFlip s.right) := by
  rw [s.switchedSpoke.rightRim_basePort]
  change s.portSwap (G.circuitStep s.splitRightRoot) =
    if s.switch.hubFlip s.right then .hub s.right (1 : Fin 3) else .hub s.right (2 : Fin 3)
  rw [s.switch_flip_right, ← hf]
  cases hh : G.hubFlip s.left
  · simp only [splitRightRoot, hh, Bool.false_eq_true, ite_false, Bool.not_false, ite_true]
    rw [s.portSwap_step_spoke_left hf, hh]
    rfl
  · simp only [splitRightRoot, hh, ite_true, Bool.not_true, Bool.false_eq_true, ite_false]
    rw [s.portSwap_step_spoke_right, hh]
    rfl

theorem leftRimSwitchDeletedPairing_eq_selected
    (hc : Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true)) :
    s.leftRimSwitchDeletedPairing hn hu hv = s.switchedSpoke.selectedRimDeletedPairing hn hu hv := by
  have hm (x : G.Dart) : s.switchedSpoke.SelectedRimMarked hn hu hv x ↔
      (s.leftRim hn hu hv).Marked (s.portSwap x) := by
    apply (s.switch_selected_marked_transport hn hu hv x).trans
    have he := G.sunRimCircuit_marked_iff_of_connected hn hu hv
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true) hc (s.portSwap x)
    exact ⟨fun h => h.elim id he.mpr, Or.inl⟩
  ext x
  have hk : s.switchedSpoke.Kept x ↔ s.Kept x := Iff.rfl
  change s.switchSpokeDeletedPairing _ _ x = _
  rw [s.switchSpokeDeletedPairing_apply, s.switchedSpoke.selectedRimDeletedPairing_apply, hm, hk]
  split_ifs <;> rfl

variable
  (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
  (hf : G.hubFlip s.left = G.hubFlip s.right)
  (hc : Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
    (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true))

include hEuler hf hc in
theorem split_left_opposite_side_iff (x : Subtype s.Kept) :
    (s.switchedSpoke.leftRim hn hu hv).OnSide (s.switch.hubFlip s.left) (s.portSwap x.val) ↔
      Connected G.circuitStep (s.leftRimDeletedPairing hn hu hv) x.val s.splitLeftRoot := by
  have hnewEuler := s.switch.rotationEuler_saturated_iff.mp
    (s.switch_saturated hf (G.rotationEuler_saturated_iff.mpr hEuler))
  have hside := s.switchedSpoke.selectedRim_opposite_left_side_iff hn hu hv
    (s.switch.dualEuler_eq_twice_components hnewEuler)
    (s.switch_rim_separates hn hu hv hEuler hf hc) (s.portSwap x.val)
  apply hside.symm.trans
  change Connected s.switch.circuitStep (s.switchedSpoke.selectedRimDeletedPairing hn hu hv)
    (s.portSwap x.val) ((s.switchedSpoke.leftRim hn hu hv).port (0, s.switch.hubFlip s.left)) ↔ _
  rw [← s.leftRimSwitchDeletedPairing_eq_selected hn hu hv hc, ← s.splitLeftRoot_step_base hn hu hv hf]
  apply (s.leftRim_deleted_connected_iff hn hu hv hf x ⟨_, s.splitLeftRoot_step_kept⟩).symm.trans
  exact ⟨fun h => h.trans (Connected.edge _).symm, fun h => h.trans (Connected.edge _)⟩

include hEuler hf hc in
theorem split_right_opposite_side_iff (x : Subtype s.Kept) :
    (s.switchedSpoke.rightRim hn hu hv).OnSide (s.switch.hubFlip s.right) (s.portSwap x.val) ↔
      Connected G.circuitStep (s.leftRimDeletedPairing hn hu hv) x.val s.splitRightRoot := by
  have hnewEuler := s.switch.rotationEuler_saturated_iff.mp
    (s.switch_saturated hf (G.rotationEuler_saturated_iff.mpr hEuler))
  have hside := s.switchedSpoke.selectedRim_opposite_right_side_iff hn hu hv
    (s.switch.dualEuler_eq_twice_components hnewEuler)
    (s.switch_rim_separates hn hu hv hEuler hf hc) (s.portSwap x.val)
  apply hside.symm.trans
  change Connected s.switch.circuitStep (s.switchedSpoke.selectedRimDeletedPairing hn hu hv)
    (s.portSwap x.val) ((s.switchedSpoke.rightRim hn hu hv).port (0, s.switch.hubFlip s.right)) ↔ _
  rw [← s.leftRimSwitchDeletedPairing_eq_selected hn hu hv hc, ← s.splitRightRoot_step_base hn hu hv hf]
  apply (s.leftRim_deleted_connected_iff hn hu hv hf x ⟨_, s.splitRightRoot_step_kept⟩).symm.trans
  exact ⟨fun h => h.trans (Connected.edge _).symm, fun h => h.trans (Connected.edge _)⟩

include hEuler hf hc in
theorem split_opposite_sides_disjoint (x : Subtype s.Kept) :
    ¬ ((s.switchedSpoke.leftRim hn hu hv).OnSide (s.switch.hubFlip s.left) (s.portSwap x.val) ∧
      (s.switchedSpoke.rightRim hn hu hv).OnSide (s.switch.hubFlip s.right) (s.portSwap x.val)) := by
  rw [s.split_left_opposite_side_iff hn hu hv hEuler hf hc,
    s.split_right_opposite_side_iff hn hu hv hEuler hf hc]
  have hsep := s.leftRim_deleted_spoke_regions_disjoint hn hu hv hEuler hf hc x.val
  cases hh : G.hubFlip s.left <;> simp only [splitLeftRoot, splitRightRoot, hh,
    Bool.false_eq_true, ite_true, ite_false]
  · exact fun h => hsep h.symm
  · exact hsep

include hEuler hf hc in
theorem split_opposite_sides_union (x : Subtype s.Kept) :
    (s.leftRim hn hu hv).OnSide (!G.hubFlip s.left) x.val ↔
      (s.switchedSpoke.leftRim hn hu hv).OnSide (s.switch.hubFlip s.left) (s.portSwap x.val) ∨
      (s.switchedSpoke.rightRim hn hu hv).OnSide (s.switch.hubFlip s.right) (s.portSwap x.val) := by
  rw [s.split_left_opposite_side_iff hn hu hv hEuler hf hc,
    s.split_right_opposite_side_iff hn hu hv hEuler hf hc, s.leftRim_spoke_side_union]
  cases hh : G.hubFlip s.left <;> simp only [splitLeftRoot, splitRightRoot, hh,
    Bool.false_eq_true, ite_true, ite_false]
  exact or_comm

end ThomGame.Pictures.PortGraph.SunSpoke

module

public import ThomGame.Pictures.SunDisjointRimSides
public import ThomGame.Pictures.SunSpokeSideDeletion
public import ThomGame.Pictures.SunSelectedRimMasks

/-!
# Opposite-spoke sides survive cutting both distinct selected rims

The other selected rim is entirely on the spoke side of the first.
Deleting that rim and the spoke therefore preserves the opposite side,
with its original base port. Both left and right statements concern the
same actual permutation cutting the union of the two rim markings.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SunSpoke

open Equiv RibbonConnectivity
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} (s : G.SunSpoke) (hn : 3 ≤ n)
  (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)

def reverse : G.SunSpoke := ⟨s.right, s.left, s.paired_right⟩

noncomputable def rightRim : G.SimpleCircuit := s.reverse.leftRim hn hu hv

theorem selectedRimMarked_twin_iff (x : G.Dart) :
    s.SelectedRimMarked hn hu hv (G.pairing.twin x) ↔ s.SelectedRimMarked hn hu hv x :=
  or_congr ((s.leftRim hn hu hv).marked_twin_iff x) ((s.rightRim hn hu hv).marked_twin_iff x)

noncomputable def selectedRimDeletedPairing : Perm G.Dart :=
  s.spokeDeletedPairing (fun x => ¬ s.SelectedRimMarked hn hu hv x)
    (fun x => not_congr (s.selectedRimMarked_twin_iff hn hu hv x))

theorem selectedRimDeletedPairing_apply (x : G.Dart) :
    s.selectedRimDeletedPairing hn hu hv x =
      if s.Kept x ∧ ¬ s.SelectedRimMarked hn hu hv x then G.pairing.twin x else x := by
  by_cases hx : s.Kept x ∧ ¬ s.SelectedRimMarked hn hu hv x <;>
    simp only [selectedRimDeletedPairing, s.spokeDeletedPairing_apply, hx, ite_false]

theorem leftRim_otherCut_kept_iff (x : G.Dart) :
    (s.Kept ((s.leftRim hn hu hv).cutPairing x) ∧
      ¬ (s.rightRim hn hu hv).Marked ((s.leftRim hn hu hv).cutPairing x)) ↔
      (s.Kept x ∧ ¬ (s.rightRim hn hu hv).Marked x) := by
  rw [(s.leftRim hn hu hv).cutPairing_eq_retainEdges]
  exact RotationEuler.retainEdges_preserves G.pairing.perm
    (fun z => ¬ (s.leftRim hn hu hv).Marked z)
    (fun z => not_congr ((s.leftRim hn hu hv).marked_twin_iff z))
    (fun z => s.Kept z ∧ ¬ (s.rightRim hn hu hv).Marked z)
    (fun z => and_congr (s.twin_kept_iff z)
      (not_congr ((s.rightRim hn hu hv).marked_twin_iff z))) x

theorem selectedRimDeletedPairing_left_eq :
    s.selectedRimDeletedPairing hn hu hv =
      RotationEuler.retainEdges (s.leftRim hn hu hv).cutPairing
        (fun x => s.Kept x ∧ ¬ (s.rightRim hn hu hv).Marked x)
        (s.leftRim_otherCut_kept_iff hn hu hv) := by
  ext x
  have hm : s.SelectedRimMarked hn hu hv x ↔
      (s.leftRim hn hu hv).Marked x ∨ (s.rightRim hn hu hv).Marked x := Iff.rfl
  rw [s.selectedRimDeletedPairing_apply, hm, RotationEuler.retainEdges_apply,
    (s.leftRim hn hu hv).cutPairing_eq_retainEdges, RotationEuler.retainEdges_apply]
  by_cases hk : s.Kept x <;> by_cases hl : (s.leftRim hn hu hv).Marked x <;>
      by_cases hr : (s.rightRim hn hu hv).Marked x <;>
    simp only [hk, hl, hr, or_true, or_false, not_true_eq_false,
      not_false_eq_true, and_true, and_false, ite_true, ite_false]
  rfl

theorem rightRim_marked_on_left_spoke_side
    (hsep : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true))
    (x : G.Dart) (hx : (s.rightRim hn hu hv).Marked x) :
    (s.leftRim hn hu hv).OnSide (!G.hubFlip s.left) x := by
  have ha : ¬ (s.leftRim hn hu hv).OnCircuitVertex (.inr (.inl s.right)) :=
    fun ha => hsep ((G.sunRimCircuit_onHub_iff_connected hn hu hv
      (G.sunRimPort hn s.left true) s.right).mp ha)
  have hs : (s.leftRim hn hu hv).OnSide (!G.hubFlip s.left) (.hub s.right (2 : Fin 3)) :=
    ((s.leftRim hn hu hv).onSide_same_vertex
      (a := .hub s.right (0 : Fin 3)) (b := .hub s.right (2 : Fin 3))
      ha rfl (!G.hubFlip s.left)).mp (s.leftRim_spoke_onSide_right hn hu hv)
  exact G.sunRimCircuit_marked_onSide_of_rim_away hn hu hv
    (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true) hsep (!G.hubFlip s.left) hs x hx

theorem selectedRim_opposite_left_side_iff
    (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm))
    (hsep : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true)) (x : G.Dart) :
    Connected G.circuitStep (s.selectedRimDeletedPairing hn hu hv)
        x ((s.leftRim hn hu hv).port (0, G.hubFlip s.left)) ↔
      (s.leftRim hn hu hv).OnSide (G.hubFlip s.left) x := by
  rw [s.selectedRimDeletedPairing_left_eq]
  apply (s.leftRim hn hu hv).opposite_deletion_onSide_iff hEuler
  intro z hz
  by_cases hk : s.Kept z
  · have hm : (s.rightRim hn hu hv).Marked z := by
      by_contra hm
      exact hz ⟨hk, hm⟩
    exact s.rightRim_marked_on_left_spoke_side hn hu hv hsep z hm
  · exact s.leftRim_omitted_onSide hn hu hv z hk

theorem reverse_selectedRimDeletedPairing :
    s.reverse.selectedRimDeletedPairing hn hu hv = s.selectedRimDeletedPairing hn hu hv := by
  ext x
  have hk : s.reverse.Kept x ↔ s.Kept x := and_comm
  have hm : s.reverse.SelectedRimMarked hn hu hv x ↔ s.SelectedRimMarked hn hu hv x := or_comm
  rw [s.reverse.selectedRimDeletedPairing_apply, s.selectedRimDeletedPairing_apply, hk, hm]

theorem leftRim_opposite_side_kept
    (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm))
    {x : G.Dart} (hx : (s.leftRim hn hu hv).OnSide (G.hubFlip s.left) x) : s.Kept x := by
  by_contra hk
  have he := (s.leftRim hn hu hv).onSide_unique hEuler hx
    (s.leftRim_omitted_onSide hn hu hv x hk)
  cases hh : G.hubFlip s.left <;> simp only [hh] at he <;> cases he

theorem rightRim_opposite_side_kept
    (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm))
    {x : G.Dart} (hx : (s.rightRim hn hu hv).OnSide (G.hubFlip s.right) x) : s.Kept x :=
  (s.reverse.leftRim_opposite_side_kept hn hu hv hEuler hx).symm

theorem selectedRim_opposite_right_side_iff
    (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm))
    (hsep : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true)) (x : G.Dart) :
    Connected G.circuitStep (s.selectedRimDeletedPairing hn hu hv)
        x ((s.rightRim hn hu hv).port (0, G.hubFlip s.right)) ↔
      (s.rightRim hn hu hv).OnSide (G.hubFlip s.right) x := by
  have hsep' : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.reverse.left true) (G.sunRimPort hn s.reverse.right true) :=
    fun h => hsep h.symm
  have he := s.reverse.selectedRim_opposite_left_side_iff hn hu hv hEuler hsep' x
  rw [s.reverse_selectedRimDeletedPairing] at he
  exact he

end ThomGame.Pictures.PortGraph.SunSpoke

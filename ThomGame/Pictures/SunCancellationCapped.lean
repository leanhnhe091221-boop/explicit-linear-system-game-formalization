module

public import ThomGame.Pictures.SunCancellationEuler
public import ThomGame.Pictures.CappedGraphRealization

/-!
# Cancellation inside the prescribed boundary cap

Boundary capping fixes every hub port and hence commutes with the local
rotation target swaps. The same contraction and three vertex splits
preserve capped Euler saturation. Disconnected capped realization then
produces an actual smaller diagram on the original boundary word.
The input capped saturation remains explicit here.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv CycleSurgery FiniteReturn RibbonConnectivity RotationEuler
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {w : List S}

theorem cappingTargets_hub (G : PortGraph P w []) (h : G.Hub)
    (i : Fin (P.word (G.hubLabel h)).length) :
    G.cappingTargets (.hub h i) = .hub h i := G.cappingTargets_unmarked _ id

theorem cappingTargets_splice (G : PortGraph P w []) (r : Perm G.Dart) (a b : G.Dart)
    (ha : G.cappingTargets a = a) (hb : G.cappingTargets b = b) :
    G.cappingTargets * splice r a b = splice (G.cappingTargets * r) a b := by
  rw [splice, splice, ← mul_assoc, mul_swap_eq_swap_mul, ha, hb, mul_assoc]

theorem cappedRotation_sameCycle_hub_iff (G : PortGraph P w []) (h : G.Hub)
    (i : Fin (P.word (G.hubLabel h)).length) (y : G.Dart) :
    G.cappedRotation.SameCycle (.hub h i) y ↔ G.rotation.SameCycle (.hub h i) y := by
  apply MarkedReturn.sameCycle_mul_iff_of_avoids G.rotation G.IsBoundary G.cappingTargets
    G.cappingTargets_unmarked
  intro x hx
  have hv := (G.rotation_sameCycle_iff _ _).mp hx
  cases x <;> simp [Port.vertex] at hv ⊢
  all_goals exact id

theorem sun_cappingTargets_hub {n : Nat} {b : Fin n → ZMod 2}
    {w : List (Fin n ⊕ Fin n)} (G : PortGraph (sunPresentation n b) w [])
    (h : G.Hub) (i : Fin 3) : G.cappingTargets (.hub h i) = .hub h i :=
  G.cappingTargets_hub h i

namespace SunSpoke

variable {n : Nat} {b : Fin n → ZMod 2} {w : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) w []} (s : G.SunSpoke)

theorem cancelContract_left :
    s.cancelContractRotation (.hub s.left (0 : Fin 3)) = G.rotation (.hub s.left (0 : Fin 3)) := by
  rw [cancelContractRotation, splice_apply,
    swap_apply_of_ne_of_ne (sun_rotation_spoke_ne_spoke _ _) (sun_rotation_spoke_ne_spoke _ _)]

theorem cancelContract_right :
    s.cancelContractRotation (.hub s.right (0 : Fin 3)) = G.rotation (.hub s.right (0 : Fin 3)) := by
  rw [cancelContractRotation, splice_apply,
    swap_apply_of_ne_of_ne (sun_rotation_spoke_ne_spoke _ _) (sun_rotation_spoke_ne_spoke _ _)]

theorem cancelLeft_right :
    s.cancelLeftRotation (.hub s.right (0 : Fin 3)) = G.rotation (.hub s.right (0 : Fin 3)) := by
  rw [cancelLeftRotation, splice_apply, s.cancelContract_left, s.cancelContract_right]
  apply swap_apply_of_ne_of_ne (sun_rotation_spoke_ne_spoke _ _)
  apply G.rotation.injective.ne
  simpa only [ne_eq, sun_hub_eq_iff, and_true] using s.distinct.symm

theorem cap_cancelContract_left :
    G.cappingTargets (s.cancelContractRotation (.hub s.left (0 : Fin 3))) =
      s.cancelContractRotation (.hub s.left (0 : Fin 3)) := by
  rw [s.cancelContract_left, sun_rotation_hub, G.sun_cappingTargets_hub]

theorem cap_cancelLeft_right :
    G.cappingTargets (s.cancelLeftRotation (.hub s.right (0 : Fin 3))) =
      s.cancelLeftRotation (.hub s.right (0 : Fin 3)) := by
  rw [s.cancelLeft_right, sun_rotation_hub, G.sun_cappingTargets_hub]

theorem cancelFull_capped_saturated (hf : G.hubFlip s.left ≠ G.hubFlip s.right)
    (hcap : count G.cappedRotation G.pairing.perm =
      2 * Nat.card (Component G.cappedRotation G.pairing.perm)) :
    count (G.cappingTargets * s.cancelFullRotation) s.cancelFullPairing =
      2 * Nat.card (Component (G.cappingTargets * s.cancelFullRotation) s.cancelFullPairing) := by
  have hn : ¬ G.cappedRotation.SameCycle (.hub s.left (0 : Fin 3))
      (G.pairing.perm (.hub s.left (0 : Fin 3))) := by
    change ¬ G.cappedRotation.SameCycle _ (G.pairing.twin _)
    rw [s.paired]
    intro he
    have h := (G.cappedRotation_sameCycle_hub_iff s.left (0 : Fin 3) _).mp he
    have hv := (G.rotation_sameCycle_iff _ _).mp h
    exact s.distinct (Sum.inl.inj (Sum.inr.inj hv))
  have hC := contractEdge_saturated G.cappedRotation G.pairing.perm G.pairing.involutive hcap _ hn
  have hpair : G.pairing.perm (.hub s.left (0 : Fin 3)) = .hub s.right (0 : Fin 3) := s.paired
  simp only [hpair] at hC
  have eC : G.cappingTargets * s.cancelContractRotation =
      splice G.cappedRotation (.hub s.left (0 : Fin 3)) (.hub s.right (0 : Fin 3)) :=
    G.cappingTargets_splice G.rotation _ _ (G.sun_cappingTargets_hub _ _) (G.sun_cappingTargets_hub _ _)
  have eL : G.cappingTargets * s.cancelLeftRotation =
      splice (G.cappingTargets * s.cancelContractRotation) (.hub s.left (0 : Fin 3))
        ((G.cappingTargets * s.cancelContractRotation) (.hub s.left (0 : Fin 3))) := by
    change G.cappingTargets * splice _ _ _ = _
    rw [G.cappingTargets_splice _ _ _ (G.sun_cappingTargets_hub _ _) s.cap_cancelContract_left]
    simp only [Perm.mul_apply, s.cap_cancelContract_left]
  have eR : G.cappingTargets * s.cancelRimRotation =
      splice (G.cappingTargets * s.cancelLeftRotation) (.hub s.right (0 : Fin 3))
        ((G.cappingTargets * s.cancelLeftRotation) (.hub s.right (0 : Fin 3))) := by
    change G.cappingTargets * splice _ _ _ = _
    rw [G.cappingTargets_splice _ _ _ (G.sun_cappingTargets_hub _ _) s.cap_cancelLeft_right]
    simp only [Perm.mul_apply, s.cap_cancelLeft_right]
  have hL := splitVertex_saturated (G.cappingTargets * s.cancelContractRotation) s.cancelFullPairing
    s.cancelFullPairing_involutive (by rw [eC]; exact hC)
    (show (G.cappingTargets * s.cancelContractRotation).SameCycle (.hub s.left (0 : Fin 3))
      ((G.cappingTargets * s.cancelContractRotation) (.hub s.left (0 : Fin 3))) from Perm.SameCycle.rfl.apply_right)
  rw [← eL] at hL
  have hR := splitVertex_saturated (G.cappingTargets * s.cancelLeftRotation) s.cancelFullPairing
    s.cancelFullPairing_involutive hL
    (show (G.cappingTargets * s.cancelLeftRotation).SameCycle (.hub s.right (0 : Fin 3))
      ((G.cappingTargets * s.cancelLeftRotation) (.hub s.right (0 : Fin 3))) from Perm.SameCycle.rfl.apply_right)
  rw [← eR] at hR
  have hs : (G.cappingTargets * s.cancelRimRotation).SameCycle
      (.hub s.left s.cancelLast) (.hub s.right s.cancelFirst) := by
    have ha : (G.cappingTargets * s.cancelRimRotation).SameCycle (.hub s.left s.cancelLast)
        ((G.cappingTargets * s.cancelRimRotation) (.hub s.left s.cancelLast)) := Perm.SameCycle.rfl.apply_right
    have hb : (G.cappingTargets * s.cancelRimRotation).SameCycle (.hub s.right s.cancelLast)
        ((G.cappingTargets * s.cancelRimRotation) (.hub s.right s.cancelLast)) := Perm.SameCycle.rfl.apply_right
    rw [Perm.mul_apply, s.cancelRim_last_left hf, G.sun_cappingTargets_hub] at ha
    rw [Perm.mul_apply, s.cancelRim_last_right hf, G.sun_cappingTargets_hub] at hb
    exact ha.trans hb
  rw [cancelFullRotation,
    G.cappingTargets_splice _ _ _ (G.sun_cappingTargets_hub _ _) (G.sun_cappingTargets_hub _ _)]
  exact splitVertex_saturated _ _ s.cancelFullPairing_involutive hR hs

theorem cancelPort_boundary (i : Fin w.length) :
    s.cancelPort (Port.top i) = G.boundaryDart (.inl i) := rfl

theorem cancelPort_cappingTargets (x : s.cancel.Dart) :
    s.cancelPort (s.cancel.cappingTargets x) = G.cappingTargets (s.cancelPort x) := by
  cases x with
  | top i =>
    change s.cancelPort (s.cancel.cappingTargets (s.cancel.boundaryDart (.inl i))) =
      G.cappingTargets (G.boundaryDart (.inl i))
    rw [s.cancel.cappingTargets_boundary, G.cappingTargets_boundary, boundaryCyclic_symm_top]
    rfl
  | bottom i => exact i.elim0
  | hub h i =>
    rw [s.cancel.cappingTargets_hub h i]
    exact (G.cappingTargets_hub h.val i).symm
  | joint j side =>
    rw [s.cancel.cappingTargets_unmarked _ id]
    cases j with
    | inl j => exact (G.cappingTargets_unmarked _ id).symm
    | inr rim => exact (G.sun_cappingTargets_hub _ _).symm

theorem cappingTargets_kept_iff (x : G.Dart) : s.Kept (G.cappingTargets x) ↔ s.Kept x := by
  have ha : G.cappingTargets x = .hub s.left (0 : Fin 3) ↔ x = .hub s.left (0 : Fin 3) := by
    simpa only [G.sun_cappingTargets_hub] using G.cappingTargets.injective.eq_iff
      (a := x) (b := .hub s.left (0 : Fin 3))
  have hb : G.cappingTargets x = .hub s.right (0 : Fin 3) ↔ x = .hub s.right (0 : Fin 3) := by
    simpa only [G.sun_cappingTargets_hub] using G.cappingTargets.injective.eq_iff
      (a := x) (b := .hub s.right (0 : Fin 3))
  exact and_congr (not_congr ha) (not_congr hb)

theorem cancel_capped_saturated (hf : G.hubFlip s.left ≠ G.hubFlip s.right)
    (hcap : count G.cappedRotation G.pairing.perm =
      2 * Nat.card (Component G.cappedRotation G.pairing.perm)) :
    count s.cancel.cappedRotation s.cancel.pairing.perm =
      2 * Nat.card (Component s.cancel.cappedRotation s.cancel.pairing.perm) := by
  have hk : ∀ x, s.Kept ((G.cappingTargets * s.cancelFullRotation) x) ↔ s.Kept x :=
    fun x => (s.cappingTargets_kept_iff _).trans (s.cancelFull_kept_iff hf x)
  let r := (G.cappingTargets * s.cancelFullRotation).subtypePerm hk
  let t := s.cancelFullPairing.subtypePerm s.cancelFullPairing_kept_iff
  have hs : count r t = 2 * Nat.card (Component r t) :=
    subtype_saturated _ _ s.Kept hk s.cancelFullPairing_kept_iff s.cancelFullPairing_involutive
      (s.cancelFull_capped_saturated hf hcap)
  have hr : ∀ x, r (s.cancelPorts x) = s.cancelPorts (s.cancel.cappedRotation x) := by
    intro x
    apply Subtype.ext
    change G.cappingTargets (s.cancelFullRotation (s.cancelPort x)) =
      s.cancelPort (s.cancel.cappingTargets (s.cancel.rotation x))
    rw [s.cancelFull_rotation hf, s.cancelPort_cappingTargets]
  have ht : ∀ x, t (s.cancelPorts x) = s.cancelPorts (s.cancel.pairing.perm x) :=
    fun x => Subtype.ext ((s.cancelFullPairing_kept _ (s.cancelPort_kept x)).trans (s.cancel_twin x).symm)
  rw [count_congr s.cancel.cappedRotation s.cancel.pairing.perm r t s.cancelPorts hr ht,
    Nat.card_congr (componentCongrEquiv s.cancel.cappedRotation s.cancel.pairing.perm r t s.cancelPorts hr ht)]
  exact hs

theorem exists_cancelled_diagram_of_capped (hw : 0 < w.length)
    (hf : G.hubFlip s.left ≠ G.hubFlip s.right)
    (hcap : count G.cappedRotation G.pairing.perm =
      2 * Nat.card (Component G.cappedRotation G.pairing.perm)) :
    ∃ d : Diagram (sunPresentation n b) w [],
      d.size + 2 = Fintype.card G.Hub ∧ d.sign = G.sign ∧
      (∀ j, d.character j = G.character j) := by
  obtain ⟨d, _, hd, hs⟩ := s.cancel.exists_diagram_of_capped_saturated_preserving hw
    (fun _ => by change 0 < 3; decide +kernel) (s.cancel_capped_saturated hf hcap)
  refine ⟨d, ?_, hs.trans s.cancel_sign, ?_⟩
  · rw [hd]
    exact s.cancel_hub_card
  · intro j
    rw [d.sun_character, G.sun_character]

end SunSpoke
end ThomGame.Pictures.PortGraph

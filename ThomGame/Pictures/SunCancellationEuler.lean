module

public import ThomGame.Pictures.SunCancellationRotation
public import ThomGame.Pictures.InvariantEuler
public import ThomGame.Pictures.SmoothingEuler

/-!
# Euler saturation of the actual cancelled sun graph

The removed spoke ports are fixed by both full surgery permutations.
Restricting to their invariant complement preserves Euler saturation.
The explicit port equivalence identifies that restriction with the
actual two-joint cancellation graph, including its pairing and rotation.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SunSpoke

open Equiv CycleSurgery FiniteReturn RibbonConnectivity RotationEuler
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} (s : G.SunSpoke)

theorem cancelFull_kept_iff (hf : G.hubFlip s.left ≠ G.hubFlip s.right) (x : G.Dart) :
    s.Kept (s.cancelFullRotation x) ↔ s.Kept x := by
  have ha : s.cancelFullRotation (.hub s.left (0 : Fin 3)) = .hub s.left (0 : Fin 3) := by
    rw [s.cancelFull_hub_left hf, ite_eq_left rfl]
  have hb : s.cancelFullRotation (.hub s.right (0 : Fin 3)) = .hub s.right (0 : Fin 3) := by
    rw [s.cancelFull_hub_right hf, ite_eq_left rfl]
  have hla : s.cancelFullRotation x = .hub s.left (0 : Fin 3) ↔ x = .hub s.left (0 : Fin 3) := by
    simpa only [ha] using s.cancelFullRotation.injective.eq_iff (a := x) (b := .hub s.left (0 : Fin 3))
  have hlb : s.cancelFullRotation x = .hub s.right (0 : Fin 3) ↔ x = .hub s.right (0 : Fin 3) := by
    simpa only [hb] using s.cancelFullRotation.injective.eq_iff (a := x) (b := .hub s.right (0 : Fin 3))
  exact and_congr (not_congr hla) (not_congr hlb)

theorem cancelFullPairing_kept_iff (x : G.Dart) :
    s.Kept (s.cancelFullPairing x) ↔ s.Kept x := by
  have ha : s.cancelFullPairing (.hub s.left (0 : Fin 3)) = .hub s.left (0 : Fin 3) := by
    change swap _ _ (G.pairing.twin _) = _
    rw [s.paired, swap_apply_right]
  have hb : s.cancelFullPairing (.hub s.right (0 : Fin 3)) = .hub s.right (0 : Fin 3) := by
    change swap _ _ (G.pairing.twin _) = _
    rw [s.paired_right, swap_apply_left]
  have hla : s.cancelFullPairing x = .hub s.left (0 : Fin 3) ↔ x = .hub s.left (0 : Fin 3) := by
    simpa only [ha] using s.cancelFullPairing.injective.eq_iff (a := x) (b := .hub s.left (0 : Fin 3))
  have hlb : s.cancelFullPairing x = .hub s.right (0 : Fin 3) ↔ x = .hub s.right (0 : Fin 3) := by
    simpa only [hb] using s.cancelFullPairing.injective.eq_iff (a := x) (b := .hub s.right (0 : Fin 3))
  exact and_congr (not_congr hla) (not_congr hlb)

theorem cancelFullPairing_involutive : Function.Involutive s.cancelFullPairing := by
  have h := removed_pair_involutive G.pairing.perm G.pairing.involutive
    (.hub s.left (0 : Fin 3))
  have hp : G.pairing.perm (.hub s.left (0 : Fin 3)) = .hub s.right (0 : Fin 3) := s.paired
  rw [hp] at h
  exact h

theorem cancelFullPairing_kept (x : G.Dart) (hx : s.Kept x) :
    s.cancelFullPairing x = G.pairing.twin x := by
  change swap _ _ (G.pairing.twin x) = _
  exact swap_apply_of_ne_of_ne (s.twin_kept hx).1 (s.twin_kept hx).2

theorem cancel_saturated (hf : G.hubFlip s.left ≠ G.hubFlip s.right)
    (hEuler : count G.rotation G.pairing.perm =
      2 * Nat.card (Component G.rotation G.pairing.perm)) :
    count s.cancel.rotation s.cancel.pairing.perm =
      2 * Nat.card (Component s.cancel.rotation s.cancel.pairing.perm) := by
  let r := s.cancelFullRotation.subtypePerm (s.cancelFull_kept_iff hf)
  let t := s.cancelFullPairing.subtypePerm s.cancelFullPairing_kept_iff
  have hs : count r t = 2 * Nat.card (Component r t) :=
    subtype_saturated s.cancelFullRotation s.cancelFullPairing s.Kept
      (s.cancelFull_kept_iff hf) s.cancelFullPairing_kept_iff s.cancelFullPairing_involutive
      (s.cancelFull_saturated hf hEuler)
  have hr : ∀ x, r (s.cancelPorts x) = s.cancelPorts (s.cancel.rotation x) :=
    fun x => Subtype.ext (s.cancelFull_rotation hf x)
  have ht : ∀ x, t (s.cancelPorts x) = s.cancelPorts (s.cancel.pairing.perm x) :=
    fun x => Subtype.ext ((s.cancelFullPairing_kept _ (s.cancelPort_kept x)).trans (s.cancel_twin x).symm)
  rw [count_congr s.cancel.rotation s.cancel.pairing.perm r t s.cancelPorts hr ht,
    Nat.card_congr (componentCongrEquiv s.cancel.rotation s.cancel.pairing.perm r t s.cancelPorts hr ht)]
  exact hs

theorem cancel_eulerDefect (hf : G.hubFlip s.left ≠ G.hubFlip s.right)
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0) :
    eulerDefect s.cancel.pairing.perm s.cancel.circuitStep = 0 := by
  have hG := Nat.card_congr
    (rotationComponentEquiv G.rotation G.pairing.perm G.pairing.involutive)
  have hH := Nat.card_congr
    (rotationComponentEquiv s.cancel.rotation s.cancel.pairing.perm s.cancel.pairing.involutive)
  rw [G.rotation_mul_pairing] at hG
  rw [s.cancel.rotation_mul_pairing] at hH
  have hs : count G.rotation G.pairing.perm = 2 * Nat.card (Component G.rotation G.pairing.perm) := by
    rw [G.rotationEuler_eq_eulerCount, hG]
    unfold eulerDefect at hEuler
    omega
  have hc := s.cancel_saturated hf hs
  rw [s.cancel.rotationEuler_eq_eulerCount, hH] at hc
  unfold eulerDefect
  omega

/-- Complete smoothing records any circles and keeps the exact original
boundary words, with two fewer hubs and the same character. -/
theorem exists_cancelled_without_junctions (hf : G.hubFlip s.left ≠ G.hubFlip s.right)
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0) :
    ∃ (H : PortGraph (sunPresentation n b) u v) (circles : List (Fin n ⊕ Fin n)),
      Nonempty (Smoothing s.cancel H circles) ∧ IsEmpty H.Joint ∧
      Fintype.card H.Hub + 2 = Fintype.card G.Hub ∧ H.sign = G.sign ∧
      (∀ j, H.character j = G.character j) ∧ eulerDefect H.pairing.perm H.circuitStep = 0 := by
  obtain ⟨H, circles, ⟨d⟩, hj⟩ := Smoothing.exists_without_junctions s.cancel
  refine ⟨H, circles, ⟨d⟩, hj, ?_, d.sign.trans s.cancel_sign, ?_, ?_⟩
  · rw [d.hub_card]
    exact s.cancel_hub_card
  · intro j
    rw [H.sun_character, G.sun_character]
  · rw [d.eulerDefect (fun _ => by change 0 < 3; decide +kernel)]
    exact s.cancel_eulerDefect hf hEuler

end ThomGame.Pictures.PortGraph.SunSpoke

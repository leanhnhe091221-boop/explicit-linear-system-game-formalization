module

public import ThomGame.Pictures.RotationEulerBound
public import ThomGame.Pictures.OrbitTransport

/-!
# The Euler upper bound for actual port graphs

The permutation-map count is identified with the existing dart Euler
count, using the actual two-element edge fibres. Connectivity and face
counts are transported along explicit permutation equivalences.
-/

@[expose] public section
namespace ThomGame.Pictures

open Equiv FiniteReturn RibbonConnectivity

namespace RotationEuler

variable {D : Type*} [Finite D] (r t : Perm D) (ht : Function.Involutive t)

omit [Finite D] in
include ht in
theorem connected_rotation_iff (a b : D) : Connected r t a b ↔ Connected t (r * t) a b := by
  constructor
  · intro h
    apply h.lift id ⟨Connected.refl, Connected.symm, Connected.trans⟩
    · intro x
      have he : (r * t) (t x) = r x := by change r (t (t x)) = r x; rw [ht]
      have hc : Connected t (r * t) (t x) ((r * t) (t x)) := Connected.circuit _
      rw [he] at hc
      exact (Connected.edge x).trans hc
    · intro x
      exact Connected.edge x
  · intro h
    apply h.lift id ⟨Connected.refl, Connected.symm, Connected.trans⟩
    · intro x
      exact Connected.circuit x
    · intro x
      exact (Connected.circuit x).trans (Connected.edge (t x))

noncomputable def rotationComponentEquiv : Component r t ≃ Component t (r * t) := by
  classical
  exact componentEquiv r t t (r * t) (connected_rotation_iff r t ht)

noncomputable def productOrbitEquiv : Orbit (t * r) ≃ Orbit (r * t) :=
  orbitEquiv (t * r) (r * t) t (fun x => by
    change r (t (t x)) = t (t (r x))
    rw [ht, ht])

omit [Finite D] in
theorem connected_swap_iff (a b : D) : Connected r t a b ↔ Connected t r a b := by
  constructor
  · intro h
    exact h.lift id ⟨Connected.refl, Connected.symm, Connected.trans⟩ Connected.circuit Connected.edge
  · intro h
    exact h.lift id ⟨Connected.refl, Connected.symm, Connected.trans⟩ Connected.circuit Connected.edge

noncomputable def dualComponentEquiv : Component r t ≃ Component (r * t) t := by
  classical
  apply componentEquiv r t (r * t) t
  intro a b
  exact (connected_rotation_iff r t ht a b).trans (connected_swap_iff t (r * t) a b)

include ht in
theorem dual_count : count (r * t) t = count r t := by
  have hf := Nat.card_congr (productOrbitEquiv r t ht)
  have hv := Nat.card_congr (orbitEquiv r (t * (r * t)) t (fun x => by
    change t (r (t (t x))) = t (r x)
    rw [ht]))
  unfold count
  rw [← hv]
  omega

end RotationEuler

namespace PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S} (G : PortGraph P u v)

theorem rotation_mul_pairing : G.rotation * G.pairing.perm = G.circuitStep := by
  ext a
  rfl

theorem rotationEuler_eq_eulerCount :
    RotationEuler.count G.rotation G.pairing.perm = eulerCount G.pairing.perm G.circuitStep := by
  classical
  have hf := Nat.card_congr
    (RotationEuler.productOrbitEquiv G.rotation G.pairing.perm G.pairing.involutive)
  rw [G.rotation_mul_pairing] at hf
  have he := Nat.card_congr G.edgeOrbitEquiv
  have hd : Nat.card G.Dart = 2 * Nat.card (Orbit G.pairing.perm) := by
    rw [he]
    simpa only [Nat.card_eq_fintype_card] using G.pairing.dart_card_eq_twice_edge_card
  unfold RotationEuler.count eulerCount
  rw [G.circuit_mul_pairing, hf]
  omega

theorem dualEuler_eq_eulerCount :
    RotationEuler.count G.circuitStep G.pairing.perm = eulerCount G.pairing.perm G.circuitStep := by
  rw [← G.rotation_mul_pairing,
    RotationEuler.dual_count G.rotation G.pairing.perm G.pairing.involutive]
  rw [G.rotation_mul_pairing]
  exact G.rotationEuler_eq_eulerCount

theorem eulerDefect_nonpos : eulerDefect G.pairing.perm G.circuitStep ≤ 0 := by
  classical
  have h := RotationEuler.count_le_twice_components G.rotation G.pairing.perm G.pairing.involutive
  have hc := Nat.card_congr
    (RotationEuler.rotationComponentEquiv G.rotation G.pairing.perm G.pairing.involutive)
  rw [G.rotation_mul_pairing] at hc
  rw [G.rotationEuler_eq_eulerCount, hc] at h
  unfold eulerDefect
  omega

theorem ribbonEuler_le_twice_components
    (hn : ∀ h : G.Hub, 0 < (P.word (G.hubLabel h)).length) :
    G.ribbonEuler ≤ 2 * Nat.card G.GraphComponent := by
  have h := G.eulerDefect_nonpos
  rw [G.eulerDefect_eq_ribbonEuler hn] at h
  omega

end PortGraph
end ThomGame.Pictures

module

public import ThomGame.Pictures.SunSwitchReturn
public import ThomGame.Pictures.RotationEulerGraph
public import ThomGame.Pictures.ComponentTransport

/-!
# Connectivity and Euler preservation of the actual sun switch

The switched spoke still connects the same two hubs. Thus exchanging
attachments inside this connected patch preserves every original
component. Together with the face-return equivalence this preserves
Euler saturation, without a simplicity assumption on other edges.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SunSpoke

open Equiv FiniteReturn RibbonConnectivity
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} (s : G.SunSpoke)

theorem rim_ports_connected (i j : Fin 3) :
    Connected G.pairing.perm G.rotation (.hub s.left i) (.hub s.right j) := by
  have h : Connected G.pairing.perm G.rotation (.hub s.left (0 : Fin 3)) (.hub s.right (0 : Fin 3)) := by
    have h := Connected.edge (p := G.pairing.perm) (f := G.rotation) (.hub s.left (0 : Fin 3))
    exact s.paired ▸ h
  exact (sameCycle_connected _ _ (G.rotation_sameCycle_hub s.left i (0 : Fin 3))).trans
    (h.trans (sameCycle_connected _ _ (G.rotation_sameCycle_hub s.right (0 : Fin 3) j)))

theorem portSwap_connected (x : G.Dart) : Connected G.pairing.perm G.rotation x (s.portSwap x) := by
  by_cases hl : x = .hub s.left (2 : Fin 3)
  · rw [hl]
    change Connected G.pairing.perm G.rotation _ (swap _ _ _)
    rw [swap_apply_left]
    exact s.rim_ports_connected _ _
  · by_cases hr : x = .hub s.right (2 : Fin 3)
    · rw [hr]
      change Connected G.pairing.perm G.rotation _ (swap _ _ _)
      rw [swap_apply_right]
      exact (s.rim_ports_connected _ _).symm
    · change Connected G.pairing.perm G.rotation x (swap _ _ x)
      rw [swap_apply_of_ne_of_ne hl hr]
      exact Connected.refl _

def switchedSpoke : s.switch.SunSpoke := ⟨s.left, s.right, s.switch_paired⟩

theorem switch_portSwap_connected (x : G.Dart) :
    Connected s.switch.pairing.perm s.switch.rotation x (s.portSwap x) :=
  s.switchedSpoke.portSwap_connected x

theorem switch_connected (x y : G.Dart) :
    Connected s.switch.pairing.perm s.switch.rotation x y ↔ Connected G.pairing.perm G.rotation x y := by
  constructor
  · intro h
    apply h.lift id ⟨Connected.refl, Connected.symm, Connected.trans⟩
    · intro z
      exact (s.portSwap_connected z).trans
        ((Connected.edge (s.portSwap z)).trans (s.portSwap_connected (G.pairing.twin (s.portSwap z))))
    · intro z
      apply sameCycle_connected
      exact (G.rotation_sameCycle_iff z (s.switch.rotation z)).mpr (s.switch.vertex_rotation z).symm
  · intro h
    apply h.lift id ⟨Connected.refl, Connected.symm, Connected.trans⟩
    · intro z
      have hp : Connected s.switch.pairing.perm s.switch.rotation
          (s.portSwap z) (s.portSwap (G.pairing.twin z)) := by
        have h := Connected.edge (p := s.switch.pairing.perm) (f := s.switch.rotation) (s.portSwap z)
        change Connected _ _ _ (s.switch.pairing.twin (s.portSwap z)) at h
        rwa [s.switch_twin_portSwap] at h
      exact (s.switch_portSwap_connected z).trans
        (hp.trans (s.switch_portSwap_connected (G.pairing.twin z)).symm)
    · intro z
      apply sameCycle_connected
      exact (s.switch.rotation_sameCycle_iff z (G.rotation z)).mpr (G.vertex_rotation z).symm

theorem switch_rotation_connected (x y : G.Dart) :
    Connected s.switch.rotation s.switch.pairing.perm x y ↔ Connected G.rotation G.pairing.perm x y :=
  (RotationEuler.connected_swap_iff _ _ x y).trans
    ((s.switch_connected x y).trans (RotationEuler.connected_swap_iff _ _ x y))

theorem switch_circuit_connected (x y : G.Dart) :
    Connected s.switch.pairing.perm s.switch.circuitStep x y ↔
      Connected G.pairing.perm G.circuitStep x y := by
  have hs := RotationEuler.connected_rotation_iff s.switch.rotation s.switch.pairing.perm
    s.switch.pairing.involutive x y
  have ho := RotationEuler.connected_rotation_iff G.rotation G.pairing.perm G.pairing.involutive x y
  rw [s.switch.rotation_mul_pairing] at hs
  rw [G.rotation_mul_pairing] at ho
  exact hs.symm.trans ((s.switch_rotation_connected x y).trans ho)

theorem switch_rotation_component_card :
    Nat.card (Component s.switch.rotation s.switch.pairing.perm) =
      Nat.card (Component G.rotation G.pairing.perm) :=
  Nat.card_congr (componentEquiv _ _ _ _ s.switch_rotation_connected)

theorem switch_rotation_orbit_card : Nat.card (Orbit s.switch.rotation) = Nat.card (Orbit G.rotation) := by
  rw [Nat.card_congr (s.switch.rotationVertexEquiv (fun _ => by change 0 < 3; omega)),
    Nat.card_congr (G.rotationVertexEquiv (fun _ => by change 0 < 3; omega))]

theorem switch_pairing_orbit_card : Nat.card (Orbit s.switch.pairing.perm) = Nat.card (Orbit G.pairing.perm) :=
  (Nat.card_congr (orbitEquiv G.pairing.perm s.switch.pairing.perm s.portSwap s.switch_twin_portSwap)).symm

theorem switch_eulerCount (hf : G.hubFlip s.left = G.hubFlip s.right) :
    eulerCount s.switch.pairing.perm s.switch.circuitStep = eulerCount G.pairing.perm G.circuitStep := by
  unfold eulerCount
  rw [s.switch.circuit_mul_pairing, G.circuit_mul_pairing, s.switch_rotation_orbit_card,
    s.switch_pairing_orbit_card, s.switch_face_card hf]

theorem switch_rotationEuler (hf : G.hubFlip s.left = G.hubFlip s.right) :
    RotationEuler.count s.switch.rotation s.switch.pairing.perm =
      RotationEuler.count G.rotation G.pairing.perm :=
  s.switch.rotationEuler_eq_eulerCount.trans ((s.switch_eulerCount hf).trans G.rotationEuler_eq_eulerCount.symm)

theorem switch_saturated (hf : G.hubFlip s.left = G.hubFlip s.right)
    (hEuler : RotationEuler.count G.rotation G.pairing.perm =
      2 * Nat.card (Component G.rotation G.pairing.perm)) :
    RotationEuler.count s.switch.rotation s.switch.pairing.perm =
      2 * Nat.card (Component s.switch.rotation s.switch.pairing.perm) := by
  rw [s.switch_rotationEuler hf, s.switch_rotation_component_card, hEuler]

end ThomGame.Pictures.PortGraph.SunSpoke

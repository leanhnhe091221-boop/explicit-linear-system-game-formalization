module

public import ThomGame.Pictures.SunRimOrientation
public import ThomGame.Pictures.PairingCycleSwitch
public import ThomGame.Pictures.PairingCycleCounts
public import ThomGame.Pictures.SunMinimalState
public import ThomGame.Pictures.DiagramCircuitSeparation

/-!
# Exact rim-component split and merge counts for actual sun switches

The switched rim walk is conjugate to the proved double target surgery.
Every rim component has two orientations. In a planar same-orientation
sun graph, the selected component therefore splits into two, or the two
selected components merge into one. This counts rim components, not the
spokes contained in their bounded regions.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv FiniteReturn RibbonConnectivity
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  (G : PortGraph (sunPresentation n b) u v) (hn : 3 ≤ n)
  (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)

def SunRimComponent := Component (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm

theorem sunRimWalk_orbit_card : Nat.card (Orbit (G.sunRimWalk hn hu hv)) =
    2 * Nat.card (G.SunRimComponent hn hu hv) :=
  PairingCycles.walk_orbit_card (G.sunRimPairing hn) (G.sunRimVertexPairing hn hu hv)

namespace SunSpoke

variable {G} (s : G.SunSpoke)

theorem switchedWalk_eq_rimSwap :
    PairingCycles.switchedWalk (G.sunRimPairing hn) (G.sunRimVertexPairing hn hu hv)
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true) =
      s.rimSwap hn true * s.rimSwap hn false * G.sunRimWalk hn hu hv := by
  unfold PairingCycles.switchedWalk
  rw [G.sunRimVertexPairing_port, G.sunRimVertexPairing_port]
  rfl

theorem switch_rim_orbit_card : Nat.card (Orbit (s.switch.sunRimWalk hn hu hv)) =
    Nat.card (Orbit (PairingCycles.switchedWalk (G.sunRimPairing hn) (G.sunRimVertexPairing hn hu hv)
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true))) := by
  let f := PairingCycles.switchedWalk (G.sunRimPairing hn) (G.sunRimVertexPairing hn hu hv)
    (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true)
  have hc : ∀ a, s.switchedRimWalk hn hu hv (s.rimSwap hn true a) = s.rimSwap hn true (f a) := by
    intro a
    have he := congrArg (fun r : Perm (G.SunRimDart hn) => r a) (s.switchedWalk_eq_rimSwap hn hu hv)
    change f a = s.rimSwap hn true (s.rimSwap hn false (G.sunRimWalk hn hu hv a)) at he
    exact (s.switch_rimWalk hn hu hv a).trans
      ((s.rimSwap_involutive hn true _).symm.trans (congrArg (s.rimSwap hn true) he.symm))
  exact (Nat.card_congr (orbitEquiv f (s.switchedRimWalk hn hu hv) (s.rimSwap hn true) hc)).symm

theorem rim_component_card_split_of_oriented
    (h : (G.sunRimWalk hn hu hv).SameCycle
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true)) :
    Nat.card (s.switch.SunRimComponent hn hu hv) = Nat.card (G.SunRimComponent hn hu hv) + 1 := by
  have hab : G.sunRimPort hn s.left true ≠ G.sunRimPort hn s.right true := by
    intro he
    exact s.distinct ((G.sun_hub_eq_iff.mp (congrArg Subtype.val he)).1)
  have hc := PairingCycles.switchedWalk_orbit_card_split
    (G.sunRimPairing hn) (G.sunRimVertexPairing hn hu hv) hab h
  have hnew := s.switch.sunRimWalk_orbit_card hn hu hv
  have hold := G.sunRimWalk_orbit_card hn hu hv
  rw [← s.switch_rim_orbit_card hn hu hv] at hc
  change Nat.card (Orbit (s.switch.sunRimWalk hn hu hv)) = Nat.card (Orbit (G.sunRimWalk hn hu hv)) + 2 at hc
  rw [hnew, hold] at hc
  omega

theorem rim_component_card_join
    (h : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true)) :
    Nat.card (s.switch.SunRimComponent hn hu hv) + 1 = Nat.card (G.SunRimComponent hn hu hv) := by
  have hc := PairingCycles.switchedWalk_orbit_card_join
    (G.sunRimPairing hn) (G.sunRimVertexPairing hn hu hv) h
  have hnew := s.switch.sunRimWalk_orbit_card hn hu hv
  have hold := G.sunRimWalk_orbit_card hn hu hv
  rw [← s.switch_rim_orbit_card hn hu hv] at hc
  change Nat.card (Orbit (s.switch.sunRimWalk hn hu hv)) + 2 = Nat.card (Orbit (G.sunRimWalk hn hu hv)) at hc
  rw [hnew, hold] at hc
  omega

theorem rim_component_card_split
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
    (hf : G.hubFlip s.left = G.hubFlip s.right)
    (hc : Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true)) :
    Nat.card (s.switch.SunRimComponent hn hu hv) = Nat.card (G.SunRimComponent hn hu hv) + 1 :=
  s.rim_component_card_split_of_oriented hn hu hv
    (s.rim_connected_same_orientation hn hu hv (G.dualEuler_eq_twice_components hEuler) hf hc)

end SunSpoke

namespace SunMinimalState

variable {w : List (Fin n ⊕ Fin n)} {G : PortGraph (sunPresentation n b) [] w}
  (h : G.SunMinimalState) (hw : ∀ z ∈ w, ∃ j, z = Sum.inl j)

include h in
theorem rim_component_card_switch (s : G.SunSpoke) :
    (Nat.card (s.switch.SunRimComponent hn (by simp) hw) : Int) =
      Nat.card (G.SunRimComponent hn (by simp) hw) +
        if Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn (by simp) hw).perm
          (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true) then 1 else -1 := by
  split_ifs with hc
  · have he := s.rim_component_card_split hn (by simp) hw h.euler (h.same_flip s) hc
    omega
  · have he := s.rim_component_card_join hn (by simp) hw hc
    omega

end SunMinimalState
end ThomGame.Pictures.PortGraph

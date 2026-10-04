module

public import ThomGame.Pictures.SunRimSwitchCounts
public import ThomGame.Pictures.PairingCycleSeparation

/-!
# The selected rim endpoints separate or join under the actual switch

Conjugation by the actual second-port exchange identifies the switched
rim graph with the paired-cycle surgery. We transfer endpoint component
membership, as well as the already proved exact component counts.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SunSpoke

open Equiv RibbonConnectivity
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} (s : G.SunSpoke) (hn : 3 ≤ n)
  (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)

theorem switch_rim_connected_iff (x y : G.SunRimDart hn) :
    Connected (s.switch.sunRimPairing hn).perm (s.switch.sunRimVertexPairing hn hu hv).perm
      (s.rimSwap hn true x) (s.rimSwap hn true y) ↔
    Connected (G.sunRimPairing hn).perm
      (PairingCycles.switchedVertex (G.sunRimVertexPairing hn hu hv)
        (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true)).perm x y := by
  let q := PairingCycles.switchedVertex (G.sunRimVertexPairing hn hu hv)
    (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true)
  have hp : ∀ z, (s.switch.sunRimPairing hn).perm (s.rimSwap hn true z) =
      s.rimSwap hn true ((G.sunRimPairing hn).perm z) := s.switch_rimPairing hn
  have hq : ∀ z, (s.switch.sunRimVertexPairing hn hu hv).perm (s.rimSwap hn true z) =
      s.rimSwap hn true (q.perm z) := by
    intro z
    change (s.switch.sunRimVertexPairing hn hu hv).twin (s.rimSwap hn true z) =
      s.rimSwap hn true (s.rimSwap hn true
        ((G.sunRimVertexPairing hn hu hv).twin (s.rimSwap hn true z)))
    exact (s.switch_rimVertexPairing hn hu hv _).trans (s.rimSwap_involutive hn true _).symm
  exact (connected_congr (G.sunRimPairing hn).perm q.perm
    (s.switch.sunRimPairing hn).perm (s.switch.sunRimVertexPairing hn hu hv).perm
    (s.rimSwap hn true) hp hq x y).symm

theorem switch_rim_separates_of_oriented
    (h : (G.sunRimWalk hn hu hv).SameCycle
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true)) :
    ¬ Connected (s.switch.sunRimPairing hn).perm (s.switch.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true) := by
  have hab : G.sunRimPort hn s.left true ≠ G.sunRimPort hn s.right true := by
    intro he
    exact s.distinct ((G.sun_hub_eq_iff.mp (congrArg Subtype.val he)).1)
  have hs := PairingCycles.switched_separates (G.sunRimPairing hn) (G.sunRimVertexPairing hn hu hv) hab h
  intro hc
  apply hs
  apply (s.switch_rim_connected_iff hn hu hv _ _).mp
  change Connected _ _ (swap _ _ (G.sunRimPort hn s.left true)) (swap _ _ (G.sunRimPort hn s.right true))
  rw [swap_apply_left, swap_apply_right]
  exact hc.symm

theorem switch_rim_joins
    (h : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true)) :
    Connected (s.switch.sunRimPairing hn).perm (s.switch.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true) := by
  have hs := PairingCycles.switched_joins (G.sunRimPairing hn) (G.sunRimVertexPairing hn hu hv) h
  have hc := (s.switch_rim_connected_iff hn hu hv _ _).mpr hs
  change Connected _ _ (swap _ _ (G.sunRimPort hn s.left true)) (swap _ _ (G.sunRimPort hn s.right true)) at hc
  rw [swap_apply_left, swap_apply_right] at hc
  exact hc.symm

theorem switch_rim_separates
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
    (hf : G.hubFlip s.left = G.hubFlip s.right)
    (hc : Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true)) :
    ¬ Connected (s.switch.sunRimPairing hn).perm (s.switch.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true) :=
  s.switch_rim_separates_of_oriented hn hu hv
    (s.rim_connected_same_orientation hn hu hv (G.dualEuler_eq_twice_components hEuler) hf hc)

theorem rimSwap_fixed_of_away {x : G.SunRimDart hn}
    (ha : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      x (G.sunRimPort hn s.left true))
    (hb : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      x (G.sunRimPort hn s.right true)) : s.rimSwap hn true x = x := by
  apply swap_apply_of_ne_of_ne
  · intro he; apply ha; rw [he]; exact Connected.refl _
  · intro he; apply hb; rw [he]; exact Connected.refl _

theorem switch_rim_connected_away {x : G.SunRimDart hn}
    (ha : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      x (G.sunRimPort hn s.left true))
    (hb : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      x (G.sunRimPort hn s.right true)) (y : G.SunRimDart hn) :
    Connected (s.switch.sunRimPairing hn).perm (s.switch.sunRimVertexPairing hn hu hv).perm x y ↔
      Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm x y := by
  have hc := (s.switch_rim_connected_iff hn hu hv x (s.rimSwap hn true y)).trans
    (PairingCycles.switched_connected_away (G.sunRimPairing hn) (G.sunRimVertexPairing hn hu hv)
      ha hb (s.rimSwap hn true y))
  rw [s.rimSwap_fixed_of_away hn hu hv ha hb, s.rimSwap_involutive] at hc
  apply hc.trans
  by_cases hya : y = G.sunRimPort hn s.left true
  · subst y
    change Connected _ _ x (swap _ _ (G.sunRimPort hn s.left true)) ↔ _
    rw [swap_apply_left]
    exact iff_of_false hb ha
  · by_cases hyb : y = G.sunRimPort hn s.right true
    · subst y
      change Connected _ _ x (swap _ _ (G.sunRimPort hn s.right true)) ↔ _
      rw [swap_apply_right]
      exact iff_of_false ha hb
    · change Connected _ _ x (swap _ _ y) ↔ _
      rw [swap_apply_of_ne_of_ne hya hyb]

end ThomGame.Pictures.PortGraph.SunSpoke

namespace ThomGame.Pictures.PortGraph.SunMinimalState

open RibbonConnectivity

variable {n : Nat} {b : Fin n → ZMod 2} {w : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) [] w} (h : G.SunMinimalState) (hn : 3 ≤ n)
  (hw : ∀ z ∈ w, ∃ j, z = Sum.inl j)

include h in
theorem rim_connected_switch_iff (s : G.SunSpoke) :
    Connected (s.switch.sunRimPairing hn).perm (s.switch.sunRimVertexPairing hn (by simp) hw).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true) ↔
      ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn (by simp) hw).perm
        (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true) := by
  constructor
  · intro hs hc
    exact s.switch_rim_separates hn (by simp) hw h.euler (h.same_flip s) hc hs
  · exact s.switch_rim_joins hn (by simp) hw

end ThomGame.Pictures.PortGraph.SunMinimalState

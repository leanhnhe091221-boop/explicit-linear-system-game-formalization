module

public import ThomGame.Pictures.SunSpokeSideDeletion
public import ThomGame.Pictures.SunSelectedRimMasks

/-!
# A same-rim spoke separates its original side into two regions

After switching, the two selected hubs lie on distinct rims. Transport
the deleted-spoke regions by the retained-port correspondence and then
forget all cuts except the new left rim. The two original attachment
regions reach opposite sides of that rim, so they were already distinct.
This uses the actual switched graph and does not choose an outer region.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SunSpoke

open Equiv RibbonConnectivity
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} (s : G.SunSpoke) (hn : 3 ≤ n)
  (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)

noncomputable def leftRimSwitchDeletedPairing : Perm G.Dart :=
  s.switchSpokeDeletedPairing (fun x => ¬ (s.leftRim hn hu hv).Marked x)
    (fun x => not_congr ((s.leftRim hn hu hv).marked_twin_iff x))

theorem leftRim_deleted_connected_iff (hf : G.hubFlip s.left = G.hubFlip s.right)
    (x y : Subtype s.Kept) :
    Connected G.circuitStep (s.leftRimDeletedPairing hn hu hv) x.val y.val ↔
      Connected s.switch.circuitStep (s.leftRimSwitchDeletedPairing hn hu hv)
        (s.portSwap x.val) (s.portSwap y.val) :=
  s.spoke_deleted_connected_iff _ _ hf x y

theorem leftRim_switchDeleted_refines
    (hc : Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true))
    {x y : G.Dart}
    (h : Connected s.switch.circuitStep (s.leftRimSwitchDeletedPairing hn hu hv) x y) :
    Connected s.switch.circuitStep (s.switchedSpoke.leftRim hn hu hv).cutPairing x y := by
  let C := s.switchedSpoke.leftRim hn hu hv
  apply h.lift id ⟨Connected.refl, Connected.symm, Connected.trans⟩ Connected.edge
  intro z
  change Connected s.switch.circuitStep C.cutPairing z
    (s.switchSpokeDeletedPairing _ _ z)
  rw [s.switchSpokeDeletedPairing_apply]
  split_ifs with hz
  · have hm : ¬ C.Marked z := by
      intro hm
      have ho := (s.switch_selected_marked_transport hn hu hv z).mp (Or.inl hm)
      have he := G.sunRimCircuit_marked_iff_of_connected hn hu hv
        (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true) hc (s.portSwap z)
      exact hz.2 (ho.elim id he.mpr)
    rw [← C.cutPairing_of_unmarked z hm]
    exact Connected.circuit z
  · exact Connected.refl z

theorem portSwap_step_spoke_left (hf : G.hubFlip s.left = G.hubFlip s.right) :
    s.portSwap (G.circuitStep (.hub s.left (0 : Fin 3))) =
      if G.hubFlip s.left then .hub s.left (2 : Fin 3) else .hub s.right (1 : Fin 3) := by
  rw [s.step_spoke_left, sun_rotation_hub, ← hf]
  cases hh : G.hubFlip s.left <;>
    simp [portSwap, swap_apply_def, sun_hub_eq_iff, Ne.symm s.distinct]
  decide +kernel

theorem portSwap_step_spoke_right :
    s.portSwap (G.circuitStep (.hub s.right (0 : Fin 3))) =
      if G.hubFlip s.left then .hub s.right (2 : Fin 3) else .hub s.left (1 : Fin 3) := by
  rw [s.step_spoke_right, sun_rotation_hub]
  cases hh : G.hubFlip s.left <;>
    simp [portSwap, swap_apply_def, sun_hub_eq_iff, s.distinct]
  decide +kernel

theorem leftRim_deleted_spoke_separates
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
    (hf : G.hubFlip s.left = G.hubFlip s.right)
    (hc : Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true)) :
    ¬ Connected G.circuitStep (s.leftRimDeletedPairing hn hu hv)
      (.hub s.left (0 : Fin 3)) (.hub s.right (0 : Fin 3)) := by
  let C := s.switchedSpoke.leftRim hn hu hv
  have hsep := s.switch_rim_separates hn hu hv hEuler hf hc
  have haway : ¬ C.OnCircuitVertex (.inr (.inl s.right)) := by
    intro h
    exact hsep ((s.switch.sunRimCircuit_onHub_iff_connected hn hu hv
      (G.sunRimPort hn s.left true) s.right).mp h)
  have hspoke : C.OnSide (G.hubFlip s.left) (.hub s.right (0 : Fin 3)) := by
    have hs := s.switchedSpoke.leftRim_spoke_onSide_right hn hu hv
    change C.OnSide (!s.switch.hubFlip s.left) (.hub s.right (0 : Fin 3)) at hs
    have he : (!s.switch.hubFlip s.left) = G.hubFlip s.left := by
      rw [s.switch_flip_left, Bool.not_not]
    exact (congrArg (fun side => C.OnSide side (.hub s.right (0 : Fin 3))) he).mp hs
  have hright (i : Fin 3) : C.OnSide (G.hubFlip s.left) (.hub s.right i) :=
    (C.onSide_same_vertex (a := .hub s.right (0 : Fin 3)) (b := .hub s.right i)
      haway rfl (G.hubFlip s.left)).mp hspoke
  have hleft1 : C.OnSide true (.hub s.left (1 : Fin 3)) := by
    change Connected s.switch.circuitStep C.cutPairing (.hub s.left (1 : Fin 3)) (C.incoming 0)
    have hi := s.switch.sunRimCircuit_incoming_at_hub hn hu hv
      (G.sunRimPort hn s.left true) 0 s.left true rfl
    change C.incoming 0 = .hub s.left (1 : Fin 3) at hi
    rw [hi]
    exact Connected.refl _
  have hleft2 : C.OnSide false (.hub s.left (2 : Fin 3)) := Connected.refl _
  have hnewEuler : eulerDefect s.switch.pairing.perm s.switch.circuitStep = 0 :=
    s.switch.rotationEuler_saturated_iff.mp
      (s.switch_saturated hf (G.rotationEuler_saturated_iff.mpr hEuler))
  have hdual := s.switch.dualEuler_eq_twice_components hnewEuler
  intro h
  have hret : Connected G.circuitStep (s.leftRimDeletedPairing hn hu hv)
      (G.circuitStep (.hub s.left (0 : Fin 3))) (G.circuitStep (.hub s.right (0 : Fin 3))) :=
    (Connected.edge _).symm.trans (h.trans (Connected.edge _))
  have htrans := (s.leftRim_deleted_connected_iff hn hu hv hf
    ⟨_, s.step_spoke_left_kept⟩ ⟨_, s.step_spoke_right_kept⟩).mp hret
  have hcut := s.leftRim_switchDeleted_refines hn hu hv hc htrans
  rw [s.portSwap_step_spoke_left hf, s.portSwap_step_spoke_right] at hcut
  cases hh : G.hubFlip s.left
  · simp only [hh, Bool.false_eq_true, ite_false] at hcut
    have hr := hright (1 : Fin 3)
    rw [hh] at hr
    have he := C.onSide_unique hdual hr (hcut.trans hleft1)
    cases he
  · simp only [hh, ite_true] at hcut
    have hr := hright (2 : Fin 3)
    rw [hh] at hr
    have he := C.onSide_unique hdual hleft2 (hcut.trans hr)
    cases he

theorem leftRim_deleted_spoke_regions_disjoint
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
    (hf : G.hubFlip s.left = G.hubFlip s.right)
    (hc : Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true)) (x : G.Dart) :
    ¬ (Connected G.circuitStep (s.leftRimDeletedPairing hn hu hv) x (.hub s.left (0 : Fin 3)) ∧
      Connected G.circuitStep (s.leftRimDeletedPairing hn hu hv) x (.hub s.right (0 : Fin 3))) := by
  rintro ⟨hl, hr⟩
  exact s.leftRim_deleted_spoke_separates hn hu hv hEuler hf hc (hl.symm.trans hr)

/-- Cutting the rim and deleting a same-rim spoke increases the total
number of dual regions by exactly two. Other components are included. -/
theorem leftRim_deleted_region_card
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
    (hf : G.hubFlip s.left = G.hubFlip s.right)
    (hc : Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true)) :
    Nat.card (Component G.circuitStep (s.leftRimDeletedPairing hn hu hv)) =
      Nat.card (Component G.circuitStep G.pairing.perm) + 2 := by
  have hfix : s.leftRimDeletedPairing hn hu hv (.hub s.left (0 : Fin 3)) = .hub s.left (0 : Fin 3) :=
    s.spokeDeletedPairing_fixed _ _ _ (fun h => h.1 rfl)
  have hcount := component_card_join_of_fixed G.circuitStep (s.leftRimDeletedPairing hn hu hv)
    hfix (s.leftRim_deleted_spoke_separates hn hu hv hEuler hf hc)
  have hrestore : CycleSurgery.splice (s.leftRimDeletedPairing hn hu hv)
      (.hub s.left (0 : Fin 3)) (.hub s.right (0 : Fin 3)) = (s.leftRim hn hu hv).cutPairing :=
    s.sun_rim_cut_restoration hn hu hv (G.sunRimPort hn s.left true)
  rw [hrestore, (s.leftRim hn hu hv).cut_component_card (G.dualEuler_eq_twice_components hEuler)] at hcount
  exact hcount.symm

end ThomGame.Pictures.PortGraph.SunSpoke

namespace ThomGame.Pictures.PortGraph.SunMinimalState

open RibbonConnectivity

variable {n : Nat} {b : Fin n → ZMod 2} {w : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) [] w} (h : G.SunMinimalState)
  (s : G.SunSpoke) (hn : 3 ≤ n) (hw : ∀ z ∈ w, ∃ j, z = Sum.inl j)

include h in
theorem deleted_spoke_separates
    (hc : Connected (G.sunRimPairing hn).perm
      (G.sunRimVertexPairing hn (by simp) hw).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true)) :
    ¬ Connected G.circuitStep (s.leftRimDeletedPairing hn (by simp) hw)
      (.hub s.left (0 : Fin 3)) (.hub s.right (0 : Fin 3)) :=
  s.leftRim_deleted_spoke_separates hn (by simp) hw h.euler (h.same_flip s) hc

include h in
theorem deleted_region_card
    (hc : Connected (G.sunRimPairing hn).perm
      (G.sunRimVertexPairing hn (by simp) hw).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true)) :
    Nat.card (Component G.circuitStep (s.leftRimDeletedPairing hn (by simp) hw)) =
      Nat.card (Component G.circuitStep G.pairing.perm) + 2 :=
  s.leftRim_deleted_region_card hn (by simp) hw h.euler (h.same_flip s) hc

end ThomGame.Pictures.PortGraph.SunMinimalState

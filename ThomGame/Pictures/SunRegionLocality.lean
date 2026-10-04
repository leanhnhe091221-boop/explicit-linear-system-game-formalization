module

public import ThomGame.Pictures.SunRestoredRegions

/-!
# Region locality when the cut misses the two switched hubs

If the edge mask retains every port at both selected hubs, all six
ports remain connected even with the spoke deleted. Both ways of
restoring that spoke therefore identify an already equal pair of
regions. The actual port exchange acts within this one region.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SunSpoke

open Equiv RibbonConnectivity
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} (s : G.SunSpoke)
  (M : G.Dart → Prop) (hM : ∀ x, M (G.pairing.twin x) ↔ M x)

theorem deleted_connected_rotation (x : G.Dart) (hx : s.Kept x) (hMx : M x) :
    Connected G.circuitStep (s.spokeDeletedPairing M hM) x (G.rotation x) := by
  have ht : Connected G.circuitStep (s.spokeDeletedPairing M hM) x (G.pairing.twin x) := by
    have hc := Connected.circuit (p := G.circuitStep) (f := s.spokeDeletedPairing M hM) x
    rw [s.spokeDeletedPairing_apply, ite_eq_left ⟨hx, hMx⟩] at hc
    exact hc
  have hf := Connected.edge (p := G.circuitStep) (f := s.spokeDeletedPairing M hM) (G.pairing.twin x)
  rw [G.circuitStep_apply, G.pairing.involutive] at hf
  exact ht.trans hf

theorem deleted_hub_connected (h : G.Hub)
    (h₁ : M (.hub h (1 : Fin 3))) (h₂ : M (.hub h (2 : Fin 3))) (i : Fin 3) :
    Connected G.circuitStep (s.spokeDeletedPairing M hM) (.hub h i) (.hub h (0 : Fin 3)) := by
  have hk₁ : s.Kept (.hub h (1 : Fin 3)) := by simp [Kept, sun_hub_eq_iff]
  have hk₂ : s.Kept (.hub h (2 : Fin 3)) := by simp [Kept, sun_hub_eq_iff]
  have hc₁ := s.deleted_connected_rotation M hM _ hk₁ h₁
  have hc₂ := s.deleted_connected_rotation M hM _ hk₂ h₂
  cases hh : G.hubFlip h
  · rw [G.sun_rotation_hub, hh] at hc₁ hc₂
    change Connected G.circuitStep (s.spokeDeletedPairing M hM) (.hub h (1 : Fin 3)) (.hub h (2 : Fin 3)) at hc₁
    change Connected G.circuitStep (s.spokeDeletedPairing M hM) (.hub h (2 : Fin 3)) (.hub h (0 : Fin 3)) at hc₂
    fin_cases i
    · exact Connected.refl _
    · exact hc₁.trans hc₂
    · exact hc₂
  · rw [G.sun_rotation_hub, hh] at hc₁ hc₂
    change Connected G.circuitStep (s.spokeDeletedPairing M hM) (.hub h (1 : Fin 3)) (.hub h (0 : Fin 3)) at hc₁
    change Connected G.circuitStep (s.spokeDeletedPairing M hM) (.hub h (2 : Fin 3)) (.hub h (1 : Fin 3)) at hc₂
    fin_cases i
    · exact Connected.refl _
    · exact hc₁
    · exact hc₂.trans hc₁

variable (hpatch : ∀ i : Fin 3, M (.hub s.left i) ∧ M (.hub s.right i))

include hpatch in
theorem deleted_spoke_connected :
    Connected G.circuitStep (s.spokeDeletedPairing M hM)
      (.hub s.left (0 : Fin 3)) (.hub s.right (0 : Fin 3)) := by
  have hc := Connected.edge (p := G.circuitStep) (f := s.spokeDeletedPairing M hM)
    (.hub s.left (0 : Fin 3))
  rw [s.step_spoke_left, G.sun_rotation_hub] at hc
  exact hc.trans (s.deleted_hub_connected M hM s.right (hpatch 1).2 (hpatch 2).2 _)

include hpatch in
theorem deleted_patch_connected (h k : G.Hub)
    (hh : h = s.left ∨ h = s.right) (hk : k = s.left ∨ k = s.right) (i j : Fin 3) :
    Connected G.circuitStep (s.spokeDeletedPairing M hM) (.hub h i) (.hub k j) := by
  have hl i := s.deleted_hub_connected M hM s.left (hpatch 1).1 (hpatch 2).1 i
  have hr i := s.deleted_hub_connected M hM s.right (hpatch 1).2 (hpatch 2).2 i
  have hs := s.deleted_spoke_connected M hM hpatch
  rcases hh with rfl | rfl <;> rcases hk with rfl | rfl
  · exact (hl i).trans (hl j).symm
  · exact (hl i).trans (hs.trans (hr j).symm)
  · exact (hr i).trans (hs.symm.trans (hl j).symm)
  · exact (hr i).trans (hr j).symm

include hpatch in
theorem deleted_portSwap_connected (x : G.Dart) :
    Connected G.circuitStep (s.spokeDeletedPairing M hM) x (s.portSwap x) := by
  by_cases hl : x = .hub s.left (2 : Fin 3)
  · subst x
    change Connected _ _ _ (swap _ _ _)
    rw [swap_apply_left]
    exact s.deleted_patch_connected M hM hpatch _ _ (Or.inl rfl) (Or.inr rfl) _ _
  by_cases hr : x = .hub s.right (2 : Fin 3)
  · subst x
    change Connected _ _ _ (swap _ _ _)
    rw [swap_apply_right]
    exact s.deleted_patch_connected M hM hpatch _ _ (Or.inr rfl) (Or.inl rfl) _ _
  · change Connected _ _ x (swap _ _ x)
    rw [swap_apply_of_ne_of_ne hl hr]
    exact Connected.refl _

include hpatch in
theorem deleted_to_switch_projection (x : G.Dart) :
    Connected G.circuitStep (s.spokeDeletedPairing M hM) x
      (s.portSwap (MarkedReturn.stepProjection s.switch.circuitStep s.Kept s.switch_step_omitted_kept x).val) := by
  by_cases hx : s.Kept x
  · have he := MarkedReturn.stepProjection_kept s.switch.circuitStep s.Kept
      s.switch_step_omitted_kept (⟨x, hx⟩ : Subtype s.Kept)
    rw [he]
    exact s.deleted_portSwap_connected M hM hpatch x
  · rw [MarkedReturn.stepProjection_omitted _ _ _ x hx]
    apply Connected.trans ?_ (s.deleted_portSwap_connected M hM hpatch _)
    by_cases hl : x = .hub s.left (0 : Fin 3)
    · subst x
      rw [s.switch_step_spoke_left, s.switch.sun_rotation_hub]
      exact s.deleted_patch_connected M hM hpatch _ _ (Or.inl rfl) (Or.inr rfl) _ _
    · have hr : x = .hub s.right (0 : Fin 3) := by
        by_contra hr
        exact hx ⟨hl, hr⟩
      subst x
      rw [s.switch_step_spoke_right, s.switch.sun_rotation_hub]
      exact s.deleted_patch_connected M hM hpatch _ _ (Or.inr rfl) (Or.inl rfl) _ _

include hpatch in
theorem deleted_connected_locality (hf : G.hubFlip s.left = G.hubFlip s.right) (x y : G.Dart) :
    Connected s.switch.circuitStep (s.switchSpokeDeletedPairing M hM) x y ↔
      Connected G.circuitStep (s.spokeDeletedPairing M hM) x y := by
  let px := MarkedReturn.stepProjection s.switch.circuitStep s.Kept s.switch_step_omitted_kept x
  let py := MarkedReturn.stepProjection s.switch.circuitStep s.Kept s.switch_step_omitted_kept y
  have hc := s.spoke_deleted_connected_iff M hM hf (s.keptSwap px) (s.keptSwap py)
  change Connected G.circuitStep (s.spokeDeletedPairing M hM) (s.portSwap px.val) (s.portSwap py.val) ↔
    Connected s.switch.circuitStep (s.switchSpokeDeletedPairing M hM)
      (s.portSwap (s.portSwap px.val)) (s.portSwap (s.portSwap py.val)) at hc
  rw [s.portSwap_involutive px.val, s.portSwap_involutive py.val] at hc
  have hx := MarkedReturn.connected_stepProjection s.switch.circuitStep
    (s.switchSpokeDeletedPairing M hM) s.Kept s.switch_step_omitted_kept x
  have hy := MarkedReturn.connected_stepProjection s.switch.circuitStep
    (s.switchSpokeDeletedPairing M hM) s.Kept s.switch_step_omitted_kept y
  have hx' := s.deleted_to_switch_projection M hM hpatch x
  have hy' := s.deleted_to_switch_projection M hM hpatch y
  constructor
  · intro h
    exact hx'.trans ((hc.mpr (hx.symm.trans (h.trans hy))).trans hy'.symm)
  · intro h
    exact hx.trans ((hc.mp (hx'.symm.trans (h.trans hy'))).trans hy.symm)

include hpatch in
theorem cut_connected_deleted_iff (x y : G.Dart) :
    Connected G.circuitStep (RotationEuler.retainEdges G.pairing.perm M hM) x y ↔
      Connected G.circuitStep (s.spokeDeletedPairing M hM) x y := by
  rw [← s.spoke_restored_pairing M hM (hpatch 0).1]
  have hs := s.deleted_spoke_connected M hM hpatch
  have ha := s.spokeDeletedPairing_fixed M hM (.hub s.left (0 : Fin 3)) (fun h => h.1 rfl)
  rw [connected_splice_iff_of_seam G.circuitStep (s.spokeDeletedPairing M hM)
    (seam_of_fixed _ _ ha)]
  constructor
  · rintro (h | ⟨hx, hy⟩ | ⟨hx, hy⟩)
    · exact h
    · exact hx.trans (hs.trans hy.symm)
    · exact hx.trans (hs.symm.trans hy.symm)
  · exact Or.inl

include hpatch in
theorem cut_connected_locality (hf : G.hubFlip s.left = G.hubFlip s.right) (x y : G.Dart) :
    Connected s.switch.circuitStep
        (RotationEuler.retainEdges s.switch.pairing.perm (fun z => M (s.portSwap z))
          (s.switch_mask_invariant M hM)) x y ↔
      Connected G.circuitStep (RotationEuler.retainEdges G.pairing.perm M hM) x y := by
  rw [← s.switch_spoke_restored_pairing M hM (hpatch 0).1,
    s.cut_connected_deleted_iff M hM hpatch]
  have hs := (s.deleted_connected_locality M hM hpatch hf _ _).mpr
    (s.deleted_spoke_connected M hM hpatch)
  have ha := s.switchSpokeDeletedPairing_fixed M hM (.hub s.left (0 : Fin 3)) (fun h => h.1 rfl)
  rw [connected_splice_iff_of_seam s.switch.circuitStep (s.switchSpokeDeletedPairing M hM)
    (seam_of_fixed _ _ ha)]
  constructor
  · rintro (h | ⟨hx, hy⟩ | ⟨hx, hy⟩)
    · exact (s.deleted_connected_locality M hM hpatch hf x y).mp h
    · exact (s.deleted_connected_locality M hM hpatch hf x y).mp (hx.trans (hs.trans hy.symm))
    · exact (s.deleted_connected_locality M hM hpatch hf x y).mp (hx.trans (hs.symm.trans hy.symm))
  · exact fun h => Or.inl ((s.deleted_connected_locality M hM hpatch hf x y).mpr h)

end ThomGame.Pictures.PortGraph.SunSpoke

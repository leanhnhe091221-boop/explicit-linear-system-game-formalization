module

public import ThomGame.Pictures.SunDeletedRegions
public import ThomGame.Pictures.RetainedEdgeReconnection

/-!
# Restoring the spoke identifies two explicitly specified regions

Both original and switched cut dual graphs are described in terms of
the original deleted-spoke regions. Restoring the spoke merges exactly
the regions of its two face successors. After switching, their original
region representatives are obtained by the inverse port exchange.
The formulas retain all three possibilities for a path, including when
the two attachment regions were already equal.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SunSpoke

open Equiv RibbonConnectivity
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} (s : G.SunSpoke)
  (M : G.Dart → Prop) (hM : ∀ x, M (G.pairing.twin x) ↔ M x)

theorem spoke_restored_pairing (hMa : M (.hub s.left (0 : Fin 3))) :
    CycleSurgery.splice (s.spokeDeletedPairing M hM)
      (.hub s.left (0 : Fin 3)) (.hub s.right (0 : Fin 3)) =
      RotationEuler.retainEdges G.pairing.perm M hM :=
  RotationEuler.restore_deleted_pair G.pairing.perm M hM _ _ s.paired s.paired_right hMa
    (s.spokeDeletedPairing M hM) (fun x => by
      rw [s.spokeDeletedPairing_apply]
      split_ifs <;> simp_all [Kept, Pairing.perm]
      rfl)

theorem switch_spoke_restored_pairing (hMa : M (.hub s.left (0 : Fin 3))) :
    CycleSurgery.splice (s.switchSpokeDeletedPairing M hM)
      (.hub s.left (0 : Fin 3)) (.hub s.right (0 : Fin 3)) =
      RotationEuler.retainEdges s.switch.pairing.perm (fun x => M (s.portSwap x))
        (s.switch_mask_invariant M hM) := by
  have hMa' : M (s.portSwap (.hub s.left (0 : Fin 3))) :=
    (congrArg M s.portSwap_spoke_left).mpr hMa
  exact RotationEuler.restore_deleted_pair s.switch.pairing.perm (fun x => M (s.portSwap x))
    (s.switch_mask_invariant M hM) _ _ s.switch_paired s.switch_paired_right hMa'
    (s.switchSpokeDeletedPairing M hM) (fun x => by
      rw [s.switchSpokeDeletedPairing_apply]
      split_ifs <;> simp_all [Kept, Pairing.perm]
      rfl)

theorem spoke_restored_connected_iff (hMa : M (.hub s.left (0 : Fin 3))) (x y : G.Dart) :
    Connected G.circuitStep (RotationEuler.retainEdges G.pairing.perm M hM) x y ↔
      Connected G.circuitStep (s.spokeDeletedPairing M hM) x y ∨
      (Connected G.circuitStep (s.spokeDeletedPairing M hM) x
          (G.circuitStep (.hub s.left (0 : Fin 3))) ∧
        Connected G.circuitStep (s.spokeDeletedPairing M hM) y
          (G.circuitStep (.hub s.right (0 : Fin 3)))) ∨
      (Connected G.circuitStep (s.spokeDeletedPairing M hM) x
          (G.circuitStep (.hub s.right (0 : Fin 3))) ∧
        Connected G.circuitStep (s.spokeDeletedPairing M hM) y
          (G.circuitStep (.hub s.left (0 : Fin 3)))) :=
  RotationEuler.restored_connected_return_iff G.pairing.perm M hM _ _ s.paired s.paired_right hMa
    (s.spokeDeletedPairing M hM) (fun z => by
      rw [s.spokeDeletedPairing_apply]
      split_ifs <;> simp_all [Kept, Pairing.perm]
      rfl) G.circuitStep x y

theorem deleted_connected_switch_attachment_iff (hf : G.hubFlip s.left = G.hubFlip s.right)
    (x : Subtype s.Kept) (z : G.Dart) (hz : s.Kept (s.switch.circuitStep z)) :
    Connected s.switch.circuitStep (s.switchSpokeDeletedPairing M hM)
        (s.portSwap x.val) (s.switch.circuitStep z) ↔
      Connected G.circuitStep (s.spokeDeletedPairing M hM)
        x.val (s.portSwap (s.switch.circuitStep z)) := by
  let y : Subtype s.Kept := ⟨s.portSwap (s.switch.circuitStep z), (s.portSwap_kept_iff _).mpr hz⟩
  have hc := s.spoke_deleted_connected_iff M hM hf x y
  change Connected G.circuitStep (s.spokeDeletedPairing M hM)
      x.val (s.portSwap (s.switch.circuitStep z)) ↔
    Connected s.switch.circuitStep (s.switchSpokeDeletedPairing M hM)
      (s.portSwap x.val) (s.portSwap (s.portSwap (s.switch.circuitStep z))) at hc
  rw [s.portSwap_involutive (s.switch.circuitStep z)] at hc
  exact hc.symm

/-- The switched regions are obtained from the old deleted-spoke regions
by identifying the two specified switched attachment classes. -/
theorem switch_spoke_restored_connected_iff (hf : G.hubFlip s.left = G.hubFlip s.right)
    (hMa : M (.hub s.left (0 : Fin 3))) (x y : Subtype s.Kept) :
    Connected s.switch.circuitStep
        (RotationEuler.retainEdges s.switch.pairing.perm (fun z => M (s.portSwap z))
          (s.switch_mask_invariant M hM)) (s.portSwap x.val) (s.portSwap y.val) ↔
      Connected G.circuitStep (s.spokeDeletedPairing M hM) x.val y.val ∨
      (Connected G.circuitStep (s.spokeDeletedPairing M hM) x.val
          (s.portSwap (s.switch.circuitStep (.hub s.left (0 : Fin 3)))) ∧
        Connected G.circuitStep (s.spokeDeletedPairing M hM) y.val
          (s.portSwap (s.switch.circuitStep (.hub s.right (0 : Fin 3))))) ∨
      (Connected G.circuitStep (s.spokeDeletedPairing M hM) x.val
          (s.portSwap (s.switch.circuitStep (.hub s.right (0 : Fin 3)))) ∧
        Connected G.circuitStep (s.spokeDeletedPairing M hM) y.val
          (s.portSwap (s.switch.circuitStep (.hub s.left (0 : Fin 3))))) := by
  have hMa' : M (s.portSwap (.hub s.left (0 : Fin 3))) :=
    (congrArg M s.portSwap_spoke_left).mpr hMa
  rw [RotationEuler.restored_connected_return_iff s.switch.pairing.perm (fun z => M (s.portSwap z))
    (s.switch_mask_invariant M hM) _ _ s.switch_paired s.switch_paired_right hMa'
    (s.switchSpokeDeletedPairing M hM) (fun z => by
      rw [s.switchSpokeDeletedPairing_apply]
      split_ifs <;> simp_all [Kept, Pairing.perm]
      rfl)]
  rw [← s.spoke_deleted_connected_iff M hM hf x y,
    s.deleted_connected_switch_attachment_iff M hM hf x _ s.switch_step_spoke_left_kept,
    s.deleted_connected_switch_attachment_iff M hM hf y _ s.switch_step_spoke_right_kept,
    s.deleted_connected_switch_attachment_iff M hM hf x _ s.switch_step_spoke_right_kept,
    s.deleted_connected_switch_attachment_iff M hM hf y _ s.switch_step_spoke_left_kept]

end ThomGame.Pictures.PortGraph.SunSpoke

module

public import ThomGame.Pictures.SunSwitchReturn
public import ThomGame.Pictures.ReturnConnectivity
public import ThomGame.Pictures.EdgeDeletionEuler
public import ThomGame.Pictures.ComponentTransport

/-!
# Dual regions after deleting the switched spoke

An arbitrary pairing-invariant mask specifies which edges may be crossed.
The selected spoke is additionally deleted. Transporting the mask by the
actual port exchange gives the corresponding cut dual graph after surgery.
Their retained face returns and edge permutations are conjugate, hence
their full component quotients are equivalent. No choice of an outer
region or assertion about the restored spoke is made here.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SunSpoke

open Equiv RibbonConnectivity
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} (s : G.SunSpoke)

theorem twin_kept_iff (x : G.Dart) : s.Kept (G.pairing.twin x) ↔ s.Kept x :=
  ⟨fun h => (congrArg s.Kept (G.pairing.involutive x)).mp (s.twin_kept h), s.twin_kept⟩

theorem switch_twin_kept_iff (x : G.Dart) : s.Kept (s.switch.pairing.twin x) ↔ s.Kept x := by
  rw [s.switch_twin, s.portSwap_kept_iff, s.twin_kept_iff, s.portSwap_kept_iff]

theorem step_omitted_kept (x : G.Dart) (hx : ¬ s.Kept x) : s.Kept (G.circuitStep x) := by
  by_cases hl : x = .hub s.left (0 : Fin 3)
  · subst x
    exact s.step_spoke_left_kept
  · have hr : x = .hub s.right (0 : Fin 3) := by
      by_contra hr
      exact hx ⟨hl, hr⟩
    subst x
    exact s.step_spoke_right_kept

theorem switch_step_omitted_kept (x : G.Dart) (hx : ¬ s.Kept x) :
    s.Kept (s.switch.circuitStep x) := by
  by_cases hl : x = .hub s.left (0 : Fin 3)
  · subst x
    exact s.switch_step_spoke_left_kept
  · have hr : x = .hub s.right (0 : Fin 3) := by
      by_contra hr
      exact hx ⟨hl, hr⟩
    subst x
    exact s.switch_step_spoke_right_kept

variable (M : G.Dart → Prop) (hM : ∀ x, M (G.pairing.twin x) ↔ M x)

/-- Delete the selected spoke and every edge not retained by the mask. -/
noncomputable def spokeDeletedPairing : Perm G.Dart :=
  RotationEuler.retainEdges G.pairing.perm (fun x => s.Kept x ∧ M x)
    (fun x => and_congr (s.twin_kept_iff x) (hM x))

include hM in
theorem switch_mask_invariant (x : G.Dart) :
    M (s.portSwap (s.switch.pairing.twin x)) ↔ M (s.portSwap x) := by
  rw [s.switch_twin, s.portSwap_involutive]
  exact hM (s.portSwap x)

/-- The same deleted edges, transported by the actual switch. -/
noncomputable def switchSpokeDeletedPairing : Perm G.Dart :=
  RotationEuler.retainEdges s.switch.pairing.perm (fun x => s.Kept x ∧ M (s.portSwap x))
    (fun x => and_congr (s.switch_twin_kept_iff x) (s.switch_mask_invariant M hM x))

theorem spokeDeletedPairing_apply (x : G.Dart) :
    s.spokeDeletedPairing M hM x = if s.Kept x ∧ M x then G.pairing.twin x else x := by
  by_cases hx : s.Kept x ∧ M x
  · simp only [spokeDeletedPairing, RotationEuler.retainEdges_apply, hx]
    rfl
  · simp only [spokeDeletedPairing, RotationEuler.retainEdges_apply, hx, ite_false]

theorem switchSpokeDeletedPairing_apply (x : G.Dart) :
    s.switchSpokeDeletedPairing M hM x =
      if s.Kept x ∧ M (s.portSwap x) then s.switch.pairing.twin x else x := by
  by_cases hx : s.Kept x ∧ M (s.portSwap x)
  · simp only [switchSpokeDeletedPairing, RotationEuler.retainEdges_apply, hx]
    rfl
  · simp only [switchSpokeDeletedPairing, RotationEuler.retainEdges_apply, hx, ite_false]

theorem spokeDeletedPairing_kept (x : G.Dart) :
    s.Kept (s.spokeDeletedPairing M hM x) ↔ s.Kept x := by
  rw [s.spokeDeletedPairing_apply]
  split_ifs
  · exact s.twin_kept_iff x
  · rfl

theorem switchSpokeDeletedPairing_kept (x : G.Dart) :
    s.Kept (s.switchSpokeDeletedPairing M hM x) ↔ s.Kept x := by
  rw [s.switchSpokeDeletedPairing_apply]
  split_ifs
  · exact s.switch_twin_kept_iff x
  · rfl

theorem spokeDeletedPairing_fixed (x : G.Dart) (hx : ¬ s.Kept x) :
    s.spokeDeletedPairing M hM x = x := by
  simp only [s.spokeDeletedPairing_apply, hx, false_and, ite_false]

theorem switchSpokeDeletedPairing_fixed (x : G.Dart) (hx : ¬ s.Kept x) :
    s.switchSpokeDeletedPairing M hM x = x := by
  simp only [s.switchSpokeDeletedPairing_apply, hx, false_and, ite_false]

theorem spokeDeletedPairing_congr (x : G.Dart) :
    s.switchSpokeDeletedPairing M hM (s.portSwap x) =
      s.portSwap (s.spokeDeletedPairing M hM x) := by
  rw [s.switchSpokeDeletedPairing_apply, s.spokeDeletedPairing_apply]
  rw [s.portSwap_involutive x, s.portSwap_kept_iff x]
  split_ifs
  · exact s.switch_twin_portSwap x
  · rfl

theorem spokeDeletedPairing_subtype_congr (x : Subtype s.Kept) :
    (s.switchSpokeDeletedPairing M hM).subtypePerm
        (s.switchSpokeDeletedPairing_kept M hM) (s.keptSwap x) =
      s.keptSwap ((s.spokeDeletedPairing M hM).subtypePerm (s.spokeDeletedPairing_kept M hM) x) :=
  Subtype.ext (s.spokeDeletedPairing_congr M hM x.val)

/-- The retained ports represent exactly corresponding deleted-spoke regions. -/
theorem spoke_deleted_connected_iff (hf : G.hubFlip s.left = G.hubFlip s.right)
    (x y : Subtype s.Kept) :
    Connected G.circuitStep (s.spokeDeletedPairing M hM) x.val y.val ↔
      Connected s.switch.circuitStep (s.switchSpokeDeletedPairing M hM)
        (s.portSwap x.val) (s.portSwap y.val) := by
  rw [← MarkedReturn.connected_return_iff G.circuitStep (s.spokeDeletedPairing M hM)
    s.Kept (s.spokeDeletedPairing_kept M hM) (s.spokeDeletedPairing_fixed M hM) s.step_omitted_kept]
  have hc := connected_congr (MarkedReturn.perm G.circuitStep s.Kept)
    ((s.spokeDeletedPairing M hM).subtypePerm (s.spokeDeletedPairing_kept M hM))
    (MarkedReturn.perm s.switch.circuitStep s.Kept)
    ((s.switchSpokeDeletedPairing M hM).subtypePerm (s.switchSpokeDeletedPairing_kept M hM))
    s.keptSwap (s.return_congr hf) (s.spokeDeletedPairing_subtype_congr M hM) x y
  exact hc.trans (MarkedReturn.connected_return_iff s.switch.circuitStep
    (s.switchSpokeDeletedPairing M hM) s.Kept (s.switchSpokeDeletedPairing_kept M hM)
    (s.switchSpokeDeletedPairing_fixed M hM) s.switch_step_omitted_kept (s.keptSwap x) (s.keptSwap y))

/-- Every full dual component has a retained representative, on both sides. -/
noncomputable def spokeDeletedRegionEquiv (hf : G.hubFlip s.left = G.hubFlip s.right) :
    Component G.circuitStep (s.spokeDeletedPairing M hM) ≃
      Component s.switch.circuitStep (s.switchSpokeDeletedPairing M hM) :=
  (MarkedReturn.returnComponentEquiv G.circuitStep (s.spokeDeletedPairing M hM) s.Kept
    (s.spokeDeletedPairing_kept M hM) (s.spokeDeletedPairing_fixed M hM) s.step_omitted_kept).symm.trans
  ((componentCongrEquiv (MarkedReturn.perm G.circuitStep s.Kept)
    ((s.spokeDeletedPairing M hM).subtypePerm (s.spokeDeletedPairing_kept M hM))
    (MarkedReturn.perm s.switch.circuitStep s.Kept)
    ((s.switchSpokeDeletedPairing M hM).subtypePerm (s.switchSpokeDeletedPairing_kept M hM))
    s.keptSwap (s.return_congr hf) (s.spokeDeletedPairing_subtype_congr M hM)).trans
  (MarkedReturn.returnComponentEquiv s.switch.circuitStep (s.switchSpokeDeletedPairing M hM) s.Kept
    (s.switchSpokeDeletedPairing_kept M hM) (s.switchSpokeDeletedPairing_fixed M hM)
    s.switch_step_omitted_kept))

theorem spoke_deleted_region_card (hf : G.hubFlip s.left = G.hubFlip s.right) :
    Nat.card (Component G.circuitStep (s.spokeDeletedPairing M hM)) =
      Nat.card (Component s.switch.circuitStep (s.switchSpokeDeletedPairing M hM)) :=
  Nat.card_congr (s.spokeDeletedRegionEquiv M hM hf)

end ThomGame.Pictures.PortGraph.SunSpoke

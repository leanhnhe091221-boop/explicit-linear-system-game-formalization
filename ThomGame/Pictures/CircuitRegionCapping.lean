module

public import ThomGame.Pictures.CircuitRegionEuler
public import ThomGame.Pictures.CircuitSectorEuler
public import ThomGame.Pictures.SlotErasureEuler
public import ThomGame.Pictures.BoundarySwapGraph
public import ThomGame.Pictures.OpenGraphBlocks

/-!
# The actual region has a saturated cap in its correct boundary direction

The frontier word follows the twisted sector rotation. Consequently the
region's stored top boundary has the reverse of the usual top convention.
Exchanging its boundary names places it on the bottom, where the standard
cap follows that sector rotation. Deleting marked circuit slots by first
return gives exactly this capped region, with the original pairing and
all interior rotations. Its saturation is proved by that port equivalence.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity MarkedReturn
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S}

theorem boundaryCyclic_bottom {w : List S} (i : Fin w.length) :
    boundaryCyclic [] w (.inr i) = .inr ((finRotate _).symm i) := by
  apply (boundaryOrderIndex [] w).injective
  rw [boundaryCyclic_index]
  change finRotate _ (Fin.natAdd 0 i.rev) = Fin.natAdd 0 (((finRotate _).symm i).rev)
  rw [rev_finRotate_symm]
  apply Fin.ext
  simp [finRotate_apply, Fin.add_def]

theorem boundaryCyclic_symm_bottom {w : List S} (i : Fin w.length) :
    (boundaryCyclic [] w).symm (.inr i) = .inr (finRotate _ i) := by
  apply (boundaryCyclic [] w).injective
  rw [Equiv.apply_symm_apply, boundaryCyclic_bottom, Equiv.symm_apply_apply]

theorem cappedRotation_bottom {w : List S} (G : PortGraph P [] w) (i : Fin w.length) :
    G.cappedRotation (.bottom i) = .bottom (finRotate _ i) := by
  change G.cappingTargets (G.boundaryDart (.inr i)) = _
  rw [G.cappingTargets_boundary, boundaryCyclic_symm_bottom]
  rfl

namespace SimpleCircuit

variable {G : PortGraph P [] []} (C : G.SimpleCircuit)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (Component G.circuitStep G.pairing.perm))

theorem keptDart_cutPairing_iff (s : Bool) (a : G.Dart) :
    C.KeptDart s (C.cutPairing a) ↔ C.KeptDart s a := by
  by_cases hm : C.Marked a
  · rw [C.cutPairing_of_marked hm]
  · rw [C.cutPairing_of_unmarked _ hm]
    exact C.keptDart_twin_iff s a

noncomputable def regionCappedRotation (s : Bool) : Perm (Subtype (C.KeptDart s)) :=
  perm (C.edgeTwist * G.rotation) (C.KeptDart s)

include hEuler in
theorem regionCappedRotation_saturated (s : Bool) :
    RotationEuler.count (C.regionCappedRotation s) (C.keptPairing s).perm =
      2 * Nat.card (Component (C.regionCappedRotation s) (C.keptPairing s).perm) := by
  have ht : C.cutPairing.subtypePerm (C.keptDart_cutPairing_iff s) = (C.keptPairing s).perm := by
    ext x
    exact C.cutPairing_of_unmarked x.val x.property.1
  have he := RotationEuler.firstReturnRotation_saturated (C.edgeTwist * G.rotation)
    (C.KeptDart s) C.cutPairing (C.keptDart_cutPairing_iff s) C.cutPairing_involutive
    (C.twisted_cut_saturated hEuler)
  rwa [ht] at he

include hEuler in
theorem regionCappedRotation_boundary (s : Bool) (i : Fin (C.frontierWord s).length) :
    (C.regionCappedRotation s (C.regionPorts hEuler s (.top i))).val =
      (C.boundaryEnumeration s (finRotate _ i)).val := by
  have hp := hit_perm (C.edgeTwist * G.rotation) (C.Frontier s) (C.boundaryEnumeration s i)
  rw [C.boundaryEnumeration_return] at hp
  have hw : ∀ {a b : G.Dart}, Hit (C.edgeTwist * G.rotation) (C.Frontier s) a b →
      C.Sector (!s) a → Hit (C.edgeTwist * G.rotation) (C.KeptDart s) a b := by
    intro a b h
    induction h with
    | direct a => exact fun _ => Hit.direct _
    | skip a hn tail ih =>
      intro ha
      have hnext := C.sector_next ha
      exact Hit.skip _ (fun hk => hn ⟨hnext, hk.1⟩) (ih hnext)
  exact (eq_perm_of_hit (C.edgeTwist * G.rotation) (C.KeptDart s)
    (C.regionPorts hEuler s (.top i))
    (((C.frontier_iff hEuler s _).mp (C.boundaryEnumeration s (finRotate _ i)).property).2)
    (hw hp (C.boundaryEnumeration s i).property.1)).symm

theorem regionCappedRotation_interior (s : Bool) (a : Subtype (C.KeptDart s))
    (ha : ¬ C.OnCircuitVertex a.val.vertex) :
    (C.regionCappedRotation s a).val = G.rotation a.val := by
  have hi : C.InteriorVertex s a.val.vertex := ⟨ha, a.val, rfl, a.property.2⟩
  have hr := C.twisted_rotation_interior hi
  have hk : C.KeptDart s ((C.edgeTwist * G.rotation) a.val) := by
    rw [hr]
    exact C.interior_port_kept s hi (G.rotation a.val) (G.vertex_rotation a.val)
  exact (perm_val_of_step _ _ a hk).trans hr

noncomputable def regionCappedPorts (s : Bool) :
    (C.regionGraph hEuler s).swapBoundary.Dart ≃ Subtype (C.KeptDart s) :=
  (C.regionGraph hEuler s).swapBoundaryPorts.symm.trans (C.regionPorts hEuler s)

include hEuler in
theorem regionCappedPorts_swap (s : Bool) (a : (C.regionGraph hEuler s).Dart) :
    C.regionCappedPorts hEuler s ((C.regionGraph hEuler s).swapBoundaryPorts a) =
      C.regionPorts hEuler s a := by
  change C.regionPorts hEuler s ((C.regionGraph hEuler s).swapBoundaryPorts.symm
    ((C.regionGraph hEuler s).swapBoundaryPorts a)) = _
  rw [Equiv.symm_apply_apply]

include hEuler in
theorem regionCappedPorts_pairing (s : Bool) (a : (C.regionGraph hEuler s).swapBoundary.Dart) :
    (C.keptPairing s).perm (C.regionCappedPorts hEuler s a) =
      C.regionCappedPorts hEuler s ((C.regionGraph hEuler s).swapBoundary.pairing.perm a) := by
  obtain ⟨a, rfl⟩ := (C.regionGraph hEuler s).swapBoundaryPorts.surjective a
  rw [(C.regionGraph hEuler s).swapBoundary_pairing, C.regionCappedPorts_swap, C.regionCappedPorts_swap]
  exact C.regionPorts_pairing hEuler s a

include hEuler in
theorem regionCappedPorts_rotation (s : Bool) (a : (C.regionGraph hEuler s).swapBoundary.Dart) :
    C.regionCappedRotation s (C.regionCappedPorts hEuler s a) =
      C.regionCappedPorts hEuler s ((C.regionGraph hEuler s).swapBoundary.cappedRotation a) := by
  apply Subtype.ext
  cases a with
  | top i => exact i.elim0
  | bottom i =>
    rw [cappedRotation_bottom]
    exact C.regionCappedRotation_boundary hEuler s i
  | hub h i =>
    have hh : (C.regionGraph hEuler s).swapBoundary.cappedRotation (.hub h i) =
        .hub h ((C.regionGraph hEuler s).swapBoundary.hubRotation h i) :=
      (C.regionGraph hEuler s).swapBoundary.cappingTargets_unmarked
        (.hub h ((C.regionGraph hEuler s).swapBoundary.hubRotation h i)) id
    rw [hh]
    exact C.regionCappedRotation_interior s _ h.property.1
  | joint j b =>
    have hj : (C.regionGraph hEuler s).swapBoundary.cappedRotation (.joint j b) =
        .joint j (!b) :=
      (C.regionGraph hEuler s).swapBoundary.cappingTargets_unmarked (.joint j (!b)) id
    rw [hj]
    exact C.regionCappedRotation_interior s _ j.property.1

include hEuler in
theorem regionGraph_swapBoundary_capped_saturated (s : Bool) :
    RotationEuler.count (C.regionGraph hEuler s).swapBoundary.cappedRotation
      (C.regionGraph hEuler s).swapBoundary.pairing.perm =
      2 * Nat.card (Component (C.regionGraph hEuler s).swapBoundary.cappedRotation
        (C.regionGraph hEuler s).swapBoundary.pairing.perm) := by
  rw [RotationEuler.count_congr _ _ _ _ (C.regionCappedPorts hEuler s)
    (C.regionCappedPorts_rotation hEuler s) (C.regionCappedPorts_pairing hEuler s),
    Nat.card_congr (componentCongrEquiv _ _ _ _ (C.regionCappedPorts hEuler s)
      (C.regionCappedPorts_rotation hEuler s) (C.regionCappedPorts_pairing hEuler s))]
  exact C.regionCappedRotation_saturated hEuler s

end SimpleCircuit
end ThomGame.Pictures.PortGraph

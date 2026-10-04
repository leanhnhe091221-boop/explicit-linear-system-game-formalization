module

public import ThomGame.Pictures.CircuitGermConnectivity
public import ThomGame.Pictures.InvariantEuler

/-!
# Euler-saturating capped sectors of an actual circuit

The twisted rotation merges the circuit vertices into its two sector
orbits. Cut circuit ports are fixed by the edge involution. Selecting a
cut side after edge reversal retains exactly one sector and its interior
vertices. This is the permutation map used to cap a region; no boundary
or connectivity premise about the region is assumed.
-/

@[expose] public section
namespace ThomGame.Pictures

open Equiv RibbonConnectivity

namespace RotationEuler

variable {D : Type*} [Finite D] (r t : Perm D)

theorem left_dual_saturated (ht : Function.Involutive t)
    (hEuler : count r t = 2 * Nat.card (Component r t)) :
    count (t * r) t = 2 * Nat.card (Component (t * r) t) := by
  have he := count_congr (r * t) t (t * r) t t (fun _ => rfl) (fun _ => rfl)
  have hc := Nat.card_congr
    (componentCongrEquiv (r * t) t (t * r) t t (fun _ => rfl) (fun _ => rfl))
  rw [← he, ← hc, dual_count r t ht,
    ← Nat.card_congr (dualComponentEquiv r t ht)]
  exact hEuler

end RotationEuler

namespace PortGraph.SimpleCircuit

open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []}
    (C : G.SimpleCircuit)

def CappedSide (s : Bool) (a : G.Dart) : Prop := C.OnSide s (G.pairing.twin a)

theorem cutPairing_twin (a : G.Dart) :
    C.cutPairing (G.pairing.perm a) = G.pairing.perm (C.cutPairing a) := by
  change C.edgeTwist (G.pairing.twin (G.pairing.twin a)) =
    G.pairing.twin (C.edgeTwist (G.pairing.twin a))
  exact C.edgeTwist_twin (G.pairing.twin a)

theorem cappedSide_rotation_iff (s : Bool) (a : G.Dart) :
    C.CappedSide s ((C.edgeTwist * G.rotation) a) ↔ C.CappedSide s a := by
  change C.OnSide s (G.pairing.perm ((C.edgeTwist * G.rotation) a)) ↔ _
  rw [← C.cutFace_conjugate, Perm.mul_apply, C.onSide_cutPairing_iff,
    C.onSide_circuitStep_iff]
  rfl

theorem cappedSide_pairing_iff (s : Bool) (a : G.Dart) :
    C.CappedSide s (C.cutPairing a) ↔ C.CappedSide s a := by
  change C.OnSide s (G.pairing.perm (C.cutPairing a)) ↔ _
  rw [← C.cutPairing_twin, C.onSide_cutPairing_iff]
  rfl

theorem cappedSide_iff_onSide {a : G.Dart} (ha : ¬ C.Marked a) (s : Bool) :
    C.CappedSide s a ↔ C.OnSide s a := C.onSide_twin_iff ha s

theorem sector_cappedSide {a : G.Dart} {s : Bool} (ha : C.Sector (!s) a) :
    C.CappedSide s a := by
  change C.OnSide s (G.pairing.twin a)
  simpa only [Bool.not_not] using C.sector_onSide_twin ha

theorem interior_cappedSide {a : G.Dart} {s : Bool} (ha : C.InteriorVertex s a.vertex) :
    C.CappedSide s a := by
  have hk := C.interior_port_kept s ha a rfl
  exact (C.cappedSide_iff_onSide hk.1 s).mpr hk.2

theorem cutPairing_fixed_iff (a : G.Dart) : C.cutPairing a = a ↔ C.Marked a := by
  constructor
  · intro he
    by_contra hn
    rw [C.cutPairing_of_unmarked a hn] at he
    exact G.pairing.ne_self a he
  · exact C.cutPairing_of_marked

theorem twisted_rotation_interior {a : G.Dart} {s : Bool}
    (ha : C.InteriorVertex s a.vertex) : (C.edgeTwist * G.rotation) a = G.rotation a := by
  apply C.edgeTwist_of_unmarked
  intro hm
  have hv := C.marked_onCircuitVertex hm
  rw [G.vertex_rotation] at hv
  exact ha.1 hv

variable (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
  2 * Nat.card (Component G.circuitStep G.pairing.perm))

include hEuler in
theorem cappedSide_sector_iff {a : G.Dart} (hv : C.OnCircuitVertex a.vertex) (s : Bool) :
    C.CappedSide s a ↔ C.Sector (!s) a := by
  constructor
  · intro ha
    obtain ⟨t, ht⟩ := (C.onCircuitVertex_iff_sector a).mp hv
    have he := C.onSide_unique hEuler ha (C.sector_onSide_twin ht)
    have hst : (!s) = t := by simpa only [Bool.not_not] using congrArg Bool.not he
    rw [hst]
    exact ht
  · exact C.sector_cappedSide

include hEuler in
theorem cappedSide_cases {a : G.Dart} {s : Bool} (ha : C.CappedSide s a) :
    C.Sector (!s) a ∨ C.InteriorVertex s a.vertex := by
  by_cases hv : C.OnCircuitVertex a.vertex
  · exact Or.inl ((C.cappedSide_sector_iff hEuler hv s).mp ha)
  · have hm : ¬ C.Marked a := fun h => hv (C.marked_onCircuitVertex h)
    exact Or.inr ⟨hv, a, rfl, (C.cappedSide_iff_onSide hm s).mp ha⟩

include hEuler in
theorem twisted_cut_saturated :
    RotationEuler.count (C.edgeTwist * G.rotation) C.cutPairing =
      2 * Nat.card (Component (C.edgeTwist * G.rotation) C.cutPairing) := by
  have hcut : RotationEuler.count G.circuitStep C.cutPairing =
      2 * Nat.card (Component G.circuitStep C.cutPairing) := by
    rw [C.cut_euler_count, C.cut_component_card hEuler, hEuler]
    push_cast
    ring
  have hd := RotationEuler.left_dual_saturated G.circuitStep C.cutPairing
    C.cutPairing_involutive hcut
  rw [RotationEuler.count_congr _ _ _ _ G.pairing.perm C.cutFace_conjugate C.cutPairing_twin,
    Nat.card_congr (componentCongrEquiv _ _ _ _ G.pairing.perm
      C.cutFace_conjugate C.cutPairing_twin)]
  exact hd

abbrev CappedDart (s : Bool) := Subtype (C.CappedSide s)

noncomputable def sectorRotation (s : Bool) : Perm (C.CappedDart s) :=
  (C.edgeTwist * G.rotation).subtypePerm (C.cappedSide_rotation_iff s)

noncomputable def sectorPairing (s : Bool) : Perm (C.CappedDart s) :=
  C.cutPairing.subtypePerm (C.cappedSide_pairing_iff s)

theorem sectorPairing_involutive (s : Bool) : Function.Involutive (C.sectorPairing s) :=
  fun a => Subtype.ext (C.cutPairing_involutive a.val)

theorem sectorPairing_label (s : Bool) (a : C.CappedDart s) :
    Port.label G.jointLabel (C.sectorPairing s a).val = Port.label G.jointLabel a.val := by
  change Port.label G.jointLabel (C.cutPairing a.val) = _
  by_cases hm : C.Marked a.val
  · rw [C.cutPairing_of_marked hm]
  · rw [C.cutPairing_of_unmarked _ hm, G.pairing.label_twin]

include hEuler in
theorem capped_sector_saturated (s : Bool) :
    RotationEuler.count (C.sectorRotation s) (C.sectorPairing s) =
      2 * Nat.card (Component (C.sectorRotation s) (C.sectorPairing s)) :=
  RotationEuler.subtype_saturated _ _ (C.CappedSide s) (C.cappedSide_rotation_iff s)
    (C.cappedSide_pairing_iff s) C.cutPairing_involutive (C.twisted_cut_saturated hEuler)

end PortGraph.SimpleCircuit
end ThomGame.Pictures

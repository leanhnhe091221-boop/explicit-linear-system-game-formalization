module

public import ThomGame.Pictures.CircuitGermBoundary
public import ThomGame.Pictures.InvariantEuler

/-!
# Euler saturation before adding the germ's boundary leaves

Retain exactly the actual uncut germ edges, fixing every other port.
The complete germ vertex set is invariant under this partial pairing and
the original rotation. Edge deletion and restriction therefore prove
Euler saturation for the partial map on the germ's original ports.
`CircuitGermEuler` completes its fixed outward ports by actual boundary leaves.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv RibbonConnectivity
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []}
    (C : G.SimpleCircuit)
    (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm))

abbrev GermOriginalPort (s : Bool) := {a : G.Dart // C.GermVertex s a.vertex}

noncomputable def germCutPairing (s : Bool) : Perm G.Dart :=
  RotationEuler.retainEdges G.pairing.perm (C.UncutDart s) (C.uncutDart_twin_iff s)

theorem germCutPairing_apply (s : Bool) (a : G.Dart) :
    C.germCutPairing s a = if C.UncutDart s a then G.pairing.twin a else a := rfl

theorem germCutPairing_involutive (s : Bool) : Function.Involutive (C.germCutPairing s) :=
  RotationEuler.retainEdges_involutive _ _ _ G.pairing.involutive

theorem germVertex_rotation_iff (s : Bool) (a : G.Dart) :
    C.GermVertex s (G.rotation a).vertex ↔ C.GermVertex s a.vertex := by
  rw [G.vertex_rotation]

include hEuler in
theorem germVertex_cutPairing_iff (s : Bool) (a : G.Dart) :
    C.GermVertex s (C.germCutPairing s a).vertex ↔ C.GermVertex s a.vertex := by
  by_cases ha : C.UncutDart s a
  · rw [C.germCutPairing_apply, ite_eq_left ha]
    exact iff_of_true
      ((C.germ_vertex_port_iff hEuler s _).mpr (Or.inl ((C.uncutDart_twin_iff s a).mpr ha)))
      ((C.germ_vertex_port_iff hEuler s a).mpr (Or.inl ha))
  · rw [C.germCutPairing_apply, ite_eq_right ha]

noncomputable def germPartialRotation (s : Bool) : Perm (C.GermOriginalPort s) :=
  G.rotation.subtypePerm (C.germVertex_rotation_iff s)

noncomputable def germPartialPairing (s : Bool) : Perm (C.GermOriginalPort s) :=
  (C.germCutPairing s).subtypePerm (C.germVertex_cutPairing_iff hEuler s)

theorem germPartialRotation_val (s : Bool) (a : C.GermOriginalPort s) :
    (C.germPartialRotation s a).val = G.rotation a.val := rfl

include hEuler in
theorem germPartialPairing_val (s : Bool) (a : C.GermOriginalPort s) :
    (C.germPartialPairing hEuler s a).val =
      if C.UncutDart s a.val then G.pairing.twin a.val else a.val := rfl

include hEuler in
theorem germPartialPairing_involutive (s : Bool) :
    Function.Involutive (C.germPartialPairing hEuler s) :=
  fun a => Subtype.ext (C.germCutPairing_involutive s a.val)

include hEuler in
theorem germCutPairing_saturated (s : Bool) :
    RotationEuler.count G.rotation (C.germCutPairing s) =
      2 * Nat.card (Component G.rotation (C.germCutPairing s)) := by
  have hc := Nat.card_congr
    (RotationEuler.dualComponentEquiv G.rotation G.pairing.perm G.pairing.involutive)
  have he := RotationEuler.dual_count G.rotation G.pairing.perm G.pairing.involutive
  rw [G.rotation_mul_pairing] at hc he
  have hp : RotationEuler.count G.rotation G.pairing.perm =
      2 * Nat.card (Component G.rotation G.pairing.perm) := by omega
  exact RotationEuler.retainEdges_saturated G.rotation G.pairing.perm (C.UncutDart s)
    (C.uncutDart_twin_iff s) G.pairing.involutive hp

include hEuler in
theorem germPartial_saturated (s : Bool) :
    RotationEuler.count (C.germPartialRotation s) (C.germPartialPairing hEuler s) =
      2 * Nat.card (Component (C.germPartialRotation s) (C.germPartialPairing hEuler s)) :=
  RotationEuler.subtype_saturated G.rotation (C.germCutPairing s)
    (fun a => C.GermVertex s a.vertex) (C.germVertex_rotation_iff s)
    (C.germVertex_cutPairing_iff hEuler s) (C.germCutPairing_involutive s)
    (C.germCutPairing_saturated hEuler s)

end ThomGame.Pictures.PortGraph.SimpleCircuit

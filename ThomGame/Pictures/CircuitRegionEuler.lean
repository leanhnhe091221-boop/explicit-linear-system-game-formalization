module

public import ThomGame.Pictures.CircuitRegionGraph
public import ThomGame.Pictures.CircuitGermPartialEuler
public import ThomGame.Pictures.VertexErasureEuler
public import ThomGame.Pictures.ConnectedGraphRealization

/-!
# Euler saturation of the actual complementary circuit region

Erase the original circuit vertices by splitting every one of their
ports into a leaf. The retained unmarked side is invariant under the
resulting rotation and the original edge pairing. Its restriction is
equivalent to the already defined region graph, preserving rotation and
pairing. This proves saturation of that graph itself.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv RibbonConnectivity
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []}
  (C : G.SimpleCircuit)

theorem offCircuitVertex_rotation (a : G.Dart) :
    (¬ C.OnCircuitVertex (G.rotation a).vertex) ↔ ¬ C.OnCircuitVertex a.vertex := by
  rw [G.vertex_rotation]

noncomputable def regionFullRotation : Perm G.Dart :=
  RotationEuler.retainEdges G.rotation (fun a => ¬ C.OnCircuitVertex a.vertex)
    C.offCircuitVertex_rotation

theorem regionFullRotation_apply (a : G.Dart) :
    C.regionFullRotation a = if C.OnCircuitVertex a.vertex then a else G.rotation a := by
  rw [regionFullRotation, RotationEuler.retainEdges_apply]
  by_cases h : C.OnCircuitVertex a.vertex <;> simp only [h, not_true_eq_false, not_false_eq_true,
    ite_true, ite_false]

theorem regionFullRotation_kept (s : Bool) (a : G.Dart) :
    C.KeptDart s (C.regionFullRotation a) ↔ C.KeptDart s a := by
  rw [C.regionFullRotation_apply]
  by_cases hv : C.OnCircuitVertex a.vertex
  · rw [ite_eq_left hv]
  · rw [ite_eq_right hv]
    have hn : ¬ C.Marked a := fun hm => hv (C.marked_onCircuitVertex hm)
    have hnr : ¬ C.Marked (G.rotation a) := by
      intro hm
      exact hv ((G.vertex_rotation a) ▸ C.marked_onCircuitVertex hm)
    exact and_congr (iff_of_true hnr hn)
      (C.onSide_same_vertex (by rwa [G.vertex_rotation]) (G.vertex_rotation a) s)

noncomputable def regionRotation (s : Bool) : Perm (Subtype (C.KeptDart s)) :=
  C.regionFullRotation.subtypePerm (C.regionFullRotation_kept s)

variable (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
  2 * Nat.card (Component G.circuitStep G.pairing.perm))

include hEuler in
theorem regionFullRotation_saturated :
    RotationEuler.count C.regionFullRotation G.pairing.perm =
      2 * Nat.card (Component C.regionFullRotation G.pairing.perm) := by
  have he := RotationEuler.dual_count G.rotation G.pairing.perm G.pairing.involutive
  have hc := Nat.card_congr
    (RotationEuler.dualComponentEquiv G.rotation G.pairing.perm G.pairing.involutive)
  rw [G.rotation_mul_pairing] at he hc
  apply RotationEuler.retainRotation_saturated G.rotation G.pairing.perm
    (fun a => ¬ C.OnCircuitVertex a.vertex) C.offCircuitVertex_rotation G.pairing.involutive
  omega

include hEuler in
theorem regionRotation_saturated (s : Bool) :
    RotationEuler.count (C.regionRotation s) (C.keptPairing s).perm =
      2 * Nat.card (Component (C.regionRotation s) (C.keptPairing s).perm) :=
  RotationEuler.subtype_saturated C.regionFullRotation G.pairing.perm (C.KeptDart s)
    (C.regionFullRotation_kept s) (C.keptDart_twin_iff s) G.pairing.involutive
    (C.regionFullRotation_saturated hEuler)

include hEuler in
theorem regionPorts_rotation (s : Bool) (a : (C.regionGraph hEuler s).Dart) :
    C.regionRotation s (C.regionPorts hEuler s a) =
      C.regionPorts hEuler s ((C.regionGraph hEuler s).rotation a) := by
  apply Subtype.ext
  change C.regionFullRotation (C.regionPorts hEuler s a).val = _
  rw [C.regionFullRotation_apply]
  cases a with
  | top i =>
    have hv := ((C.frontier_iff hEuler s _).mp (C.boundaryEnumeration s i).property).1
    exact ite_eq_left hv
  | bottom i => exact i.elim0
  | hub h i =>
    change (if C.OnCircuitVertex (.inr (.inl h.val)) then (Port.hub h.val i : G.Dart)
      else G.rotation (.hub h.val i)) = G.rotation (.hub h.val i)
    rw [ite_eq_right h.property.1]
  | joint j b =>
    change (if C.OnCircuitVertex (.inr (.inr j.val)) then (Port.joint j.val b : G.Dart)
      else G.rotation (.joint j.val b)) = G.rotation (.joint j.val b)
    rw [ite_eq_right j.property.1]

include hEuler in
theorem regionPorts_pairing (s : Bool) (a : (C.regionGraph hEuler s).Dart) :
    (C.keptPairing s).perm (C.regionPorts hEuler s a) =
      C.regionPorts hEuler s ((C.regionGraph hEuler s).pairing.perm a) :=
  Subtype.ext (C.regionGraph_twin hEuler s a).symm

include hEuler in
theorem regionGraph_rotationEuler (s : Bool) :
    RotationEuler.count (C.regionGraph hEuler s).rotation (C.regionGraph hEuler s).pairing.perm =
      2 * Nat.card (Component (C.regionGraph hEuler s).rotation (C.regionGraph hEuler s).pairing.perm) := by
  rw [RotationEuler.count_congr _ _ _ _ (C.regionPorts hEuler s)
    (C.regionPorts_rotation hEuler s) (C.regionPorts_pairing hEuler s),
    Nat.card_congr (componentCongrEquiv _ _ _ _ (C.regionPorts hEuler s)
      (C.regionPorts_rotation hEuler s) (C.regionPorts_pairing hEuler s))]
  exact C.regionRotation_saturated hEuler s

include hEuler in
theorem regionGraph_eulerDefect (s : Bool) :
    eulerDefect (C.regionGraph hEuler s).pairing.perm (C.regionGraph hEuler s).circuitStep = 0 :=
  (C.regionGraph hEuler s).rotationEuler_saturated_iff.mp (C.regionGraph_rotationEuler hEuler s)

end ThomGame.Pictures.PortGraph.SimpleCircuit

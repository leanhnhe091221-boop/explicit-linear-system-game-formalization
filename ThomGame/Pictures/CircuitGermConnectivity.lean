module

public import ThomGame.Pictures.CircuitGermGraph
public import ThomGame.Pictures.RestrictedConnectivity

/-!
# Connectivity of the actual circuit germ

Paths on the selected cut side lift through the unchanged internal
pairing and rotations. The retained circuit connects all rim vertices,
and each new boundary leaf is joined to its own original port. Thus
every germ is connected, even if the original graph has other components.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv RibbonConnectivity
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []}
    (C : G.SimpleCircuit)
    (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm))

theorem onSide_circuitStep_iff (s : Bool) (a : G.Dart) :
    C.OnSide s (G.circuitStep a) ↔ C.OnSide s a :=
  ⟨fun h => (Connected.edge a).trans h, fun h => (Connected.edge a).symm.trans h⟩

theorem onSide_cutPairing_iff (s : Bool) (a : G.Dart) :
    C.OnSide s (C.cutPairing a) ↔ C.OnSide s a :=
  ⟨fun h => (Connected.circuit a).trans h, fun h => (Connected.circuit a).symm.trans h⟩

theorem onSide_uncut {s : Bool} {a : G.Dart} (ha : C.OnSide s a) : C.UncutDart s a := by
  by_cases hm : C.Marked a
  · exact Or.inl hm
  · exact Or.inr ⟨hm, ha⟩

include hEuler in
theorem onSide_germVertex {s : Bool} {a : G.Dart} (ha : C.OnSide s a) :
    C.GermVertex s a.vertex :=
  (C.germ_vertex_port_iff hEuler s a).mpr (Or.inl (C.onSide_uncut ha))

include hEuler in
theorem germInternalPort_rotation (s : Bool)
    (a : {a : G.Dart // C.GermVertex s a.vertex}) :
    (C.germGraph hEuler s).rotation (C.germInternalPort hEuler s a) =
      C.germInternalPort hEuler s ⟨G.rotation a.val,
        by rw [G.vertex_rotation]; exact a.property⟩ := by
  rcases a with ⟨a, ha⟩
  cases a with
  | top i => exact i.elim0
  | bottom i => exact i.elim0
  | hub h i =>
    change (C.germGraph hEuler s).rotation
      (C.germInternalPort hEuler s ⟨.hub h i, ha⟩) =
        C.germInternalPort hEuler s ⟨.hub h (G.hubRotation h i), ha⟩
    rw [C.germInternalPort_hub hEuler s ⟨h, ha⟩, C.germInternalPort_hub hEuler s ⟨h, ha⟩]
    rfl
  | joint j b =>
    change (C.germGraph hEuler s).rotation
      (C.germInternalPort hEuler s ⟨.joint j b, ha⟩) =
        C.germInternalPort hEuler s ⟨.joint j (!b), ha⟩
    rw [C.germInternalPort_joint hEuler s ⟨j, ha⟩, C.germInternalPort_joint hEuler s ⟨j, ha⟩]
    rfl

include hEuler in
theorem germInternalPort_rotation_pow (s : Bool)
    (a : {a : G.Dart // C.GermVertex s a.vertex}) (n : Nat) :
    ((C.germGraph hEuler s).rotation ^ n) (C.germInternalPort hEuler s a) =
      C.germInternalPort hEuler s ⟨(G.rotation ^ n) a.val,
        by rw [G.vertex_rotation_pow]; exact a.property⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih, C.germInternalPort_rotation]
    apply congrArg (C.germInternalPort hEuler s)
    apply Subtype.ext
    simp only [pow_succ', Perm.mul_apply]

include hEuler in
theorem germInternalPort_same_vertex (s : Bool)
    (a b : {a : G.Dart // C.GermVertex s a.vertex}) (hv : a.val.vertex = b.val.vertex) :
    Connected (C.germGraph hEuler s).pairing.perm (C.germGraph hEuler s).circuitStep
      (C.germInternalPort hEuler s a) (C.germInternalPort hEuler s b) := by
  obtain ⟨n, hn⟩ := ((G.rotation_sameCycle_iff a.val b.val).mpr hv).exists_nat_pow_eq
  apply (C.germGraph hEuler s).connected_of_same_vertex
  have he := C.germInternalPort_rotation_pow hEuler s a n
  have hab : (⟨(G.rotation ^ n) a.val, by rw [G.vertex_rotation_pow]; exact a.property⟩ :
      {a : G.Dart // C.GermVertex s a.vertex}) = b := Subtype.ext hn
  rw [hab] at he
  rw [← he, (C.germGraph hEuler s).vertex_rotation_pow]

include hEuler in
theorem germInternalPort_circuitStep_onSide (s : Bool)
    (a : Subtype (C.OnSide s)) :
    (C.germGraph hEuler s).circuitStep
      (C.germInternalPort hEuler s ⟨a.val, C.onSide_germVertex hEuler a.property⟩) =
      C.germInternalPort hEuler s ⟨G.circuitStep a.val,
        C.onSide_germVertex hEuler ((C.onSide_circuitStep_iff s a.val).mpr a.property)⟩ := by
  rw [(C.germGraph hEuler s).circuitStep_apply,
    C.germGraph_twin_internal_uncut hEuler s _ (C.onSide_uncut a.property),
    C.germInternalPort_rotation]
  rfl

include hEuler in
theorem germInternalPort_cut_connected (s : Bool) (a b : Subtype (C.OnSide s))
    (hab : Connected G.circuitStep C.cutPairing a.val b.val) :
    Connected (C.germGraph hEuler s).pairing.perm (C.germGraph hEuler s).circuitStep
      (C.germInternalPort hEuler s ⟨a.val, C.onSide_germVertex hEuler a.property⟩)
      (C.germInternalPort hEuler s ⟨b.val, C.onSide_germVertex hEuler b.property⟩) := by
  apply hab.lift_restricted (C.OnSide s) (C.onSide_circuitStep_iff s) (C.onSide_cutPairing_iff s)
    a.property b.property (fun a => C.germInternalPort hEuler s
      ⟨a.val, C.onSide_germVertex hEuler a.property⟩)
    ⟨Connected.refl, Connected.symm, Connected.trans⟩
  · intro x
    rw [← C.germInternalPort_circuitStep_onSide]
    exact Connected.circuit _
  · intro x
    by_cases hx : C.Marked x.val
    · have he := C.cutPairing_of_marked hx
      have he' : (⟨C.cutPairing x.val,
          C.onSide_germVertex hEuler ((C.onSide_cutPairing_iff s x.val).mpr x.property)⟩ :
          {a : G.Dart // C.GermVertex s a.vertex}) =
          ⟨x.val, C.onSide_germVertex hEuler x.property⟩ := Subtype.ext he
      rw [he']
      exact Connected.refl _
    · have he := C.cutPairing_of_unmarked x.val hx
      have he' : (⟨C.cutPairing x.val,
          C.onSide_germVertex hEuler ((C.onSide_cutPairing_iff s x.val).mpr x.property)⟩ :
          {a : G.Dart // C.GermVertex s a.vertex}) =
          ⟨G.pairing.twin x.val, (C.germ_vertex_port_iff hEuler s _).mpr
            (Or.inl ((C.uncutDart_twin_iff s x.val).mpr (C.onSide_uncut x.property)))⟩ :=
        Subtype.ext he
      rw [he', ← C.germGraph_twin_internal_uncut hEuler s
        ⟨x.val, C.onSide_germVertex hEuler x.property⟩ (C.onSide_uncut x.property)]
      exact Connected.edge _

noncomputable def germCircuitDart (s : Bool) (i : Fin C.length) :
    (C.germGraph hEuler s).Dart :=
  C.germInternalPort hEuler s ⟨C.dart i, Or.inl ⟨i, rfl⟩⟩

include hEuler in
theorem germCircuitDart_next (s : Bool) (i : Fin C.length) :
    Connected (C.germGraph hEuler s).pairing.perm (C.germGraph hEuler s).circuitStep
      (C.germCircuitDart hEuler s i) (C.germCircuitDart hEuler s (finRotate C.length i)) := by
  have hm : C.Marked (C.dart i) := ⟨(i, false), rfl⟩
  have he := C.germGraph_twin_internal_uncut hEuler s
    ⟨C.dart i, Or.inl ⟨i, rfl⟩⟩ (Or.inl hm)
  have hc := Connected.edge (p := (C.germGraph hEuler s).pairing.perm)
    (f := (C.germGraph hEuler s).circuitStep) (C.germCircuitDart hEuler s i)
  change Connected _ _ _ ((C.germGraph hEuler s).pairing.twin
    (C.germInternalPort hEuler s ⟨C.dart i, Or.inl ⟨i, rfl⟩⟩)) at hc
  rw [he] at hc
  exact hc.trans (C.germInternalPort_same_vertex hEuler s _ _ (C.next_vertex i).symm)

include hEuler in
theorem germCircuitDart_connected (s : Bool) (i j : Fin C.length) :
    Connected (C.germGraph hEuler s).pairing.perm (C.germGraph hEuler s).circuitStep
      (C.germCircuitDart hEuler s i) (C.germCircuitDart hEuler s j) := by
  obtain ⟨n, rfl⟩ := (finRotate_sameCycle i j).exists_nat_pow_eq
  induction n with
  | zero => exact Connected.refl _
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    exact ih.trans (C.germCircuitDart_next hEuler s _)

include hEuler in
theorem germInternalPort_connected_base (s : Bool)
    (a : {a : G.Dart // C.GermVertex s a.vertex}) :
    Connected (C.germGraph hEuler s).pairing.perm (C.germGraph hEuler s).circuitStep
      (C.germInternalPort hEuler s a) (C.germCircuitDart hEuler s 0) := by
  rcases a.property with ha | ha
  · obtain ⟨i, hi⟩ := ha
    exact (C.germInternalPort_same_vertex hEuler s a
      ⟨C.dart i, Or.inl ⟨i, rfl⟩⟩ hi.symm).trans (C.germCircuitDart_connected hEuler s i 0)
  · have hs := (C.interior_port_kept s ha a.val rfl).2
    have hroot : C.OnSide s (C.port (0, s)) := Connected.refl _
    have hc := C.germInternalPort_cut_connected hEuler s ⟨a.val, hs⟩ ⟨C.port (0, s), hroot⟩ hs
    have hv := C.port_vertex (0, s)
    exact hc.trans (C.germInternalPort_same_vertex hEuler s _
      ⟨C.dart 0, Or.inl ⟨0, rfl⟩⟩ hv)

include hEuler in
theorem germGraph_connected_base (s : Bool) (a : (C.germGraph hEuler s).Dart) :
    Connected (C.germGraph hEuler s).pairing.perm (C.germGraph hEuler s).circuitStep
      a (C.germCircuitDart hEuler s 0) := by
  cases a with
  | top i => exact i.elim0
  | bottom i =>
    have hc := Connected.edge (p := (C.germGraph hEuler s).pairing.perm)
      (f := (C.germGraph hEuler s).circuitStep) (.bottom i)
    change Connected _ _ _ ((C.germGraph hEuler s).pairing.twin (.bottom i)) at hc
    rw [C.germGraph_twin_bottom] at hc
    exact hc.trans (C.germInternalPort_connected_base hEuler s _)
  | hub h i =>
    rw [← C.germInternalPort_hub]
    exact C.germInternalPort_connected_base hEuler s _
  | joint j b =>
    rw [← C.germInternalPort_joint]
    exact C.germInternalPort_connected_base hEuler s _

include hEuler in
theorem germGraph_connected (s : Bool) (a b : (C.germGraph hEuler s).Dart) :
    Connected (C.germGraph hEuler s).rotation (C.germGraph hEuler s).pairing.perm a b := by
  apply (RotationEuler.connected_rotation_iff _ _ (C.germGraph hEuler s).pairing.involutive a b).mpr
  rw [(C.germGraph hEuler s).rotation_mul_pairing]
  exact (C.germGraph_connected_base hEuler s a).trans (C.germGraph_connected_base hEuler s b).symm

end ThomGame.Pictures.PortGraph.SimpleCircuit

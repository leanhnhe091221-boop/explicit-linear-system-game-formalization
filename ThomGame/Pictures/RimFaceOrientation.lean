module

public import ThomGame.Pictures.RowEdgeSwitchFaces

/-!
# The intrinsic facial orientation of a cubic rim dart

A facial rim chooses one of the two turns at each retained vertex.
The cubic rotation makes this choice unique. It is constant on each
oriented rim orbit and reverses on crossing either of the two pairings.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv
open scoped Classical

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  (G : SolutionGroup.RowGraph A [] []) (γ : Hypergraph.Cycle A.hypergraph)

def RimCorner (side : Bool) (x : G.RimDart γ) : Prop :=
  match side with
  | false => G.rotation (G.rimSwitch γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim x).val = x.val
  | true => G.rotation x.val = (G.rimSwitch γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim x).val

theorem rimSimpleCircuit_incoming_eq (a : G.RimDart γ)
    (i : Fin (G.rimSimpleCircuit γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim a).length) :
    (G.rimSimpleCircuit γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim a).incoming i =
      (G.rimSwitch γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim
        (OrbitEnumeration.dart (G.rimWalk γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim) a i)).val := by
  let C := G.rimSimpleCircuit γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim a
  let y : G.RimDart γ := ⟨C.incoming i,
    C.marked_label_rim γ (G.rimSimpleCircuit_rim γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim a) ⟨(i, true), rfl⟩⟩
  exact congrArg Subtype.val (G.rimSwitch_unique γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim _ y
    (C.incoming_vertex i) (fun he => C.incoming_ne_outgoing i (congrArg Subtype.val he)))

theorem rimCorner_of_face (a : G.RimDart γ) (side : Bool)
    (hf : (G.rimSimpleCircuit γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim a).BoundsFaceOrbit side)
    (x : G.RimDart γ) (hx : (G.rimWalk γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim).SameCycle a x) :
    G.RimCorner γ side x := by
  obtain ⟨i, rfl⟩ := (OrbitEnumeration.dart_range (G.rimWalk γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim) a x).mpr hx
  have hc := SimpleCircuit.corner_rotation_of_boundsFaceOrbit _ side hf i
  cases side
  · change G.rotation ((G.rimSimpleCircuit γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim a).incoming i) = _ at hc
    exact (congrArg G.rotation (G.rimSimpleCircuit_incoming_eq γ a i)).symm.trans hc
  · change G.rotation _ = (G.rimSimpleCircuit γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim a).incoming i at hc
    exact hc.trans (G.rimSimpleCircuit_incoming_eq γ a i)

theorem rim_face_of_corners (a : G.RimDart γ) (side : Bool)
    (hc : ∀ x : G.RimDart γ, (G.rimWalk γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim).SameCycle a x →
      G.RimCorner γ side x) :
    (G.rimSimpleCircuit γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim a).BoundsFaceOrbit side := by
  apply SimpleCircuit.boundsFaceOrbit_of_corner_rotation
  intro i
  have hi := hc _ (OrbitEnumeration.dart_sameCycle _ a i)
  cases side
  · change G.rotation ((G.rimSimpleCircuit γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim a).incoming i) = _
    rw [G.rimSimpleCircuit_incoming_eq]
    exact hi
  · change G.rotation _ = (G.rimSimpleCircuit γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim a).incoming i
    rw [G.rimSimpleCircuit_incoming_eq]
    exact hi

theorem rimCorner_switch (side : Bool) (x : G.RimDart γ) (hc : G.RimCorner γ side x) :
    G.RimCorner γ (!side) (G.rimSwitch γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim x) := by
  cases side
  · exact hc.trans (congrArg Subtype.val (G.rimSwitch_involutive γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim x)).symm
  · exact (congrArg (fun y : G.RimDart γ => G.rotation y.val)
      (G.rimSwitch_involutive γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim x)).trans hc

noncomputable def rimFaceSide (x : G.RimDart γ) : Bool :=
  if G.RimCorner γ false x then false else true

variable [IsEmpty G.Joint]

omit [DecidableEq R] [DecidableEq S] in
theorem row_rotation_two_ne_self (x : G.Dart) : G.rotation (G.rotation x) ≠ x := by
  cases x with
  | top j => exact j.elim0
  | bottom j => exact j.elim0
  | joint j b => exact isEmptyElim j
  | hub h j =>
    have hn : G.hubRotation h (G.hubRotation h j) ≠ j := by
      have hf : ∀ (b : Bool) (i : Fin 3),
          (if b then (finRotate 3).symm else finRotate 3)
            ((if b then (finRotate 3).symm else finRotate 3) i) ≠ i := by decide +kernel
      exact hf (G.hubFlip h) j
    intro he
    exact hn ((G.row_hub_eq_iff.mp he).2)

theorem rimCorner_unique {x : G.RimDart γ} {side other : Bool}
    (hs : G.RimCorner γ side x) (ht : G.RimCorner γ other x) : side = other := by
  cases side <;> cases other
  · rfl
  · exact (G.row_rotation_two_ne_self x.val ((congrArg G.rotation ht).trans hs)).elim
  · exact (G.row_rotation_two_ne_self x.val ((congrArg G.rotation hs).trans ht)).elim
  · rfl

theorem rimFaceSide_eq_of_corner {x : G.RimDart γ} {side : Bool}
    (hc : G.RimCorner γ side x) : G.rimFaceSide γ x = side := by
  unfold rimFaceSide
  split_ifs with hf
  · exact G.rimCorner_unique γ hf hc
  · cases side
    · exact (hf hc).elim
    · rfl

variable (hf : ∀ a : G.RimDart γ,
  ∃ side, (G.rimSimpleCircuit γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim a).BoundsFaceOrbit side)

include hf in
theorem rimFaceSide_corner (x : G.RimDart γ) : G.RimCorner γ (G.rimFaceSide γ x) x := by
  obtain ⟨side, hs⟩ := hf x
  have hc := G.rimCorner_of_face γ x side hs x Perm.SameCycle.rfl
  rw [G.rimFaceSide_eq_of_corner γ hc]
  exact hc

include hf in
theorem rimFaceSide_sameCycle {x y : G.RimDart γ}
    (hxy : (G.rimWalk γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim).SameCycle x y) :
    G.rimFaceSide γ x = G.rimFaceSide γ y := by
  obtain ⟨side, hs⟩ := hf x
  exact (G.rimFaceSide_eq_of_corner γ (G.rimCorner_of_face γ x side hs x Perm.SameCycle.rfl)).trans
    (G.rimFaceSide_eq_of_corner γ (G.rimCorner_of_face γ x side hs y hxy)).symm

include hf in
theorem rimFaceSide_switch (x : G.RimDart γ) :
    G.rimFaceSide γ (G.rimSwitch γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim x) = !(G.rimFaceSide γ x) :=
  G.rimFaceSide_eq_of_corner γ (G.rimCorner_switch γ _ x (G.rimFaceSide_corner γ hf x))

include hf in
theorem rimFaceSide_twin (x : G.RimDart γ) :
    G.rimFaceSide γ ((G.rimPairing γ).twin x) = !(G.rimFaceSide γ x) := by
  have he := (G.rimFaceSide_sameCycle γ hf
    (show (G.rimWalk γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim).SameCycle x (G.rimWalk γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim x)
      from Perm.SameCycle.rfl.apply_right)).symm
  change G.rimFaceSide γ (G.rimSwitch γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim ((G.rimPairing γ).twin x)) = _ at he
  rw [G.rimFaceSide_switch γ hf] at he
  simpa only [Bool.not_not] using congrArg Bool.not he

end ThomGame.Pictures.PortGraph

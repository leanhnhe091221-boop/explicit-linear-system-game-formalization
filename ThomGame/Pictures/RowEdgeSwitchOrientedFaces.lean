module

public import ThomGame.Pictures.RimFaceOrientation

/-!
# Reconnecting rims with matching facial orientations

The old facial-side function survives an attachment exchange whose two
cuts have the same side. It is invariant under the actual new rim walk.
The unchanged local corners therefore certify every new facial orbit,
whether the operation splits one old rim or joins two different rims.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.RowEdgeSwitch

open Equiv
open scoped Classical

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  {G : SolutionGroup.RowGraph A [] []} (s : G.RowEdgeSwitch)
  (γ : Hypergraph.Cycle A.hypergraph)

theorem rimSwitch_eq (x : G.RimDart γ) :
    s.graph.rimSwitch γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim x = G.rimSwitch γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim x :=
  congrArg (fun p => p.twin x) (s.rimVertexPairing_eq γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim)

theorem rimCorner_iff (side : Bool) (x : G.RimDart γ) :
    s.graph.RimCorner γ side x ↔ G.RimCorner γ side x := by
  cases side
  · change s.graph.rotation (s.graph.rimSwitch γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim x).val = x.val ↔ _
    rw [s.rimSwitch_eq, s.rotation]
    rfl
  · change s.graph.rotation x.val = (s.graph.rimSwitch γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim x).val ↔ _
    rw [s.rimSwitch_eq, s.rotation]
    rfl

variable (ha : Port.label G.jointLabel s.first ∈ Set.range γ.edge)
  (hs : G.rimFaceSide γ ⟨s.first, ha⟩ = G.rimFaceSide γ ⟨s.second, s.label_eq ▸ ha⟩)

include hs in
theorem rimFaceSide_rimSwap (x : G.RimDart γ) :
    G.rimFaceSide γ (s.rimSwap γ ha x) = G.rimFaceSide γ x :=
  @Pairing.label_swap (G.RimDart γ) Bool (G.rimFaceSide γ) (Classical.typeDecidableEq _)
    ⟨s.first, ha⟩ ⟨s.second, s.label_eq ▸ ha⟩ hs x

variable [IsEmpty G.Joint]
  (hf : ∀ a : G.RimDart γ,
    ∃ side, (G.rimSimpleCircuit γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim a).BoundsFaceOrbit side)

include hs hf in
theorem rimFaceSide_newWalk (x : G.RimDart γ) :
    G.rimFaceSide γ (s.graph.rimWalk γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim x) = G.rimFaceSide γ x := by
  change G.rimFaceSide γ
    ((s.graph.rimVertexPairing γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim).perm ((s.graph.rimPairing γ).perm x)) = _
  rw [s.rimVertexPairing_eq, s.rimPairing_perm γ ha]
  change G.rimFaceSide γ (G.rimSwitch γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim
    (s.rimSwap γ ha ((G.rimPairing γ).twin (s.rimSwap γ ha x)))) = _
  rw [G.rimFaceSide_switch γ hf, s.rimFaceSide_rimSwap γ ha hs,
    G.rimFaceSide_twin γ hf, s.rimFaceSide_rimSwap γ ha hs, Bool.not_not]

include hs hf in
theorem rim_faces_of_same_side : ∀ a : s.graph.RimDart γ,
    ∃ side, (s.graph.rimSimpleCircuit γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim a).BoundsFaceOrbit side := by
  intro a
  refine ⟨G.rimFaceSide γ a, s.graph.rim_face_of_corners γ a _ ?_⟩
  intro x hx
  have he := CycleSurgery.invariant_sameCycle (s.graph.rimWalk γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim)
    (G.rimFaceSide γ) (s.rimFaceSide_newWalk γ ha hs hf) hx
  rw [he]
  exact (s.rimCorner_iff γ _ x).mpr (G.rimFaceSide_corner γ hf x)

end ThomGame.Pictures.PortGraph.RowEdgeSwitch

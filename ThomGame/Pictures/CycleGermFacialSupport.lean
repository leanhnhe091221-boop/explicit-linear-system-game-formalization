module

public import ThomGame.Pictures.CycleIntersectionTurns
public import ThomGame.Pictures.CircuitGermThreeSteps
public import ThomGame.Pictures.CircuitFaces

/-!
# Actual quadrilaterals covering the exterior face darts of a cycle germ

The intersection hypothesis gives the three-edge decomposition on the
original graph. Every retained face dart on the exterior side of the germ
is an internal dart of one of these quadrilaterals. The later lift of the
whole original circuit across the glued seam is a separate construction.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open RibbonConnectivity

namespace SimpleCircuit

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []}
  (C : G.SimpleCircuit)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (Component G.circuitStep G.pairing.perm))

include hEuler in
theorem germVertex_exterior_onCircuit {s : Bool} {x : G.Dart}
    (hv : C.GermVertex s x.vertex) (hs : C.OnSide (!s) x) : C.OnCircuitVertex x.vertex := by
  rcases hv with hv | hv
  · exact hv
  · have ht := (C.interior_port_kept s hv x rfl).2
    exact False.elim ((Bool.not_eq_self s).mp (C.onSide_unique hEuler hs ht))

noncomputable def germFaceSource (s : Bool) : (C.germGraph hEuler s).swapBoundary.Dart → G.Dart
  | .top i => G.pairing.twin (C.boundaryEnumeration (!s) i).val
  | .bottom i => i.elim0
  | .hub h i => .hub h.val i
  | .joint j b => .joint j.val b

theorem germFaceSource_label (s : Bool) (x : (C.germGraph hEuler s).swapBoundary.Dart) :
    Port.label G.jointLabel (C.germFaceSource hEuler s x) =
      Port.label (C.germGraph hEuler s).swapBoundary.jointLabel x := by
  cases x with
  | top i =>
    change Port.label G.jointLabel (G.pairing.twin (C.boundaryEnumeration (!s) i).val) = _
    rw [G.pairing.label_twin]
    exact C.boundaryEnumeration_label (!s) i
  | bottom i => exact i.elim0
  | hub h i => rfl
  | joint j b => rfl

theorem onSide_of_sameFace {s : Bool} {x y : G.Dart}
    (hxy : G.circuitStep.SameCycle x y) (hx : C.OnSide s x) : C.OnSide s y :=
  predicate_of_sameCycle G.circuitStep (C.OnSide s)
    (fun z hz => (C.onSide_circuitStep_iff s z).mpr hz) hxy hx

end SimpleCircuit

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  (G : SolutionGroup.RowGraph A [] []) [IsEmpty G.Joint]
  (C D : Hypergraph.Cycle A.hypergraph) (a : G.RimDart C) (b : G.RimDart D)
  (hcommon : ∀ e f, e ∈ Set.range C.edge → e ∈ Set.range D.edge →
    f ∈ Set.range C.edge → f ∈ Set.range D.edge → e = f)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (Component G.circuitStep G.pairing.perm))
  (side : Bool) (hf : (G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).BoundsFaceOrbit side)

omit [IsEmpty G.Joint] in
include hf in
theorem rimFace_label {x : G.Dart}
    (hx : G.circuitStep.SameCycle x ((G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).port (0, side))) :
    Port.label G.jointLabel x ∈ Set.range D.edge := by
  obtain ⟨i, rfl⟩ := (hf x).mp hx
  exact G.rimSimpleCircuit_marked_label D b ⟨(i, side), rfl⟩

include hcommon hf in
theorem rimFace_entry_quad (s : Bool) (x : G.Dart)
    (hx : (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Frontier (!s) x)
    (hface : G.circuitStep.SameCycle (G.pairing.twin x)
      ((G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).port (0, side))) :
    ∃ q : ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).germGraph hEuler s).swapBoundary.BoundaryQuadPath,
      q.firstDart = .top (((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).boundaryEnumeration (!s)).symm
        ⟨x, hx⟩) := by
  let γ := G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a
  have hyf : G.circuitStep.SameCycle (G.rotation x)
      ((G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).port (0, side)) := by
    have he := hface.apply_left
    rw [G.circuitStep_apply, G.pairing.involutive] at he
    exact he
  have hy := G.frontier_rotation_marked C a hx
  have hz := G.frontier_common_edge_exits C D hcommon a hx
    (G.rimFace_label D b side hf hyf) (G.rimFace_label D b side hf hyf.apply_left)
  obtain ⟨q, hq, _, _⟩ := γ.germTop_quad_of_crossing hEuler s x hx hy hz
    (G.row_twin_vertex_ne (G.rotation x))
  exact ⟨q, hq⟩

include hcommon hf in
theorem rimFace_marked_quad (s : Bool) (x : G.Dart)
    (hx : (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Marked x)
    (hs : (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).OnSide (!s) x)
    (hface : G.circuitStep.SameCycle x
      ((G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).port (0, side))) :
    ∃ q : ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).germGraph hEuler s).swapBoundary.BoundaryQuadPath,
      q.middleDart = (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).germTopInternalPort hEuler s
        ⟨x, Or.inl ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).marked_onCircuitVertex hx)⟩ := by
  let γ := G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a
  let y := G.rotation.symm x
  have hyr : G.rotation y = x := G.rotation.apply_symm_apply x
  have hyv : y.vertex = x.vertex := (G.vertex_rotation y).symm.trans (congrArg Port.vertex hyr)
  have hyp : G.circuitStep (G.pairing.twin y) = x := by
    rw [G.circuitStep_apply, G.pairing.involutive]; exact hyr
  have hyf : G.circuitStep.SameCycle (G.pairing.twin y)
      ((G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).port (0, side)) := by
    apply Equiv.Perm.sameCycle_apply_left.mp
    rwa [hyp]
  have hyD : Port.label G.jointLabel y ∈ Set.range D.edge := by
    have h := G.rimFace_label D b side hf hyf
    rwa [G.pairing.label_twin] at h
  have hyn : ¬ γ.Marked y := by
    intro hy
    have he := G.common_cycle_ports_eq C D hcommon hyv
      (G.rimSimpleCircuit_marked_label C a hy) hyD
      (G.rimSimpleCircuit_marked_label C a hx) (G.rimFace_label D b side hf hface)
    exact G.row_rotation_ne_self y (hyr.trans he.symm)
  have hys : γ.OnSide (!s) y := by
    apply (γ.onSide_twin_iff hyn (!s)).mp
    apply (γ.onSide_circuitStep_iff (!s) (G.pairing.twin y)).mp
    rwa [hyp]
  have hyv' : γ.OnCircuitVertex y.vertex := by rw [hyv]; exact γ.marked_onCircuitVertex hx
  have hy : γ.Frontier (!s) y := (γ.frontier_iff hEuler (!s) y).mpr ⟨hyv', hyn, hys⟩
  have hmid := G.frontier_rotation_marked C a hy
  have hmidf : G.circuitStep.SameCycle (G.rotation y)
      ((G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).port (0, side)) := by rwa [hyr]
  have hz := G.frontier_common_edge_exits C D hcommon a hy
    (G.rimFace_label D b side hf hmidf) (G.rimFace_label D b side hf hmidf.apply_left)
  obtain ⟨q, _, hq, _⟩ := γ.germTop_quad_of_crossing hEuler s y hy hmid hz
    (G.row_twin_vertex_ne (G.rotation y))
  refine ⟨q, hq.trans ?_⟩
  exact congrArg (γ.germTopInternalPort hEuler s) (Subtype.ext hyr)

include hcommon hf in
theorem rimFace_germ_internal_supported (s : Bool)
    (x : {x : G.Dart // (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).GermVertex s x.vertex})
    (hs : (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).OnSide (!s) x.val)
    (hface : G.circuitStep.SameCycle x.val
      ((G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).port (0, side))) :
    ∃ q : ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).germGraph hEuler s).swapBoundary.BoundaryQuadPath,
      (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).germTopInternalPort hEuler s x ∈
        [q.middleDart, q.lastDart] := by
  classical
  let γ := G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a
  have hv := γ.germVertex_exterior_onCircuit hEuler x.property hs
  by_cases hx : γ.Marked x.val
  · obtain ⟨q, hq⟩ := G.rimFace_marked_quad C D a b hcommon hEuler side hf s x.val hx hs hface
    exact ⟨q, by rw [← hq]; simp⟩
  · let y := G.circuitStep.symm x.val
    have hyp : G.circuitStep y = x.val := G.circuitStep.apply_symm_apply x.val
    have hyv : (G.pairing.twin y).vertex = x.val.vertex :=
      (G.vertex_circuitStep y).symm.trans (congrArg Port.vertex hyp)
    have hyC : Port.label G.jointLabel (G.pairing.twin y) ∈ Set.range C.edge := by
      by_contra hn
      have h := G.rotation_nonrim_enters_rim C a (G.pairing.twin y) (hyv.symm ▸ hv) hn
      change Port.label G.jointLabel (G.circuitStep y) ∈ Set.range C.edge at h
      rw [hyp] at h
      exact hx (G.rimSimpleCircuit_marked_of_vertex_label C a hv h)
    have hym : γ.Marked y := (γ.marked_twin_iff y).mp
      (G.rimSimpleCircuit_marked_of_vertex_label C a (hyv.symm ▸ hv) hyC)
    have hys : γ.OnSide (!s) y := by
      apply (γ.onSide_circuitStep_iff (!s) y).mp
      rwa [hyp]
    have hyf : G.circuitStep.SameCycle y
        ((G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).port (0, side)) := by
      exact Equiv.Perm.sameCycle_symm_apply_left.mpr hface
    obtain ⟨q, hq⟩ := G.rimFace_marked_quad C D a b hcommon hEuler side hf s y hym hys hyf
    have he := γ.germTopInternalPort_step hEuler s
      ⟨y, Or.inl (γ.marked_onCircuitVertex hym)⟩ x hym hyp
    rw [← hq, q.second_step] at he
    exact ⟨q, by rw [← he]; simp⟩

include hcommon hf in
theorem rimFace_germ_supported (s : Bool)
    (hs : (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).OnSide (!s)
      ((G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).port (0, side)))
    (x : ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).germGraph hEuler s).swapBoundary.Dart)
    (hface : G.circuitStep.SameCycle
      ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).germFaceSource hEuler s x)
      ((G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).port (0, side))) :
    ∃ q : ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).germGraph hEuler s).swapBoundary.BoundaryQuadPath,
      x ∈ [q.firstDart, q.middleDart, q.lastDart] := by
  let γ := G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a
  cases x with
  | top i =>
    obtain ⟨q, hq⟩ := G.rimFace_entry_quad C D a b hcommon hEuler side hf s
      (γ.boundaryEnumeration (!s) i).val (γ.boundaryEnumeration (!s) i).property hface
    rw [Equiv.symm_apply_apply] at hq
    exact ⟨q, by rw [← hq]; simp⟩
  | bottom i => exact i.elim0
  | hub h i =>
    let y : {y : G.Dart // γ.GermVertex s y.vertex} := ⟨.hub h.val i, h.property⟩
    have hys : γ.OnSide (!s) y.val := γ.onSide_of_sameFace hface.symm hs
    obtain ⟨q, hq⟩ := G.rimFace_germ_internal_supported C D a b hcommon hEuler side hf s y hys hface
    change γ.germTopInternalPort hEuler s ⟨.hub h.val i, h.property⟩ ∈ _ at hq
    rw [γ.germTopInternalPort_hub hEuler s h i] at hq
    exact ⟨q, List.mem_cons_of_mem _ hq⟩
  | joint j t => exact isEmptyElim j.val

include hcommon hf in
theorem rimFace_germ_supported_of_entry (s : Bool) (entry : G.Dart)
    (he : (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Frontier (!s) entry)
    (heface : G.circuitStep.SameCycle (G.pairing.twin entry)
      ((G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).port (0, side)))
    (x : ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).germGraph hEuler s).swapBoundary.Dart)
    (hface : G.circuitStep.SameCycle
      ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).germFaceSource hEuler s x)
      ((G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).port (0, side))) :
    ∃ q : ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).germGraph hEuler s).swapBoundary.BoundaryQuadPath,
      x ∈ [q.firstDart, q.middleDart, q.lastDart] := by
  let γ := G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a
  have hs := ((γ.frontier_iff hEuler (!s) entry).mp he).2.2
  have hst := (γ.onSide_twin_iff he.2 (!s)).mpr hs
  exact G.rimFace_germ_supported C D a b hcommon hEuler side hf s
    (γ.onSide_of_sameFace heface hst) x hface

end ThomGame.Pictures.PortGraph

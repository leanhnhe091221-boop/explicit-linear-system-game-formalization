module

public import ThomGame.Pictures.FacialCircuitMarked
public import ThomGame.Pictures.LiftedGermSupport

/-!
# A boundary edge of an original face appears at both seam ports

The directed projection commutes with edge reversal. Thus membership in
the lifted circuit, without selecting an orientation, is precisely
membership in the original circuit. A frontier edge places either face
orientation on the exterior cut side and supplies quadrilateral support.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open RibbonConnectivity

namespace SimpleCircuit

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []}
  (C : G.SimpleCircuit)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (Component G.circuitStep G.pairing.perm)) (s : Bool)

theorem orientedFaceProjection_pairing (x : (C.orientedGluedGraph hEuler s).Dart) :
    C.orientedFaceProjection hEuler s ((C.orientedGluedGraph hEuler s).pairing.twin x) =
      G.pairing.twin (C.orientedFaceProjection hEuler s x) := by
  obtain ⟨x, rfl⟩ := (C.orientedGluedPorts hEuler s).surjective x
  unfold orientedFaceProjection
  rw [show (C.orientedGluedGraph hEuler s).pairing.twin (C.orientedGluedPorts hEuler s x) =
      C.orientedGluedPorts hEuler s ((C.gluedGraph hEuler s).pairing.twin x) from
        reverseCompPorts_pairing (C.germGraph hEuler s) (C.regionGraph hEuler (!s)) x,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, C.gluedFaceProjection_pairing]

theorem orientedFaceProjection_seam_false (j : Fin (C.frontierWord (!s)).length) :
    C.orientedFaceProjection hEuler s (.joint (.inr j) false) =
      (C.boundaryEnumeration (!s) j).val := rfl

theorem orientedFaceProjection_seam_true (j : Fin (C.frontierWord (!s)).length) :
    C.orientedFaceProjection hEuler s (.joint (.inr j) true) =
      G.pairing.twin (C.boundaryEnumeration (!s) j).val := rfl

variable (hc : ∀ x y : G.Vertex, G.Reachable x y)
  (D : G.SimpleCircuit) (side : Bool) (hf : D.BoundsFaceOrbit side)

theorem orientedLiftedCircuit_marked_iff (x : (C.orientedGluedGraph hEuler s).Dart) :
    (C.orientedLiftedCircuit hEuler hc s D side hf).Marked x ↔
      D.Marked (C.orientedFaceProjection hEuler s x) := by
  rw [(C.orientedLiftedCircuit hEuler hc s D side hf).marked_iff_side_or_twin false x]
  change (∃ j, (C.orientedLiftedCircuit hEuler hc s D side hf).dart j = x) ∨
    (∃ j, (C.orientedLiftedCircuit hEuler hc s D side hf).dart j =
      (C.orientedGluedGraph hEuler s).pairing.twin x) ↔ _
  rw [C.orientedLiftedCircuit_range, C.orientedLiftedCircuit_range,
    C.orientedFaceProjection_pairing, D.marked_iff_face_or_twin side hf]

theorem orientedLiftedCircuit_marked_seam (j : Fin (C.frontierWord (!s)).length)
    (hj : D.Marked (C.boundaryEnumeration (!s) j).val) (b : Bool) :
    (C.orientedLiftedCircuit hEuler hc s D side hf).Marked (.joint (.inr j) b) := by
  rw [C.orientedLiftedCircuit_marked_iff]
  cases b
  · exact hj
  · exact (D.marked_twin_iff _).mpr hj

include hEuler hf in
theorem face_exterior_of_frontier_edge (entry : G.Dart)
    (he : C.Frontier (!s) entry) (hD : D.Marked entry) :
    C.OnSide (!s) (D.port (0, side)) := by
  have hs := ((C.frontier_iff hEuler (!s) entry).mp he).2.2
  rcases (D.marked_iff_face_or_twin side hf entry).mp hD with hd | hd
  · exact C.onSide_of_sameFace hd hs
  · exact C.onSide_of_sameFace hd ((C.onSide_twin_iff he.2 (!s)).mpr hs)

end SimpleCircuit

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  (G : SolutionGroup.RowGraph A [] []) [IsEmpty G.Joint]
  (C D : Hypergraph.Cycle A.hypergraph) (a : G.RimDart C) (b : G.RimDart D)
  (hcommon : ∀ e f, e ∈ Set.range C.edge → e ∈ Set.range D.edge →
    f ∈ Set.range C.edge → f ∈ Set.range D.edge → e = f)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (Component G.circuitStep G.pairing.perm))
  (hc : ∀ x y : G.Vertex, G.Reachable x y) (s side : Bool)
  (hf : (G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).BoundsFaceOrbit side)

include hcommon in
theorem orientedLiftedRimCircuit_supported_of_side
    (hs : (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).OnSide (!s)
      ((G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).port (0, side))) :
    ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).orientedLiftedCircuit hEuler hc s
      (G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b) side hf).SupportedByQuads false := by
  intro j x hx
  let γ := G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a
  let δ := G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b
  have hp := γ.orientedLiftedCircuit_source hEuler hc s δ side hf j
  change (γ.orientedLiftedCircuit hEuler hc s δ side hf).dart j = _ at hx
  rw [hx, γ.orientedFaceProjection_germ] at hp
  exact G.rimFace_germ_supported C D a b hcommon hEuler side hf s hs x hp

end ThomGame.Pictures.PortGraph

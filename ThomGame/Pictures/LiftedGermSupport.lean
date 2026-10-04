module

public import ThomGame.Pictures.LiftedGermFaces
public import ThomGame.Pictures.QuadCrossingCircuit

/-! # Original crossing faces satisfy the actual glued quadrilateral support condition -/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open RibbonConnectivity

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  (G : SolutionGroup.RowGraph A [] []) [IsEmpty G.Joint]
  (C D : Hypergraph.Cycle A.hypergraph) (a : G.RimDart C) (b : G.RimDart D)
  (hcommon : ∀ e f, e ∈ Set.range C.edge → e ∈ Set.range D.edge →
    f ∈ Set.range C.edge → f ∈ Set.range D.edge → e = f)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (Component G.circuitStep G.pairing.perm))
  (hc : ∀ x y : G.Vertex, G.Reachable x y) (s side : Bool)
  (hf : (G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).BoundsFaceOrbit side)
  (entry : G.Dart)
  (he : (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Frontier (!s) entry)
  (heface : G.circuitStep.SameCycle (G.pairing.twin entry)
    ((G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).port (0, side)))

include hcommon he heface in
theorem orientedLiftedRimCircuit_supported :
    ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).orientedLiftedCircuit hEuler hc s
      (G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b) side hf).SupportedByQuads false := by
  intro j x hx
  let γ := G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a
  let δ := G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b
  have hp := γ.orientedLiftedCircuit_source hEuler hc s δ side hf j
  change (γ.orientedLiftedCircuit hEuler hc s δ side hf).dart j = _ at hx
  have hproj : γ.orientedFaceProjection hEuler s
      ((γ.orientedLiftedCircuit hEuler hc s δ side hf).dart j) = γ.germFaceSource hEuler s x :=
    (congrArg (γ.orientedFaceProjection hEuler s) hx).trans (γ.orientedFaceProjection_germ hEuler s x)
  have hp' : G.circuitStep.SameCycle (γ.germFaceSource hEuler s x) (δ.port (0, side)) := hproj ▸ hp
  exact G.rimFace_germ_supported_of_entry C D a b hcommon hEuler side hf s entry he heface x hp'

omit [IsEmpty G.Joint] in
include he heface in
theorem orientedLiftedRimCircuit_crosses :
    ∃ j x, ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).orientedLiftedCircuit hEuler hc s
      (G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b) side hf).port (j, false) =
        compRightEmbedding ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).regionGraph hEuler (!s)).swapBoundary
          ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).germGraph hEuler s).swapBoundary x := by
  let γ := G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a
  let δ := G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b
  let x : (γ.germGraph hEuler s).swapBoundary.Dart :=
    .top ((γ.boundaryEnumeration (!s)).symm ⟨entry, he⟩)
  have hp : G.circuitStep.SameCycle (γ.germFaceSource hEuler s x) (δ.port (0, side)) := by
    change G.circuitStep.SameCycle
      (G.pairing.twin (γ.boundaryEnumeration (!s) ((γ.boundaryEnumeration (!s)).symm ⟨entry, he⟩)).val) _
    rw [Equiv.apply_symm_apply]
    exact heface
  have hproj : G.circuitStep.SameCycle
      (γ.orientedFaceProjection hEuler s
        (compRightEmbedding (γ.regionGraph hEuler (!s)).swapBoundary (γ.germGraph hEuler s).swapBoundary x))
      (δ.port (0, side)) := by
    rw [γ.orientedFaceProjection_germ]
    exact hp
  obtain ⟨j, hj⟩ := (γ.orientedLiftedCircuit_range hEuler hc s δ side hf _).mpr hproj
  exact ⟨j, x, hj⟩

end ThomGame.Pictures.PortGraph

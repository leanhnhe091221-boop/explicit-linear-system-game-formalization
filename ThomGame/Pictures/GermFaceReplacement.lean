module

public import ThomGame.Pictures.LiftedGermSupport
public import ThomGame.Pictures.LiftedFaceReplacement

/-!
# Original crossing faces survive actual germ replacement and smoothing

The input is an original facial rim circuit and an exterior entry.
Quadrilateral support is derived from the cycle intersection hypothesis.
The result accounts for every original face port exactly once after the
specified full smoothing, with its original edge label.
-/

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


variable {N : SolutionGroup.RowGraph A ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).frontierWord (!s)) []} [IsEmpty N.Joint]
  (r : ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).germGraph hEuler s).swapBoundary.BoundaryQuadReplacement N)
  (red : ClosedGluingReduction ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).regionGraph hEuler (!s)).swapBoundary N)

include hcommon hEuler hc hf he heface in
theorem rimFace_replacement_survives :
    ∃ F : red.graph.SimpleCircuit, F.BoundsFaceOrbit false ∧
      (∀ j : Fin F.length, ∃ i : Fin (G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).length,
        red.trace.portEmbedding (F.dart j) = r.gluedPorts ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).regionGraph hEuler (!s)).swapBoundary
          ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).orientedLiftPort hEuler hc s ((G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).port (i, side))) ∧
        Port.label red.graph.jointLabel (F.dart j) = Port.label G.jointLabel ((G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).port (i, side))) ∧
      (∀ i : Fin (G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).length, ∃! j : Fin F.length,
        red.trace.portEmbedding (F.dart j) = r.gluedPorts ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).regionGraph hEuler (!s)).swapBoundary
          ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).orientedLiftPort hEuler hc s ((G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).port (i, side)))) := by
  exact (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).liftedFace_replacement_survives
    hEuler hc s (G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b) side hf
    (G.orientedLiftedRimCircuit_supported C D a b hcommon hEuler hc s side hf entry he heface) r red

include hcommon hEuler hc hf he heface in
theorem rimFace_replacement_survives_equiv :
    ∃ F : red.graph.SimpleCircuit, F.BoundsFaceOrbit false ∧
      F.length = (G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).length ∧
      ∃ e : Fin F.length ≃ Fin (G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).length,
        ∀ j : Fin F.length,
          red.trace.portEmbedding (F.dart j) =
            r.gluedPorts ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).regionGraph hEuler (!s)).swapBoundary
              ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).orientedLiftPort hEuler hc s
                ((G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).port (e j, side))) ∧
          Port.label red.graph.jointLabel (F.dart j) =
            Port.label G.jointLabel ((G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).port (e j, side)) := by
  exact (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).liftedFace_replacement_survives_equiv
    hEuler hc s (G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b) side hf
    (G.orientedLiftedRimCircuit_supported C D a b hcommon hEuler hc s side hf entry he heface) r red

end ThomGame.Pictures.PortGraph

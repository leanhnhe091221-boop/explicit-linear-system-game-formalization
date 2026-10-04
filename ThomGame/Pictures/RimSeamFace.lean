module

public import ThomGame.Pictures.SeamFaceReplacement
public import ThomGame.Pictures.ReducedGluingClassification
public import ThomGame.Pictures.RimCircuitUniqueness

/-!
# A target rim circuit meeting the seam is facial

The old rim through the original frontier edge supplies a facial
witness. Its lifted face lies on the exterior cut side, so all its germ
ports have quadrilateral support. The preserved face and the arbitrary
target circuit share the actual smoothed edge at the recorded seam.
Uniqueness of the restricted rim component gives target faciality.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open RibbonConnectivity

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  (G : SolutionGroup.RowGraph A [] []) [IsEmpty G.Joint]
  (C D : Hypergraph.Cycle A.hypergraph) (a : G.RimDart C)
  (hcommon : ∀ e f, e ∈ Set.range C.edge → e ∈ Set.range D.edge →
    f ∈ Set.range C.edge → f ∈ Set.range D.edge → e = f)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (Component G.circuitStep G.pairing.perm))
  (hc : ∀ x y : G.Vertex, G.Reachable x y) (s : Bool)
  (hfaces : ∀ b : G.RimDart D,
    ∃ side, (G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).BoundsFaceOrbit side)
  {N : SolutionGroup.RowGraph A
    ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).frontierWord (!s)) []}
  [IsEmpty N.Joint]
  (r : ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).germGraph hEuler s).swapBoundary.BoundaryQuadReplacement N)
  (red : ThomGame.Pictures.ClosedGluingReduction
    ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).regionGraph hEuler (!s)).swapBoundary N)
  (hTargetEuler : RotationEuler.count red.graph.circuitStep red.graph.pairing.perm =
    2 * Nat.card (Component red.graph.circuitStep red.graph.pairing.perm))
  (X : red.graph.SimpleCircuit)
  (hlabels : ∀ k : Fin X.length, Port.label red.graph.jointLabel (X.dart k) ∈ Set.range D.edge)

include hcommon hc hfaces hlabels hTargetEuler r in
theorem rim_circuit_facial_of_meets_seam (hseam : red.MeetsSeam X) : ∃ side, X.BoundsFaceOrbit side := by
  let γ := G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a
  obtain ⟨k, j, b, hpair, hlabel⟩ := hseam
  let entry := (γ.boundaryEnumeration (!s) j).val
  have he : γ.Frontier (!s) entry := (γ.boundaryEnumeration (!s) j).property
  have hentry : Port.label G.jointLabel entry ∈ Set.range D.edge := by
    rw [show Port.label G.jointLabel entry = (γ.frontierWord (!s))[j] from
      γ.boundaryEnumeration_label (!s) j, ← hlabel]
    exact hlabels k
  let c : G.RimDart D := ⟨entry, hentry⟩
  let δ := G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim c
  have hm : δ.Marked entry := ⟨(0, false), rfl⟩
  obtain ⟨side, hf⟩ := hfaces c
  have hout := γ.face_exterior_of_frontier_edge hEuler s δ side hf entry he hm
  have hsup := G.orientedLiftedRimCircuit_supported_of_side C D a c hcommon hEuler hc s side hf hout
  obtain ⟨F, hF, hmark, hl⟩ := γ.liftedFace_replacement_meets_seam hEuler hc s δ side hf hsup
    r red j hm b (X.dart k) hpair
  have hFlabels (l : Fin F.length) : Port.label red.graph.jointLabel (F.dart l) ∈ Set.range D.edge := by
    obtain ⟨m, hm⟩ := hl l
    rw [hm]
    exact G.rimSimpleCircuit_marked_label D c ⟨(m, side), rfl⟩
  exact X.exists_face_of_common_rim_port D (by simp) (by simp) hlabels F hFlabels
    hTargetEuler (X.dart k) ⟨(k, false), rfl⟩ hmark false hF

end ThomGame.Pictures.PortGraph

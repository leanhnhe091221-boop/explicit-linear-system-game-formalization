module

public import ThomGame.Construction.WheelGermQuadTop
public import ThomGame.Pictures.BoundaryQuadReplacement

/-!
# Actual stellar replacement retaining all original outer quadrilaterals

Retraction acts on the original germ, the finite inward trace starts on
that graph, and inclusion returns to the original top boundary. Every
outer quadrilateral retains its boundary positions, three specified
ports, edge pairs and Sigma labels. Oriented gluing with the actual
complementary region then has the original size, odd sign, zero Euler
defect and a minimal diagram with its exact relation multiset.

Preservation of whole original crossing faces is proved in
WheelGermOldFaces and combined with this normalization construction in
WheelGermFaceNormalization.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures RibbonConnectivity
open scoped BigOperators

variable {d : SigmaDiagram [] []} {H : SigmaGraph [] []} 
  (t : SigmaGraphWitness d H) (i : WheelCycleIndex)
  (a : H.RimDart (numberedWheelCycles i)) (side : Bool)
  (m : GermSunRelabelling t i a side)
  (hw : ((closedSigmaRimCircuit H i a).frontierWord (!side)).map m.edge =
    closedSigmaRimSunFrontierWord H i a (!side))
  {K : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0))
    [] (((closedSigmaRimCircuit H i a).frontierWord (!side)).map m.edge).reverse}
  (q : PortGraph.SunSwitchTrace (germSunInitialGraph t i a side m) K)
  (L : IncludedWheelSun i K ((closedSigmaRimCircuit H i a).frontierWord (!side)).reverse)

theorem germSunTopPorts_vertices
    (x y : (smoothedSigmaRimGermGraph t i a side).swapBoundary.Dart) :
    (germSunTopPorts t i a side m q L x).vertex = (germSunTopPorts t i a side m q L y).vertex ↔
      x.vertex = y.vertex :=
  (PortGraph.vertex_iff_of_rotation_equiv L.topPorts L.topPorts_rotation _ _).trans
    ((PortGraph.vertex_iff_of_rotation_equiv L.ports L.rotation _ _).trans
      ((q.ports_vertex_iff _ _).trans
        (PortGraph.vertex_iff_of_rotation_equiv (germSunInitialPorts t i a side m)
          (germSunInitialPorts_rotation t i a side m) x y)))

noncomputable def germSunQuadReplacement
    (hp : ∀ x : (smoothedSigmaRimGermGraph t i a side).swapBoundary.Dart,
      (numberedWheelCycleRetraction i).retract.edge
        (Port.label (smoothedSigmaRimGermGraph t i a side).swapBoundary.jointLabel x) =
          some (m.edge (Port.label (smoothedSigmaRimGermGraph t i a side).swapBoundary.jointLabel x))) :
    (smoothedSigmaRimGermGraph t i a side).swapBoundary.BoundaryQuadReplacement L.topGraph where
  ports := germSunTopPorts t i a side m q L
  boundary := germSunTopPorts_boundaryDart t i a side m q L
  vertices := germSunTopPorts_vertices t i a side m q L
  quadPath := germSunTopQuad t i a side m hw q L
  first := germSunTopQuad_firstDart t i a side m hw q L
  middle := germSunTopQuad_middleDart t i a side m hw q L
  last := germSunTopQuad_lastDart t i a side m hw q L
  pairs := germSunTopQuad_pairs t i a side m hw q L
  labels := germSunTopQuad_labels t i a side m q L hp

theorem smoothedSigmaRim_exists_structural_oriented_gluing [IsEmpty H.Joint]
    (hmin : d.Minimal) (hs : d.sign = 1) (hi : i ≠ oddWheelCycle) :
    ∃ side, ∃ m : GermSunRelabelling t i a side,
    ∃ hw : ((closedSigmaRimCircuit H i a).frontierWord (!side)).map m.edge =
        closedSigmaRimSunFrontierWord H i a (!side),
    ∃ K : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0))
        [] (((closedSigmaRimCircuit H i a).frontierWord (!side)).map m.edge).reverse,
    ∃ q : PortGraph.SunSwitchTrace (germSunInitialGraph t i a side m) K,
    ∃ L : IncludedWheelSun i K ((closedSigmaRimCircuit H i a).frontierWord (!side)).reverse,
      q.Inward (wheelCycles i).length_ge_three (germSunInitial_spokes t i a side m hw) ∧
      K.SunFaceState (wheelCycles i).length_ge_three (germSunInitial_spokes t i a side m hw) ∧
      Nonempty ((smoothedSigmaRimGermGraph t i a side).swapBoundary.BoundaryQuadReplacement L.topGraph) ∧
      (∑ h : L.graph.Hub, ([L.graph.hubLabel h] : Multiset (Fin 1417152))) =
        ((∑ h : (smoothedSigmaRimGermGraph t i a side).Hub,
          ([(smoothedSigmaRimGermGraph t i a side).hubLabel h] : Multiset (Fin 1417152))).filterMap
            (numberedWheelCycleRetraction i).retract.vertex).map (numberedWheelSunEmbedding i).vertex ∧
      Fintype.card (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.Hub = d.size ∧
      (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.sign = 1 ∧
      eulerDefect (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.pairing.perm
        (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.circuitStep = 0 ∧
      ∃ f : SigmaDiagram [] [],
        (f.labels : Multiset (Fin 1417152)) =
          (∑ h : (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.Hub,
            ([(L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.hubLabel h] : Multiset (Fin 1417152))) ∧
        f.size = d.size ∧ f.sign = 1 ∧ f.Minimal := by
  obtain ⟨side, m, hw, K, q, L, hp, hq, hK, hl, hn, hz⟩ :=
    smoothedSigmaRimGerm_exists_structural_normalization t i a hmin hs hi
  exact ⟨side, m, hw, K, q, L, hq, hK, ⟨germSunQuadReplacement t i a side m hw q L hp⟩, hl,
    includedSunOrientedGluing_hub_card t hmin hs i a side L hn,
    includedSunOrientedGluing_sign t hmin hs i a side L hz,
    includedSunOrientedGluing_euler t i a side L,
    includedSunOrientedGluing_exists_minimal_diagram t hmin hs i a side L hn hz⟩

end ThomGame.Construction

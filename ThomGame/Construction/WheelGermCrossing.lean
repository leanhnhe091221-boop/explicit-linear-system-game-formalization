module

public import ThomGame.Construction.WheelGermStructuralGluing
public import ThomGame.Pictures.QuadCrossingSmoothing

/-!
# Supported crossing faces in the actual Sigma replacement and smoothing

The replacement is the one obtained by normalizing the actual germ.
Any old facial circuit in the original composition whose replaced-side
face darts follow its outer quadrilaterals survives in the specific
oriented gluing reduction. All retained face darts and their labels are
accounted for exactly. WheelGermOldFaces derives this support for the
original crossing faces of distinct constellation indices.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures

variable {d : SigmaDiagram [] []} {H : SigmaGraph [] []} 
  (t : SigmaGraphWitness d H) [IsEmpty H.Joint] (i : WheelCycleIndex)
  (a : H.RimDart (numberedWheelCycles i)) (side : Bool)
  (m : GermSunRelabelling t i a side)
  (hw : ((closedSigmaRimCircuit H i a).frontierWord (!side)).map m.edge =
    closedSigmaRimSunFrontierWord H i a (!side))
  {K : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0))
    [] (((closedSigmaRimCircuit H i a).frontierWord (!side)).map m.edge).reverse}
  (q : PortGraph.SunSwitchTrace (germSunInitialGraph t i a side m) K)
  (L : IncludedWheelSun i K ((closedSigmaRimCircuit H i a).frontierWord (!side)).reverse)
  (hp : ∀ x : (smoothedSigmaRimGermGraph t i a side).swapBoundary.Dart,
    (numberedWheelCycleRetraction i).retract.edge
      (Port.label (smoothedSigmaRimGermGraph t i a side).swapBoundary.jointLabel x) =
        some (m.edge (Port.label (smoothedSigmaRimGermGraph t i a side).swapBoundary.jointLabel x)))

@[reducible] noncomputable def germOriginalOrientedComposition : SigmaGraph [] [] :=
  (smoothedSigmaRimRegionGraph t i a (!side)).swapBoundary.comp
    (smoothedSigmaRimGermGraph t i a side).swapBoundary

theorem germSun_crossing_face_survives
    (C : (germOriginalOrientedComposition t i a side).SimpleCircuit)
    (faceSide : Bool) (hc : C.SupportedByQuads faceSide) (hf : C.BoundsFaceOrbit faceSide)
    (hx : ∃ k x, C.port (k, faceSide) =
      PortGraph.compRightEmbedding (smoothedSigmaRimRegionGraph t i a (!side)).swapBoundary
        (smoothedSigmaRimGermGraph t i a side).swapBoundary x) :
    ∃ D : (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.SimpleCircuit,
      D.BoundsFaceOrbit false ∧
      (∀ j : Fin D.length, ∃ k : Fin C.length,
        (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).trace.portEmbedding (D.dart j) =
          (germSunQuadReplacement t i a side m hw q L hp).gluedPorts
            (smoothedSigmaRimRegionGraph t i a (!side)).swapBoundary (C.port (k, faceSide)) ∧
        Port.label (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.jointLabel (D.dart j) =
          Port.label (germOriginalOrientedComposition t i a side).jointLabel (C.port (k, faceSide))) ∧
      (∀ k : Fin C.length, (germOriginalOrientedComposition t i a side).Terminal (C.port (k, faceSide)) →
        ∃! j : Fin D.length,
          (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).trace.portEmbedding (D.dart j) =
            (germSunQuadReplacement t i a side m hw q L hp).gluedPorts
              (smoothedSigmaRimRegionGraph t i a (!side)).swapBoundary (C.port (k, faceSide))) := by
  let : IsEmpty (smoothedSigmaRimGermGraph t i a side).swapBoundary.Joint :=
    ⟨fun j => isEmptyElim (j.val : H.Joint)⟩
  let : IsEmpty L.topGraph.Joint := L.topGraph_noJoints
  let r := germSunQuadReplacement t i a side m hw q L hp
  let g := L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))
  obtain ⟨k₀, ha⟩ := PortGraph.SimpleCircuit.exists_terminal_of_quad_crossing
    (smoothedSigmaRimRegionGraph t i a (!side)).swapBoundary
    (smoothedSigmaRimGermGraph t i a side).swapBoundary C faceSide hc hf hx
  exact ⟨r.reducedCrossingCircuit C faceSide hc hf g k₀ ha,
    r.reducedCrossingCircuit_face C faceSide hc hf g k₀ ha,
    r.reducedCrossingCircuit_label C faceSide hc hf g k₀ ha,
    r.reducedCrossingCircuit_complete C faceSide hc hf g k₀ ha⟩

end ThomGame.Construction

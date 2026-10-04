module

public import ThomGame.Construction.WheelGermCrossing
public import ThomGame.Construction.WheelLiftedFaces
public import ThomGame.Pictures.GermFaceReplacement
public import ThomGame.Pictures.ExteriorFaceReplacement

/-!
# Original numbered crossing faces survive the actual sun replacement

The old face is specified in the original reduced Sigma graph. Its
lift, quadrilateral support, and retained-port correspondence are
proved, not additional hypotheses. This covers distinct constellation
indices and a specified crossing entry on the replaced germ's frontier.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures

variable {d : SigmaDiagram [] []} {H : SigmaGraph [] []} 
  (t : SigmaGraphWitness d H) [IsEmpty H.Joint] (hmin : d.Minimal) (hs : d.sign = 1)
  (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (s : Bool)

noncomputable def originalSigmaFaceLift (x : H.Dart) : (germOriginalOrientedComposition t i a s).Dart :=
  (closedSigmaRimCircuit H i a).orientedLiftPort
    (t.dualEuler)
    (reduced_minimal_odd_sigma_reachable t hmin hs) s x

variable (m : GermSunRelabelling t i a s)
  (hw : ((closedSigmaRimCircuit H i a).frontierWord (!s)).map m.edge =
    closedSigmaRimSunFrontierWord H i a (!s))
  {K : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0))
    [] (((closedSigmaRimCircuit H i a).frontierWord (!s)).map m.edge).reverse}
  (q : PortGraph.SunSwitchTrace (germSunInitialGraph t i a s m) K)
  (L : IncludedWheelSun i K ((closedSigmaRimCircuit H i a).frontierWord (!s)).reverse)
  (hp : ∀ x : (smoothedSigmaRimGermGraph t i a s).swapBoundary.Dart,
    (numberedWheelCycleRetraction i).retract.edge
      (Port.label (smoothedSigmaRimGermGraph t i a s).swapBoundary.jointLabel x) =
        some (m.edge (Port.label (smoothedSigmaRimGermGraph t i a s).swapBoundary.jointLabel x)))

theorem germSun_original_crossing_face_survives
    (j : WheelCycleIndex) (hij : i ≠ j) (b : H.RimDart (numberedWheelCycles j))
    (faceSide : Bool) (hf : (closedSigmaRimCircuit H j b).BoundsFaceOrbit faceSide)
    (entry : H.Dart) (he : (closedSigmaRimCircuit H i a).Frontier (!s) entry)
    (heface : H.circuitStep.SameCycle (H.pairing.twin entry)
      ((closedSigmaRimCircuit H j b).port (0, faceSide))) :
    ∃ F : (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s))).graph.SimpleCircuit,
      F.BoundsFaceOrbit false ∧
      (∀ k : Fin F.length, ∃ l : Fin (closedSigmaRimCircuit H j b).length,
        (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s))).trace.portEmbedding (F.dart k) =
          (germSunQuadReplacement t i a s m hw q L hp).gluedPorts
          (smoothedSigmaRimRegionGraph t i a (!s)).swapBoundary
          (originalSigmaFaceLift t hmin hs i a s ((closedSigmaRimCircuit H j b).port (l, faceSide))) ∧
        Port.label (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s))).graph.jointLabel (F.dart k) =
          Port.label H.jointLabel ((closedSigmaRimCircuit H j b).port (l, faceSide))) ∧
      (∀ l : Fin (closedSigmaRimCircuit H j b).length, ∃! k : Fin F.length,
        (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s))).trace.portEmbedding (F.dart k) =
          (germSunQuadReplacement t i a s m hw q L hp).gluedPorts
          (smoothedSigmaRimRegionGraph t i a (!s)).swapBoundary
          (originalSigmaFaceLift t hmin hs i a s ((closedSigmaRimCircuit H j b).port (l, faceSide)))) := by
  let : IsEmpty L.topGraph.Joint := L.topGraph_noJoints
  exact H.rimFace_replacement_survives (numberedWheelCycles i) (numberedWheelCycles j) a b
    (numberedWheelCycles_intersection_unique i j hij)
    (t.dualEuler)
    (reduced_minimal_odd_sigma_reachable t hmin hs) s faceSide hf entry he heface
    (germSunQuadReplacement t i a s m hw q L hp)
    (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s)))

/-- One specified replacement preserves every original crossing face with a distinct
constellation index. The equivalence records the actual original ports and labels. -/
def GermSunPreservesOriginalCrossingFaces : Prop :=
  ∀ (j : WheelCycleIndex), i ≠ j → ∀ (b : H.RimDart (numberedWheelCycles j))
    (faceSide : Bool), (closedSigmaRimCircuit H j b).BoundsFaceOrbit faceSide →
    ∀ (entry : H.Dart), (closedSigmaRimCircuit H i a).Frontier (!s) entry →
    H.circuitStep.SameCycle (H.pairing.twin entry)
      ((closedSigmaRimCircuit H j b).port (0, faceSide)) →
    ∃ F : (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s))).graph.SimpleCircuit,
      F.BoundsFaceOrbit false ∧ F.length = (closedSigmaRimCircuit H j b).length ∧
      ∃ e : Fin F.length ≃ Fin (closedSigmaRimCircuit H j b).length,
        ∀ k : Fin F.length,
          (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s))).trace.portEmbedding (F.dart k) =
            (germSunQuadReplacement t i a s m hw q L hp).gluedPorts
              (smoothedSigmaRimRegionGraph t i a (!s)).swapBoundary
              (originalSigmaFaceLift t hmin hs i a s
                ((closedSigmaRimCircuit H j b).port (e k, faceSide))) ∧
          Port.label (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s))).graph.jointLabel (F.dart k) =
            Port.label H.jointLabel ((closedSigmaRimCircuit H j b).port (e k, faceSide))

theorem germSun_preserves_original_crossing_faces :
    GermSunPreservesOriginalCrossingFaces t hmin hs i a s m hw q L hp := by
  intro j hij b faceSide hf entry he heface
  let : IsEmpty L.topGraph.Joint := L.topGraph_noJoints
  exact H.rimFace_replacement_survives_equiv (numberedWheelCycles i) (numberedWheelCycles j) a b
    (numberedWheelCycles_intersection_unique i j hij)
    (t.dualEuler)
    (reduced_minimal_odd_sigma_reachable t hmin hs) s faceSide hf entry he heface
    (germSunQuadReplacement t i a s m hw q L hp)
    (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s)))

/-- Every original face whose vertices avoid the germ survives this replacement.
There is no restriction on its labels or constellation index. -/
def GermSunPreservesExteriorFaces : Prop :=
  ∀ (D : H.SimpleCircuit) (faceSide : Bool), D.BoundsFaceOrbit faceSide →
    (∀ k : Fin D.length, ¬ (closedSigmaRimCircuit H i a).GermVertex s
      (D.port (k, faceSide)).vertex) →
    ∃ F : (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s))).graph.SimpleCircuit,
      F.BoundsFaceOrbit false ∧ F.length = D.length ∧
      ∃ e : Fin F.length ≃ Fin D.length, ∀ k : Fin F.length,
        (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s))).trace.portEmbedding (F.dart k) =
          (germSunQuadReplacement t i a s m hw q L hp).gluedPorts
            (smoothedSigmaRimRegionGraph t i a (!s)).swapBoundary
            (originalSigmaFaceLift t hmin hs i a s (D.port (e k, faceSide))) ∧
        Port.label (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s))).graph.jointLabel (F.dart k) =
          Port.label H.jointLabel (D.port (e k, faceSide))

theorem germSun_preserves_exterior_faces :
    GermSunPreservesExteriorFaces t hmin hs i a s m hw q L hp := by
  intro D faceSide hf hout
  let : IsEmpty L.topGraph.Joint := L.topGraph_noJoints
  exact (closedSigmaRimCircuit H i a).exteriorFace_replacement_survives
    (t.dualEuler) s
    (reduced_minimal_odd_sigma_reachable t hmin hs) D faceSide hf hout
    (germSunQuadReplacement t i a s m hw q L hp)
    (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s)))

end ThomGame.Construction

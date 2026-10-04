module

public import ThomGame.Construction.WheelExteriorCircuitRecovery
public import ThomGame.Construction.WheelGermOldFaces
public import ThomGame.Pictures.RimSeamFace

/-!
# One actual normalization preserves faciality for every other index

Every target circuit is covered: the exterior case recovers in the
original graph, the interior sun case is excluded, and the seam case
shares an actual preserved old facial rim edge. This supplies the
other-index preservation required by the descent in Lemma 11.8.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures PortGraph

variable {d : SigmaDiagram [] []} {H : SigmaGraph [] []} 
  (t : SigmaGraphWitness d H) [IsEmpty H.Joint] (hmin : d.Minimal) (hs : d.sign = 1)
  (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (s : Bool)
  (m : GermSunRelabelling t i a s)
  (hw : ((closedSigmaRimCircuit H i a).frontierWord (!s)).map m.edge =
    closedSigmaRimSunFrontierWord H i a (!s))
  {K : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0))
    [] (((closedSigmaRimCircuit H i a).frontierWord (!s)).map m.edge).reverse}
  (q : SunSwitchTrace (germSunInitialGraph t i a s m) K)
  (L : IncludedWheelSun i K ((closedSigmaRimCircuit H i a).frontierWord (!s)).reverse)
  (hp : ∀ x : (smoothedSigmaRimGermGraph t i a s).swapBoundary.Dart,
    (numberedWheelCycleRetraction i).retract.edge
      (Port.label (smoothedSigmaRimGermGraph t i a s).swapBoundary.jointLabel x) =
        some (m.edge (Port.label (smoothedSigmaRimGermGraph t i a s).swapBoundary.jointLabel x)))

include hmin hs m hw q hp in
theorem germSun_seam_circuit_facial (j : WheelCycleIndex) (hij : i ≠ j)
    (hfaces : ∀ b : H.RimDart (numberedWheelCycles j),
      ∃ side, (closedSigmaRimCircuit H j b).BoundsFaceOrbit side)
    (C : (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s))).graph.SimpleCircuit)
    (hlabels : ∀ k : Fin C.length,
      Port.label (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s))).graph.jointLabel
        (C.dart k) ∈ Set.range (numberedWheelCycles j).edge)
    (hseam : (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s))).MeetsSeam C) :
    ∃ side, C.BoundsFaceOrbit side := by
  let : IsEmpty L.topGraph.Joint := L.topGraph_noJoints
  exact H.rim_circuit_facial_of_meets_seam (numberedWheelCycles i) (numberedWheelCycles j) a
    (numberedWheelCycles_intersection_unique i j hij)
    (t.dualEuler)
    (reduced_minimal_odd_sigma_reachable t hmin hs) s hfaces
    (germSunQuadReplacement t i a s m hw q L hp)
    (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s)))
    ((L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s))).graph.dualEuler_eq_twice_components
      (includedSunOrientedGluing_euler t i a s L)) C hlabels hseam

include hmin hs m hw q hp in
theorem germSun_other_circuit_facial
    (hK : K.SunFaceState (wheelCycles i).length_ge_three (germSunInitial_spokes t i a s m hw))
    (j : WheelCycleIndex) (hij : i ≠ j)
    (hfaces : ∀ b : H.RimDart (numberedWheelCycles j),
      ∃ side, (closedSigmaRimCircuit H j b).BoundsFaceOrbit side)
    (C : (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s))).graph.SimpleCircuit)
    (hlabels : ∀ k : Fin C.length,
      Port.label (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s))).graph.jointLabel
        (C.dart k) ∈ Set.range (numberedWheelCycles j).edge) :
    ∃ side, C.BoundsFaceOrbit side := by
  let : IsEmpty (smoothedSigmaRimRegionGraph t i a (!s)).Joint := ⟨fun x => isEmptyElim x.val⟩
  rcases L.oriented_other_circuit_seam_or_exterior _ hK j hij C hlabels with hseam | hleft
  · exact germSun_seam_circuit_facial t hmin hs i a s m hw q L hp j hij hfaces C hlabels hseam
  · exact includedSunOrientedGluing_exterior_facial t i a s L C j hfaces hlabels hleft

include hmin hs m hw q hp in
theorem germSun_other_rims_facial
    (hK : K.SunFaceState (wheelCycles i).length_ge_three (germSunInitial_spokes t i a s m hw))
    (j : WheelCycleIndex) (hij : i ≠ j)
    (hfaces : ∀ b : H.RimDart (numberedWheelCycles j),
      ∃ side, (closedSigmaRimCircuit H j b).BoundsFaceOrbit side)
    (b : (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s))).graph.RimDart (numberedWheelCycles j)) :
    ∃ side, (closedSigmaRimCircuit (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s))).graph j b).BoundsFaceOrbit side :=
  germSun_other_circuit_facial t hmin hs i a s m hw q L hp hK j hij hfaces _
    ((L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s))).graph.rimSimpleCircuit_rim
      (numberedWheelCycles j) (by simp) (by simp) b)

end ThomGame.Construction

module

public import ThomGame.Construction.WheelGermOldFaces

/-!
# A single actual normalization preserves original crossing and exterior faces

The side, relabelling, finite inward-switch trace and inclusion are
constructed on the actual Sigma graph using an Euler/size/sign witness
from a minimal odd diagram. The historical `smoothed` names include
this general input, without requiring a smoothing. For that same chosen
replacement, every original crossing facial circuit with a distinct
constellation index survives, with a bijection of its original ports,
unchanged labels and unchanged length. Every original face disjoint from
the germ survives under the same replacement, without restrictions on
its labels or constellation index. The resulting graph retains the
size and odd sign, satisfies the Euler equality, and has a minimal
diagram with exactly its relation multiset.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures RibbonConnectivity
open scoped BigOperators

variable {d : SigmaDiagram [] []} {H : SigmaGraph [] []} 
  (t : SigmaGraphWitness d H) [IsEmpty H.Joint]
  (hmin : d.Minimal) (hs : d.sign = 1)
  (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i))

theorem smoothedSigmaRim_exists_face_preserving_normalization (hi : i ≠ oddWheelCycle) :
    ∃ side, ∃ m : GermSunRelabelling t i a side,
    ∃ hw : ((closedSigmaRimCircuit H i a).frontierWord (!side)).map m.edge =
        closedSigmaRimSunFrontierWord H i a (!side),
    ∃ K : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0))
        [] (((closedSigmaRimCircuit H i a).frontierWord (!side)).map m.edge).reverse,
    ∃ q : PortGraph.SunSwitchTrace (germSunInitialGraph t i a side m) K,
    ∃ L : IncludedWheelSun i K ((closedSigmaRimCircuit H i a).frontierWord (!side)).reverse,
    ∃ hp : ∀ x : (smoothedSigmaRimGermGraph t i a side).swapBoundary.Dart,
        (numberedWheelCycleRetraction i).retract.edge
          (Port.label (smoothedSigmaRimGermGraph t i a side).swapBoundary.jointLabel x) =
            some (m.edge (Port.label (smoothedSigmaRimGermGraph t i a side).swapBoundary.jointLabel x)),
      q.Inward (wheelCycles i).length_ge_three (germSunInitial_spokes t i a side m hw) ∧
      K.SunFaceState (wheelCycles i).length_ge_three (germSunInitial_spokes t i a side m hw) ∧
      GermSunPreservesOriginalCrossingFaces t hmin hs i a side m hw q L hp ∧
      GermSunPreservesExteriorFaces t hmin hs i a side m hw q L hp ∧
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
  exact ⟨side, m, hw, K, q, L, hp, hq, hK,
    germSun_preserves_original_crossing_faces t hmin hs i a side m hw q L hp,
    germSun_preserves_exterior_faces t hmin hs i a side m hw q L hp, hl,
    includedSunOrientedGluing_hub_card t hmin hs i a side L hn,
    includedSunOrientedGluing_sign t hmin hs i a side L hz,
    includedSunOrientedGluing_euler t i a side L,
    includedSunOrientedGluing_exists_minimal_diagram t hmin hs i a side L hn hz⟩

end ThomGame.Construction

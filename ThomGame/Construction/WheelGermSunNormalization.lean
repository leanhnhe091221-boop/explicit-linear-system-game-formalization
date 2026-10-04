module

public import ThomGame.Construction.WheelGermSunGraph
public import ThomGame.Construction.WheelSunOrientedGluing
public import ThomGame.Pictures.SunSwitchPortTrace

/-!
# Normalizing the actual germ and including its retained quadrilaterals

The finite inward-switch algorithm starts at the relabelled actual germ.
Its port correspondence extends through all switches and the inclusion
back into Sigma. Every outer quadrilateral retains its three specified
ports and both ends of each edge. Labels follow the retraction and
inclusion; proving this composite fixes original quadrilateral labels
requires the separate neighbourhood-incidence argument.
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

include hw in
theorem germSunInitial_spokes :
    ∀ z ∈ (((closedSigmaRimCircuit H i a).frontierWord (!side)).map m.edge).reverse,
      ∃ j, z = Sum.inl j := by
  rw [hw]
  exact closedSigmaRimSunFrontierWord_reverse_spokes H i a (!side)

include hw in
theorem germSunInitial_boundary_spokes :
    ∀ j, ∃ k, Port.label (germSunInitialGraph t i a side m).jointLabel
      ((germSunInitialGraph t i a side m).boundaryDart j) = Sum.inl k := by
  intro j
  cases j with
  | inl k => exact k.elim0
  | inr k => exact germSunInitial_spokes t i a side m hw _ (List.get_mem _ k)

variable {K : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0))
    [] (((closedSigmaRimCircuit H i a).frontierWord (!side)).map m.edge).reverse}
  (q : PortGraph.SunSwitchTrace (germSunInitialGraph t i a side m) K)
  (L : IncludedWheelSun i K ((closedSigmaRimCircuit H i a).frontierWord (!side)).reverse)

noncomputable def germSunNormalizedPorts :
    (smoothedSigmaRimGermGraph t i a side).swapBoundary.Dart ≃ L.graph.Dart :=
  (germSunInitialPorts t i a side m).trans (q.ports.trans L.ports)

theorem germSunNormalizedPorts_label
    (x : (smoothedSigmaRimGermGraph t i a side).swapBoundary.Dart) :
    Port.label L.graph.jointLabel (germSunNormalizedPorts t i a side m q L x) =
      (numberedWheelSunEmbedding i).edge
        (m.edge (Port.label (smoothedSigmaRimGermGraph t i a side).swapBoundary.jointLabel x)) :=
  (L.label _).trans (congrArg (numberedWheelSunEmbedding i).edge
    ((q.ports_label _).trans (germSunInitialPorts_label t i a side m x)))

noncomputable def germSunNormalizedQuad
    (p : (smoothedSigmaRimGermGraph t i a side).swapBoundary.BoundaryQuadPath) :
    L.graph.BoundaryQuadPath :=
  L.quadPath (q.quadPath (germSunInitial_boundary_spokes t i a side m hw)
    (germSunInitialQuad t i a side m p))

theorem germSunNormalizedQuad_firstDart
    (p : (smoothedSigmaRimGermGraph t i a side).swapBoundary.BoundaryQuadPath) :
    (germSunNormalizedQuad t i a side m hw q L p).firstDart =
      germSunNormalizedPorts t i a side m q L p.firstDart :=
  (L.quadPath_first _).trans (congrArg L.ports
    ((q.quadPath_firstDart _ _).trans (congrArg q.ports (germSunInitialQuad_firstDart t i a side m p))))

theorem germSunNormalizedQuad_middleDart
    (p : (smoothedSigmaRimGermGraph t i a side).swapBoundary.BoundaryQuadPath) :
    (germSunNormalizedQuad t i a side m hw q L p).middleDart =
      germSunNormalizedPorts t i a side m q L p.middleDart :=
  (L.quadPath_middle _).trans (congrArg L.ports
    ((q.quadPath_middleDart _ _).trans (congrArg q.ports (germSunInitialQuad_middleDart t i a side m p))))

theorem germSunNormalizedQuad_lastDart
    (p : (smoothedSigmaRimGermGraph t i a side).swapBoundary.BoundaryQuadPath) :
    (germSunNormalizedQuad t i a side m hw q L p).lastDart =
      germSunNormalizedPorts t i a side m q L p.lastDart :=
  (L.quadPath_last _).trans (congrArg L.ports
    ((q.quadPath_lastDart _ _).trans (congrArg q.ports (germSunInitialQuad_lastDart t i a side m p))))

include hw in
theorem germSunNormalizedQuad_pairs
    (p : (smoothedSigmaRimGermGraph t i a side).swapBoundary.BoundaryQuadPath)
    (x : (smoothedSigmaRimGermGraph t i a side).swapBoundary.Dart)
    (hx : x ∈ [p.firstDart, p.middleDart, p.lastDart]) :
    L.graph.pairing.twin (germSunNormalizedPorts t i a side m q L x) =
      germSunNormalizedPorts t i a side m q L
        ((smoothedSigmaRimGermGraph t i a side).swapBoundary.pairing.twin x) := by
  have hxi : germSunInitialPorts t i a side m x ∈
      [(germSunInitialQuad t i a side m p).firstDart,
        (germSunInitialQuad t i a side m p).middleDart,
        (germSunInitialQuad t i a side m p).lastDart] := by
    rw [germSunInitialQuad_firstDart, germSunInitialQuad_middleDart, germSunInitialQuad_lastDart]
    simpa only [List.mem_cons, List.not_mem_nil, or_false, Equiv.apply_eq_iff_eq] using hx
  exact (L.twin _).trans (congrArg L.ports
    ((q.quad_pairs_preserved (germSunInitial_boundary_spokes t i a side m hw) _ _ hxi).trans
      (congrArg q.ports (germSunInitialPorts_twin t i a side m x))))

theorem smoothedSigmaRimGerm_exists_structural_normalization [IsEmpty H.Joint]
    (hmin : d.Minimal) (hs : d.sign = 1) (hi : i ≠ oddWheelCycle) :
    ∃ side, ∃ m : GermSunRelabelling t i a side,
    ∃ hw : ((closedSigmaRimCircuit H i a).frontierWord (!side)).map m.edge =
        closedSigmaRimSunFrontierWord H i a (!side),
    ∃ K : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0))
        [] (((closedSigmaRimCircuit H i a).frontierWord (!side)).map m.edge).reverse,
    ∃ q : PortGraph.SunSwitchTrace (germSunInitialGraph t i a side m) K,
    ∃ L : IncludedWheelSun i K ((closedSigmaRimCircuit H i a).frontierWord (!side)).reverse,
      (∀ x : (smoothedSigmaRimGermGraph t i a side).swapBoundary.Dart,
        (numberedWheelCycleRetraction i).retract.edge
          (Port.label (smoothedSigmaRimGermGraph t i a side).swapBoundary.jointLabel x) =
            some (m.edge (Port.label (smoothedSigmaRimGermGraph t i a side).swapBoundary.jointLabel x))) ∧
      q.Inward (wheelCycles i).length_ge_three (germSunInitial_spokes t i a side m hw) ∧
      K.SunFaceState (wheelCycles i).length_ge_three (germSunInitial_spokes t i a side m hw) ∧
      (∑ h : L.graph.Hub, ([L.graph.hubLabel h] : Multiset (Fin 1417152))) =
        ((∑ h : (smoothedSigmaRimGermGraph t i a side).Hub,
          ([(smoothedSigmaRimGermGraph t i a side).hubLabel h] : Multiset (Fin 1417152))).filterMap
            (numberedWheelCycleRetraction i).retract.vertex).map (numberedWheelSunEmbedding i).vertex ∧
      Fintype.card L.graph.Hub = Fintype.card (smoothedSigmaRimGermGraph t i a side).Hub ∧
      (smoothedSigmaRimGermGraph t i a side).sign = 0 := by
  obtain ⟨side, m, hw, hp, hl, hm, hz⟩ :=
    smoothedSigmaRimGerm_exists_structural_sun t i a hmin hs hi
  let : IsEmpty (germSunInitialGraph t i a side m).Joint := germSunInitialGraph_noJoints t i a side m
  obtain ⟨K, q, hq, hK, hf, hkl, hkn, _⟩ := hm.exists_facial_cover_switches_of_connected
    (germSunInitialGraph_connected t i a side m) (wheelCycles i).length_ge_three
      (germSunInitial_spokes t i a side m hw)
  have hmap : ((((closedSigmaRimCircuit H i a).frontierWord (!side)).map m.edge).reverse).map
      (numberedWheelSunEmbedding i).edge =
        ((closedSigmaRimCircuit H i a).frontierWord (!side)).reverse := by
    rw [hw, List.map_reverse]
    exact congrArg List.reverse (closedSigmaRimSunFrontierWord_map H i a (!side))
  let L := includeWheelSunAtFrontier i K _ hmap hi (germSunInitial_spokes t i a side m hw) hK hf
  refine ⟨side, m, hw, K, q, L, ?_, hq, hK,
    L.hub_relations.trans (congrArg (Multiset.map (numberedWheelSunEmbedding i).vertex) (hkl.trans hl)),
    L.hub_card.trans (hkn.trans (germSunInitialGraph_hub_card t i a side m)), hz⟩
  intro x
  exact (hp x).trans (congrArg some (germSunInitialPorts_label t i a side m x))

end ThomGame.Construction

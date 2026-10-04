module

public import ThomGame.Construction.WheelCycleSeparation
public import ThomGame.Construction.WheelGraphWitness
public import ThomGame.Pictures.CycleFrontier
public import ThomGame.Pictures.CircuitRegionPartition

/-!
# Ordered region graphs for the actual central rims and pentagons

The diagram Euler theorem supplies every premise for extracting the two
region port graphs. Their labels are still actual numbered matrix rows
and columns, and their boundary words avoid the selected hypergraph rim.
The same construction applies to every certified smoothed diagram.
Diagram witnesses with the exact boundary and interior relation multiset
are supplied separately in `WheelRegionDiagrams`; no graph isomorphism is
asserted by either result.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures Pictures.RibbonConnectivity

theorem closedSigmaRimFrontierWord_no_rim (G : SigmaGraph [] []) (i : WheelCycleIndex)
    (a : G.RimDart (numberedWheelCycles i)) (s : Bool) :
    ∀ z ∈ (closedSigmaRimCircuit G i a).frontierWord s, z ∉ Set.range (numberedWheelCycles i).edge :=
  G.rimSimpleCircuit_frontierWord_no_rim _ (by simp) (by simp) a s

@[reducible] noncomputable def closedSigmaRimRegionGraph (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) (s : Bool) :
    SigmaGraph ((closedSigmaRimCircuit d.graph i a).frontierWord s) [] :=
  (closedSigmaRimCircuit d.graph i a).regionGraph d.graph_dualEuler s

noncomputable def closedSigmaRimRegionPorts (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) (s : Bool) :
    (closedSigmaRimRegionGraph d i a s).Dart ≃
      Subtype ((closedSigmaRimCircuit d.graph i a).KeptDart s) :=
  (closedSigmaRimCircuit d.graph i a).regionPorts d.graph_dualEuler s

theorem closedSigmaRimRegionGraph_twin (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) (s : Bool)
    (b : (closedSigmaRimRegionGraph d i a s).Dart) :
    (closedSigmaRimRegionPorts d i a s ((closedSigmaRimRegionGraph d i a s).pairing.twin b)).val =
      d.graph.pairing.twin (closedSigmaRimRegionPorts d i a s b).val :=
  (closedSigmaRimCircuit d.graph i a).regionGraph_twin d.graph_dualEuler s b

theorem closedSigmaRimRegionGraph_character (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) (s : Bool) (r : Fin 1417152) :
    (closedSigmaRimRegionGraph d i a s).character r =
      (Nat.card {h : d.graph.Hub //
        (closedSigmaRimCircuit d.graph i a).InteriorVertex s (.inr (.inl h)) ∧
          d.graph.hubLabel h = r} : ZMod 2) :=
  (closedSigmaRimCircuit d.graph i a).regionGraph_character d.graph_dualEuler s r

@[reducible] noncomputable def smoothedSigmaRimRegionGraph {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (h : SigmaGraphWitness d H)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (s : Bool) :
    SigmaGraph ((closedSigmaRimCircuit H i a).frontierWord s) [] :=
  (closedSigmaRimCircuit H i a).regionGraph (h.dualEuler) s

noncomputable def smoothedSigmaRimRegionPorts {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (h : SigmaGraphWitness d H)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (s : Bool) :
    (smoothedSigmaRimRegionGraph h i a s).Dart ≃
      Subtype ((closedSigmaRimCircuit H i a).KeptDart s) :=
  (closedSigmaRimCircuit H i a).regionPorts (h.dualEuler) s

theorem smoothedSigmaRimRegionGraph_twin {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (h : SigmaGraphWitness d H)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (s : Bool)
    (b : (smoothedSigmaRimRegionGraph h i a s).Dart) :
    (smoothedSigmaRimRegionPorts h i a s ((smoothedSigmaRimRegionGraph h i a s).pairing.twin b)).val =
      H.pairing.twin (smoothedSigmaRimRegionPorts h i a s b).val :=
  (closedSigmaRimCircuit H i a).regionGraph_twin
    (h.dualEuler) s b

end ThomGame.Construction

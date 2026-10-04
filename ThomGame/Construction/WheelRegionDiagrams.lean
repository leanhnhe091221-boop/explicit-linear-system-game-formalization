module

public import ThomGame.Construction.WheelRegionGraph
public import ThomGame.Pictures.CircuitRegionDiagram

/-!
# Actual numbered-wheel region diagrams

The region on either side of every lifted central rim or pentagon has
a genuine diagram on its exact frontier word. All interior row labels,
hub counts, and signs are preserved. No connectivity condition is added,
and the result also covers every certified smoothing of the input.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures
open scoped BigOperators

theorem closedSigmaRimRegion_exists_diagram (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) (s : Bool) :
    ∃ e : SigmaDiagram ((closedSigmaRimCircuit d.graph i a).frontierWord s) [],
      (e.labels : Multiset (Fin 1417152)) =
        (∑ h : (closedSigmaRimRegionGraph d i a s).Hub,
          ([(closedSigmaRimRegionGraph d i a s).hubLabel h] : Multiset (Fin 1417152))) ∧
      e.size = Fintype.card (closedSigmaRimRegionGraph d i a s).Hub ∧
      e.sign = (closedSigmaRimRegionGraph d i a s).sign :=
  (closedSigmaRimCircuit d.graph i a).exists_region_diagram_preserving d.graph_dualEuler s
    (fun _ => by change 0 < 3; omega)

theorem smoothedSigmaRimRegion_exists_diagram {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (t : SigmaGraphWitness d H)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (s : Bool) :
    ∃ e : SigmaDiagram ((closedSigmaRimCircuit H i a).frontierWord s) [],
      (e.labels : Multiset (Fin 1417152)) =
        (∑ h : (smoothedSigmaRimRegionGraph t i a s).Hub,
          ([(smoothedSigmaRimRegionGraph t i a s).hubLabel h] : Multiset (Fin 1417152))) ∧
      e.size = Fintype.card (smoothedSigmaRimRegionGraph t i a s).Hub ∧
      e.sign = (smoothedSigmaRimRegionGraph t i a s).sign :=
  (closedSigmaRimCircuit H i a).exists_region_diagram_preserving
    (t.dualEuler) s (fun _ => by change 0 < 3; omega)

end ThomGame.Construction

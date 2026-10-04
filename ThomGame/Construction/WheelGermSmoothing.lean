module

public import ThomGame.Construction.WheelGermGraph
public import ThomGame.Pictures.CircuitGermRecovery

/-!
# Certified recovery of actual numbered wheel components

The germ-region composition of every lifted central rim or pentagon has
an ordinary smoothing trace which deletes only its seam junctions and
loses no circles. The recovered graph has exactly the original component's
ports, edge pairing, port labels and rotations. Certified smoothed input
diagrams have the same recovery construction.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures Pictures.RibbonConnectivity
open scoped BigOperators

noncomputable def closedSigmaRimReduction (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) (s : Bool) :
    SelectedReduction (closedSigmaRimGluedGraph d i a s)
      ((closedSigmaRimCircuit d.graph i a).GluedSeam d.graph_dualEuler s) :=
  (closedSigmaRimCircuit d.graph i a).germReduction d.graph_dualEuler s

@[reducible] noncomputable def closedSigmaRecoveredGraph (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) (s : Bool) : SigmaGraph [] [] :=
  (closedSigmaRimReduction d i a s).graph

noncomputable def closedSigmaRecoveryTrace (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) (s : Bool) :
    Smoothing (closedSigmaRimGluedGraph d i a s) (closedSigmaRecoveredGraph d i a s) [] :=
  (closedSigmaRimReduction d i a s).trace

noncomputable def closedSigmaRecoveredPorts (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) (s : Bool) :
    (closedSigmaRecoveredGraph d i a s).Dart ≃ {b : d.graph.Dart //
      Connected d.graph.circuitStep d.graph.pairing.perm b (closedSigmaRimCircuit d.graph i a).cutBase} :=
  (closedSigmaRimCircuit d.graph i a).recoveredPorts d.graph_dualEuler s

theorem closedSigmaRecoveredPorts_twin (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) (s : Bool) (b : (closedSigmaRecoveredGraph d i a s).Dart) :
    (closedSigmaRecoveredPorts d i a s ((closedSigmaRecoveredGraph d i a s).pairing.twin b)).val =
      d.graph.pairing.twin (closedSigmaRecoveredPorts d i a s b).val :=
  (closedSigmaRimCircuit d.graph i a).recoveredPorts_twin d.graph_dualEuler s b

theorem closedSigmaRecoveredPorts_label (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) (s : Bool) (b : (closedSigmaRecoveredGraph d i a s).Dart) :
    Port.label d.graph.jointLabel (closedSigmaRecoveredPorts d i a s b).val =
      Port.label (closedSigmaRecoveredGraph d i a s).jointLabel b :=
  (closedSigmaRimCircuit d.graph i a).recoveredPorts_label d.graph_dualEuler s b

theorem closedSigmaRecoveredPorts_rotation (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) (s : Bool) (b : (closedSigmaRecoveredGraph d i a s).Dart) :
    (closedSigmaRecoveredPorts d i a s ((closedSigmaRecoveredGraph d i a s).rotation b)).val =
      d.graph.rotation (closedSigmaRecoveredPorts d i a s b).val :=
  (closedSigmaRimCircuit d.graph i a).recoveredPorts_rotation d.graph_dualEuler s b

theorem closedSigmaRecoveredPorts_vertex_iff (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) (s : Bool)
    (b c : (closedSigmaRecoveredGraph d i a s).Dart) :
    b.vertex = c.vertex ↔ (closedSigmaRecoveredPorts d i a s b).val.vertex =
      (closedSigmaRecoveredPorts d i a s c).val.vertex :=
  (closedSigmaRimCircuit d.graph i a).recoveredPorts_vertex_iff d.graph_dualEuler s b c

theorem closedSigmaRecoveredGraph_sign (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) (s : Bool) :
    (closedSigmaRecoveredGraph d i a s).sign =
      ∑ h : (closedSigmaRimCircuit d.graph i a).ComponentHub, numberedSystem.rhs (d.graph.hubLabel h.val) :=
  (closedSigmaRecoveryTrace d i a s).sign.trans (closedSigmaRimGluedGraph_sign d i a s)

noncomputable def smoothedSigmaRimReduction {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (h : SigmaGraphWitness d H)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (s : Bool) :
    SelectedReduction (smoothedSigmaRimGluedGraph h i a s)
      ((closedSigmaRimCircuit H i a).GluedSeam (h.dualEuler) s) :=
  (closedSigmaRimCircuit H i a).germReduction (h.dualEuler) s

@[reducible] noncomputable def smoothedSigmaRecoveredGraph {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (h : SigmaGraphWitness d H)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (s : Bool) : SigmaGraph [] [] :=
  (smoothedSigmaRimReduction h i a s).graph

noncomputable def smoothedSigmaRecoveryTrace {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (h : SigmaGraphWitness d H)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (s : Bool) :
    Smoothing (smoothedSigmaRimGluedGraph h i a s) (smoothedSigmaRecoveredGraph h i a s) [] :=
  (smoothedSigmaRimReduction h i a s).trace

noncomputable def smoothedSigmaRecoveredPorts {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (h : SigmaGraphWitness d H)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (s : Bool) :
    (smoothedSigmaRecoveredGraph h i a s).Dart ≃ {b : H.Dart //
      Connected H.circuitStep H.pairing.perm b (closedSigmaRimCircuit H i a).cutBase} :=
  (closedSigmaRimCircuit H i a).recoveredPorts (h.dualEuler) s

theorem smoothedSigmaRecoveredPorts_twin {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (h : SigmaGraphWitness d H)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (s : Bool)
    (b : (smoothedSigmaRecoveredGraph h i a s).Dart) :
    (smoothedSigmaRecoveredPorts h i a s ((smoothedSigmaRecoveredGraph h i a s).pairing.twin b)).val =
      H.pairing.twin (smoothedSigmaRecoveredPorts h i a s b).val :=
  (closedSigmaRimCircuit H i a).recoveredPorts_twin (h.dualEuler) s b

theorem smoothedSigmaRecoveredPorts_rotation {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (h : SigmaGraphWitness d H)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (s : Bool)
    (b : (smoothedSigmaRecoveredGraph h i a s).Dart) :
    (smoothedSigmaRecoveredPorts h i a s ((smoothedSigmaRecoveredGraph h i a s).rotation b)).val =
      H.rotation (smoothedSigmaRecoveredPorts h i a s b).val :=
  (closedSigmaRimCircuit H i a).recoveredPorts_rotation
    (h.dualEuler) s b

end ThomGame.Construction

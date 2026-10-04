module

public import ThomGame.Construction.WheelMinimalGerm
public import ThomGame.Construction.WheelGermSmoothing
public import ThomGame.Pictures.ReducedMinimalRecovery

/-! # Whole-graph port recovery for reduced minimal odd numbered diagrams -/

@[expose] public section
namespace ThomGame.Construction

open Pictures

variable {d : SigmaDiagram [] []} {H : SigmaGraph [] []} 
  (t : SigmaGraphWitness d H) [IsEmpty H.Joint] (hmin : d.Minimal) (hs : d.sign = 1)

include t hmin hs in
theorem reduced_minimal_odd_sigma_reachable : ∀ x y : H.Vertex, H.Reachable x y :=
  t.minimal_odd_reduced_reachable hmin hs

noncomputable def minimalSigmaRecoveredAllPorts (i : WheelCycleIndex)
    (a : H.RimDart (numberedWheelCycles i)) (s : Bool) :
    (smoothedSigmaRecoveredGraph t i a s).Dart ≃ H.Dart :=
  t.minimal_odd_recoveredAllPorts hmin hs
    (closedSigmaRimCircuit H i a) s

theorem minimalSigmaRecoveredAllPorts_twin (i : WheelCycleIndex)
    (a : H.RimDart (numberedWheelCycles i)) (s : Bool)
    (b : (smoothedSigmaRecoveredGraph t i a s).Dart) :
    minimalSigmaRecoveredAllPorts t hmin hs i a s ((smoothedSigmaRecoveredGraph t i a s).pairing.twin b) =
      H.pairing.twin (minimalSigmaRecoveredAllPorts t hmin hs i a s b) :=
  (closedSigmaRimCircuit H i a).recoveredAllPorts_twin
    (t.dualEuler)
    (reduced_minimal_odd_sigma_reachable t hmin hs) s b

theorem minimalSigmaRecoveredAllPorts_label (i : WheelCycleIndex)
    (a : H.RimDart (numberedWheelCycles i)) (s : Bool)
    (b : (smoothedSigmaRecoveredGraph t i a s).Dart) :
    Port.label H.jointLabel (minimalSigmaRecoveredAllPorts t hmin hs i a s b) =
      Port.label (smoothedSigmaRecoveredGraph t i a s).jointLabel b :=
  (closedSigmaRimCircuit H i a).recoveredAllPorts_label
    (t.dualEuler)
    (reduced_minimal_odd_sigma_reachable t hmin hs) s b

theorem minimalSigmaRecoveredAllPorts_rotation (i : WheelCycleIndex)
    (a : H.RimDart (numberedWheelCycles i)) (s : Bool)
    (b : (smoothedSigmaRecoveredGraph t i a s).Dart) :
    minimalSigmaRecoveredAllPorts t hmin hs i a s ((smoothedSigmaRecoveredGraph t i a s).rotation b) =
      H.rotation (minimalSigmaRecoveredAllPorts t hmin hs i a s b) :=
  (closedSigmaRimCircuit H i a).recoveredAllPorts_rotation
    (t.dualEuler)
    (reduced_minimal_odd_sigma_reachable t hmin hs) s b

theorem minimalSigmaRecoveredAllPorts_vertex_iff (i : WheelCycleIndex)
    (a : H.RimDart (numberedWheelCycles i)) (s : Bool)
    (b c : (smoothedSigmaRecoveredGraph t i a s).Dart) :
    b.vertex = c.vertex ↔ (minimalSigmaRecoveredAllPorts t hmin hs i a s b).vertex =
      (minimalSigmaRecoveredAllPorts t hmin hs i a s c).vertex :=
  (closedSigmaRimCircuit H i a).recoveredAllPorts_vertex_iff
    (t.dualEuler)
    (reduced_minimal_odd_sigma_reachable t hmin hs) s b c

include t hmin hs in
theorem minimalSigmaRecoveredGraph_sign (i : WheelCycleIndex)
    (a : H.RimDart (numberedWheelCycles i)) (s : Bool) :
    (smoothedSigmaRecoveredGraph t i a s).sign = 1 :=
  ((closedSigmaRimCircuit H i a).germReduction_sign_of_connected
    (t.dualEuler)
    (reduced_minimal_odd_sigma_reachable t hmin hs) s).trans
      (t.sign.trans (d.graph_sign.trans hs))

end ThomGame.Construction

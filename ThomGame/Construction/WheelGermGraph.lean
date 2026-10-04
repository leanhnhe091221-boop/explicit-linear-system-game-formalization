module

public import ThomGame.Construction.WheelRegionGraph
public import ThomGame.Pictures.CircuitGermGluing
public import ThomGame.Pictures.CycleGermCharge

/-!
# Actual numbered wheel germs and their rejoining

All central rims and pentagons in closed diagrams, including certified
smoothings, admit the actual germ and opposite-region composition.
The first-return theorem recovers original edge endpoints. Every stellar
rim in a component of sign one has a germ of sign zero. These are port
graphs; a diagram realization and an arbitrary-region replacement theorem
are not asserted here.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures
open scoped BigOperators

theorem numberedWheelCycle_stellar_of_ne_odd (i : WheelCycleIndex) (hi : i ≠ oddWheelCycle) :
    Nonempty ((numberedWheelCycles i).Stellar numberedSystem.rhs) := by
  rcases i with r | ⟨r, j⟩
  · exact ⟨numberedCentralWheelStellar r⟩
  · refine ⟨numberedPentagonWheelStellar r j ?_⟩
    intro h
    have he := congrArg (fun row : Row => (⟨row.1, row.2.1⟩ : (r : WheelIndex) × Fin (wheelFamily.size r))) h
    exact hi (congrArg Sum.inr he)

@[reducible] noncomputable def closedSigmaRimGermGraph (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) (s : Bool) :
    SigmaGraph [] ((closedSigmaRimCircuit d.graph i a).frontierWord (!s)) :=
  (closedSigmaRimCircuit d.graph i a).germGraph d.graph_dualEuler s

noncomputable def closedSigmaRimGermPorts (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) (s : Bool) :
    (closedSigmaRimGermGraph d i a s).Dart ≃ (closedSigmaRimCircuit d.graph i a).GermRaw s :=
  (closedSigmaRimCircuit d.graph i a).germPorts d.graph_dualEuler s

theorem closedSigmaRimGermGraph_twin (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) (s : Bool)
    (b : (closedSigmaRimGermGraph d i a s).Dart) :
    closedSigmaRimGermPorts d i a s ((closedSigmaRimGermGraph d i a s).pairing.twin b) =
      ((closedSigmaRimCircuit d.graph i a).germRawPairing s).twin (closedSigmaRimGermPorts d i a s b) :=
  (closedSigmaRimCircuit d.graph i a).germGraph_twin d.graph_dualEuler s b

theorem closedSigmaRimGermGraph_character (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) (s : Bool) (r : Fin 1417152) :
    (closedSigmaRimGermGraph d i a s).character r =
      (Nat.card {h : d.graph.Hub //
        (closedSigmaRimCircuit d.graph i a).GermVertex s (.inr (.inl h)) ∧
          d.graph.hubLabel h = r} : ZMod 2) :=
  (closedSigmaRimCircuit d.graph i a).germGraph_character d.graph_dualEuler s r

/-- A stellar rim in an odd component has a germ of sign zero. -/
theorem closedSigmaRimGermGraph_exists_sign_zero (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) (hi : i ≠ oddWheelCycle) :
    d.graph.OddRimComponentHasZeroSignGerm (numberedWheelCycles i) d.graph_dualEuler a :=
  (numberedWheelCycle_stellar_of_ne_odd i hi).elim fun hc =>
    PortGraph.stellar_oddRimComponentHasZeroSignGerm (A := numberedSystem) d.graph (numberedWheelCycles i)
      d.graph_dualEuler a hc

@[reducible] noncomputable def closedSigmaRimGluedGraph (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) (s : Bool) : SigmaGraph [] [] :=
  (closedSigmaRimGermGraph d i a s).comp (closedSigmaRimRegionGraph d i a (!s))

theorem closedSigmaRimGluedGraph_sign (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) (s : Bool) :
    (closedSigmaRimGluedGraph d i a s).sign =
      ∑ h : (closedSigmaRimCircuit d.graph i a).ComponentHub, numberedSystem.rhs (d.graph.hubLabel h.val) := by
  simpa only [SolutionGroup.triangularPresentation_parity] using
    (closedSigmaRimCircuit d.graph i a).gluedGraph_sign d.graph_dualEuler s

theorem closedSigmaRimGlued_firstReturn (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) (s : Bool)
    (b : (closedSigmaRimCircuit d.graph i a).GluingOriginal s) :
    let C := closedSigmaRimCircuit d.graph i a
    C.gluingRawVal s (C.gluedPorts d.graph_dualEuler s
      (MarkedReturn.perm (C.gluedStep d.graph_dualEuler s) (C.GluedRetained d.graph_dualEuler s)
        ⟨C.gluedOriginalPort d.graph_dualEuler s b, C.gluedOriginalPort_retained d.graph_dualEuler s b⟩).val) =
          d.graph.pairing.twin (C.gluingOriginalVal s b) :=
  (closedSigmaRimCircuit d.graph i a).glued_firstReturn_val d.graph_dualEuler s b

@[reducible] noncomputable def smoothedSigmaRimGermGraph {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (h : SigmaGraphWitness d H)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (s : Bool) :
    SigmaGraph [] ((closedSigmaRimCircuit H i a).frontierWord (!s)) :=
  (closedSigmaRimCircuit H i a).germGraph (h.dualEuler) s

/-- The same specialization for every certified smoothing. -/
theorem smoothedSigmaRimGermGraph_exists_sign_zero {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (h : SigmaGraphWitness d H)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (hi : i ≠ oddWheelCycle) :
    H.OddRimComponentHasZeroSignGerm (numberedWheelCycles i)
      (h.dualEuler) a :=
  (numberedWheelCycle_stellar_of_ne_odd i hi).elim fun hc =>
    PortGraph.stellar_oddRimComponentHasZeroSignGerm (A := numberedSystem) H (numberedWheelCycles i)
      (h.dualEuler) a hc

@[reducible] noncomputable def smoothedSigmaRimGluedGraph {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (h : SigmaGraphWitness d H)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (s : Bool) : SigmaGraph [] [] :=
  (smoothedSigmaRimGermGraph h i a s).comp (smoothedSigmaRimRegionGraph h i a (!s))

theorem smoothedSigmaRimGlued_firstReturn {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (h : SigmaGraphWitness d H)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (s : Bool)
    (b : (closedSigmaRimCircuit H i a).GluingOriginal s) :
    let C := closedSigmaRimCircuit H i a
    let he := h.dualEuler
    C.gluingRawVal s (C.gluedPorts he s
      (MarkedReturn.perm (C.gluedStep he s) (C.GluedRetained he s)
        ⟨C.gluedOriginalPort he s b, C.gluedOriginalPort_retained he s b⟩).val) =
          H.pairing.twin (C.gluingOriginalVal s b) :=
  (closedSigmaRimCircuit H i a).glued_firstReturn_val
    (h.dualEuler) s b

end ThomGame.Construction

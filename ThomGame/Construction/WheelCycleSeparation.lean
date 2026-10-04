module

public import ThomGame.Construction.WheelCycleRestriction
public import ThomGame.Pictures.DiagramCircuitSeparation

/-!
# Two cut components for the actual central rims and pentagons

Every lifted rim component in a closed numbered diagram is the simple
circuit already constructed from its two-regular restricted graph.
The zero Euler defect discharges the separation hypothesis. The same
statements apply after any certified smoothing trace.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures Pictures.RibbonConnectivity

theorem closedSigmaRimDiagram_cut_component_card (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) :
    Nat.card (Component d.graph.circuitStep (closedSigmaRimCircuit d.graph i a).cutPairing) =
      Nat.card (Component d.graph.circuitStep d.graph.pairing.perm) + 1 :=
  d.cut_component_card (closedSigmaRimCircuit d.graph i a)

theorem closedSigmaRimDiagram_cut_marked_connected_iff (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i))
    (x y : Fin (closedSigmaRimCircuit d.graph i a).length × Bool) :
    Connected d.graph.circuitStep (closedSigmaRimCircuit d.graph i a).cutPairing
      ((closedSigmaRimCircuit d.graph i a).port x) ((closedSigmaRimCircuit d.graph i a).port y) ↔
        x.2 = y.2 :=
  (closedSigmaRimCircuit d.graph i a).cut_marked_connected_iff d.graph_dualEuler x y

noncomputable def closedSigmaRimDiagram_sidesEquiv (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) :
    Bool ≃ {c : Component d.graph.circuitStep (closedSigmaRimCircuit d.graph i a).cutPairing //
      (closedSigmaRimCircuit d.graph i a).cutComponentToOld c =
        component d.graph.circuitStep d.graph.pairing.perm (closedSigmaRimCircuit d.graph i a).cutBase} :=
  (closedSigmaRimCircuit d.graph i a).cutSidesEquiv d.graph_dualEuler

theorem smoothed_closedSigmaRim_cut_component_card {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []} {circles : List (Fin 1889684)} (h : Smoothing d.graph H circles)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) :
    Nat.card (Component H.circuitStep (closedSigmaRimCircuit H i a).cutPairing) =
      Nat.card (Component H.circuitStep H.pairing.perm) + 1 :=
  h.diagram_cut_component_card (fun _ => by change 0 < 3; omega) (closedSigmaRimCircuit H i a)

theorem smoothed_closedSigmaRim_cut_marked_connected_iff {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []} {circles : List (Fin 1889684)} (h : Smoothing d.graph H circles)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i))
    (x y : Fin (closedSigmaRimCircuit H i a).length × Bool) :
    Connected H.circuitStep (closedSigmaRimCircuit H i a).cutPairing
      ((closedSigmaRimCircuit H i a).port x) ((closedSigmaRimCircuit H i a).port y) ↔ x.2 = y.2 :=
  (closedSigmaRimCircuit H i a).cut_marked_connected_iff
    (h.diagram_dualEuler (fun _ => by change 0 < 3; omega)) x y

noncomputable def smoothed_closedSigmaRim_sidesEquiv {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []} {circles : List (Fin 1889684)} (h : Smoothing d.graph H circles)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) :
    Bool ≃ {c : Component H.circuitStep (closedSigmaRimCircuit H i a).cutPairing //
      (closedSigmaRimCircuit H i a).cutComponentToOld c =
        component H.circuitStep H.pairing.perm (closedSigmaRimCircuit H i a).cutBase} :=
  (closedSigmaRimCircuit H i a).cutSidesEquiv (h.diagram_dualEuler (fun _ => by change 0 < 3; omega))

end ThomGame.Construction

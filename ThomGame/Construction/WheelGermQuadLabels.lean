module

public import ThomGame.Construction.WheelGermSunNormalization
public import ThomGame.Pictures.CycleGermQuadNeighbourhood

/-!
# Retraction and normalization fix original outer-quadrilateral labels

The actual germ's quadrilateral hubs lie on the chosen rim circuit, so
all three edge labels belong to its open sun neighbourhood. Retraction
is a left inverse there. The complete normalization therefore retains
the original Sigma labels, as well as the previously proved edge pairs.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures

variable {d : SigmaDiagram [] []} {H : SigmaGraph [] []} 
  (t : SigmaGraphWitness d H) (i : WheelCycleIndex)
  (a : H.RimDart (numberedWheelCycles i)) (side : Bool)

theorem smoothedSigmaRimGermQuad_labels_in_neighbourhood
    (p : (smoothedSigmaRimGermGraph t i a side).swapBoundary.BoundaryQuadPath)
    (x : (smoothedSigmaRimGermGraph t i a side).swapBoundary.Dart)
    (hx : x ∈ [p.firstDart, p.middleDart, p.lastDart]) :
    Port.label (smoothedSigmaRimGermGraph t i a side).swapBoundary.jointLabel x ∈
      Set.range (numberedWheelCycleRetraction i).inclusion.edge :=
  H.rimGermQuad_labels_in_open (numberedWheelCycles i) (numberedWheelCycleRetraction i).inclusion
    (numberedWheelCycle_vertices_in_retraction i) a
    (t.dualEuler) side p x hx

variable (m : GermSunRelabelling t i a side)
  {K : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0))
    [] (((closedSigmaRimCircuit H i a).frontierWord (!side)).map m.edge).reverse}
  (q : PortGraph.SunSwitchTrace (germSunInitialGraph t i a side m) K)
  (L : IncludedWheelSun i K ((closedSigmaRimCircuit H i a).frontierWord (!side)).reverse)
  (hp : ∀ x : (smoothedSigmaRimGermGraph t i a side).swapBoundary.Dart,
    (numberedWheelCycleRetraction i).retract.edge
      (Port.label (smoothedSigmaRimGermGraph t i a side).swapBoundary.jointLabel x) =
        some (m.edge (Port.label (smoothedSigmaRimGermGraph t i a side).swapBoundary.jointLabel x)))

include hp in
theorem germSunNormalizedQuad_labels
    (p : (smoothedSigmaRimGermGraph t i a side).swapBoundary.BoundaryQuadPath)
    (x : (smoothedSigmaRimGermGraph t i a side).swapBoundary.Dart)
    (hx : x ∈ [p.firstDart, p.middleDart, p.lastDart]) :
    Port.label L.graph.jointLabel (germSunNormalizedPorts t i a side m q L x) =
      Port.label (smoothedSigmaRimGermGraph t i a side).swapBoundary.jointLabel x := by
  rw [germSunNormalizedPorts_label]
  obtain ⟨z, hz⟩ := smoothedSigmaRimGermQuad_labels_in_neighbourhood t i a side p x hx
  have he := (numberedWheelCycleRetraction i).edge_leftInverse z
  rw [hz] at he
  have hm := Option.some.inj ((hp x).symm.trans he)
  rw [hm]
  exact hz

end ThomGame.Construction

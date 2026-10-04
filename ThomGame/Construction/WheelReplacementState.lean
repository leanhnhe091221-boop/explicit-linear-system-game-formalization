module

public import ThomGame.Construction.WheelMinimalGraphState
public import ThomGame.Construction.WheelDecreasingReplacement

/-!
# The actual decreasing replacement has a minimal odd graph state

The concrete replacement now accepts a size/sign/Euler diagram witness.
Every actual minimal odd state supplies that witness, so the complete
decreasing replacement returns another actual minimal odd state with
the same size and all other already facial indices preserved.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures

variable {d : SigmaDiagram [] []} {H : SigmaGraph [] []} {circles : List (Fin 1889684)}
    (t : Smoothing d.graph H circles) [IsEmpty H.Joint]
    (hmin : d.Minimal) (hs : d.sign = 1)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i))

include t hmin hs in
theorem smoothedSigmaRim_exists_decreasing_state (hi : i ≠ oddWheelCycle)
    (hn : ¬ ∃ side, (closedSigmaRimCircuit H i a).BoundsFaceOrbit side) :
    ∃ H' : SigmaGraph [] [], IsEmpty H'.Joint ∧ SigmaMinimalState H' ∧
      Fintype.card H'.Hub = Fintype.card H.Hub ∧
      sigmaNonfacialRimCount H' i < sigmaNonfacialRimCount H i ∧
      ∀ j : WheelCycleIndex, i ≠ j → SigmaRimsFacial H j → SigmaRimsFacial H' j := by
  obtain ⟨H', hJ, hsize, hsign, heuler, hlt, hfaces, f, _, hfsize, hfsign, hfmin⟩ :=
    smoothedSigmaRim_exists_decreasing_replacement t hmin hs i a hi hn
  have hstate : SigmaMinimalState H' :=
    PortGraph.ClosedMinimalOddState.of_witness heuler hsign f hfmin
      (hfsize.trans hsize.symm) hfsign
  exact ⟨H', hJ, hstate, hsize.trans (t.hub_card.trans d.graph_hub_card).symm, hlt, hfaces⟩

namespace SigmaMinimalState

variable {G : SigmaGraph [] []} (h : SigmaMinimalState G) [IsEmpty G.Joint]

include h in
theorem exists_decreasing_replacement (i : WheelCycleIndex)
    (a : G.RimDart (numberedWheelCycles i)) (hi : i ≠ oddWheelCycle)
    (hn : ¬ ∃ side, (closedSigmaRimCircuit G i a).BoundsFaceOrbit side) :
    ∃ K : SigmaGraph [] [], IsEmpty K.Joint ∧ SigmaMinimalState K ∧
      Fintype.card K.Hub = Fintype.card G.Hub ∧
      sigmaNonfacialRimCount K i < sigmaNonfacialRimCount G i ∧
      ∀ j : WheelCycleIndex, i ≠ j → SigmaRimsFacial G j → SigmaRimsFacial K j := by
  obtain ⟨d, hm, hs, t⟩ := h.exists_graph_witness
  obtain ⟨K, hJ, hsize, hsign, heuler, hlt, hfaces, f, _, hfsize, hfsign, hfmin⟩ :=
    smoothedSigmaRim_exists_decreasing_replacement t hm hs i a hi hn
  have hstate : SigmaMinimalState K :=
    PortGraph.ClosedMinimalOddState.of_witness heuler hsign f hfmin
      (hfsize.trans hsize.symm) hfsign
  exact ⟨K, hJ, hstate, hsize.trans t.size_eq.symm, hlt, hfaces⟩

end SigmaMinimalState
end ThomGame.Construction

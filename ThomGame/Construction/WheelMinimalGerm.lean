module

public import ThomGame.Construction.WheelGermGraph
public import ThomGame.Pictures.MinimalRimGerm

/-!
# Minimal odd numbered wheel diagrams have zero-sign stellar germs

The connected-component parity premise is discharged from diagram
minimality, including for arbitrary certified smoothings. This file gives
zero-sign port graphs; their actual diagram witnesses are constructed in
`WheelGermDiagrams`. Arbitrary-region replacement is a separate step.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures
open scoped BigOperators

theorem minimal_odd_sigma_hubs_reachable (d : SigmaDiagram [] [])
    (hmin : d.Minimal) (hs : d.sign = 1) (h k : d.graph.Hub) :
    d.graph.Reachable (.inr (.inl h)) (.inr (.inl k)) :=
  d.minimal_odd_hubs_reachable hmin hs h k

theorem J_sigma_eq_one_iff_closed_minimal_odd_hubs_connected :
    J_sigma = 1 ↔ ∃ d : SigmaDiagram [] [], d.sign = 1 ∧ d.Minimal ∧
      ∀ h k : d.graph.Hub, d.graph.Reachable (.inr (.inl h)) (.inr (.inl k)) := by
  constructor
  · intro hj
    obtain ⟨d, hs, hm⟩ := J_sigma_eq_one_iff_closed_minimal_odd_diagram.mp hj
    exact ⟨d, hs, hm, minimal_odd_sigma_hubs_reachable d hm hs⟩
  · rintro ⟨d, hs, hm, _⟩
    exact J_sigma_eq_one_iff_closed_minimal_odd_diagram.mpr ⟨d, hs, hm⟩

theorem closedSigmaRimGermGraph_minimal_exists_sign_zero (d : SigmaDiagram [] [])
    (hmin : d.Minimal) (hs : d.sign = 1) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) (hi : i ≠ oddWheelCycle) :
    d.graph.RimHasZeroSignGerm (numberedWheelCycles i) d.graph_dualEuler a := by
  obtain ⟨hc⟩ := numberedWheelCycle_stellar_of_ne_odd i hi
  exact d.minimal_odd_stellar_rim_hasZeroSignGerm hmin hs (numberedWheelCycles i) a hc

theorem smoothed_minimal_odd_sigma_hubs_reachable {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (t : SigmaGraphWitness d H)
    (hmin : d.Minimal) (hs : d.sign = 1) (h k : H.Hub) :
    H.Reachable (.inr (.inl h)) (.inr (.inl k)) :=
  t.minimal_odd_hubs_reachable hmin hs h k

theorem smoothedSigmaRimGermGraph_minimal_exists_sign_zero {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (t : SigmaGraphWitness d H)
    (hmin : d.Minimal) (hs : d.sign = 1) (i : WheelCycleIndex)
    (a : H.RimDart (numberedWheelCycles i)) (hi : i ≠ oddWheelCycle) :
    H.RimHasZeroSignGerm (numberedWheelCycles i)
      (t.dualEuler) a := by
  obtain ⟨hc⟩ := numberedWheelCycle_stellar_of_ne_odd i hi
  exact t.minimal_odd_stellar_rim_hasZeroSignGerm hmin hs (numberedWheelCycles i) a hc

end ThomGame.Construction

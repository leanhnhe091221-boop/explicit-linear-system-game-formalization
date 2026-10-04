module

public import ThomGame.Construction.WheelStellarCovers
public import ThomGame.Pictures.CoveredRimComponents

/-!
# The three covered edges of the exceptional numbered pentagon

The actual edge labels at positions 2, 3 and 4 belong to stellar cycles.
Their occurrences have distinct relation labels at both endpoints, and
all external ports on each connected restricted rim component face the
same side. These conclusions are derived on the actual stellar-normalized
Sigma graph, preparing the exceptional-cycle surgery in Theorem 11.4.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures

def oddWheelCoveredEdges : Set (Fin 1889684) :=
  {e | ∃ k : Fin (numberedWheelCycles oddWheelCycle).length,
    2 ≤ k.val ∧ (numberedWheelCycles oddWheelCycle).edge k = e}

theorem oddWheelCoveredEdges_subset :
    oddWheelCoveredEdges ⊆ Set.range (numberedWheelCycles oddWheelCycle).edge := by
  rintro e ⟨k, _, hk⟩
  exact ⟨k, hk⟩

theorem numbered_oddWheelCycle_covered (k : Fin (numberedWheelCycles oddWheelCycle).length)
    (hk : 2 ≤ k.val) :
    ∃ i : WheelCycleIndex, i ≠ oddWheelCycle ∧
      (numberedWheelCycles oddWheelCycle).edge k ∈ Set.range (numberedWheelCycles i).edge := by
  obtain ⟨i, hi, he⟩ := oddWheelCycle_covered k hk
  have hne : i ≠ oddWheelCycle := by
    intro h
    subst i
    exact oddPentagon_not_stellar hi
  refine ⟨i, hne, (numberedWheelCycles_edge_range i _).mpr ?_⟩
  have hc : colEquiv.symm ((numberedWheelCycles oddWheelCycle).edge k) =
      (wheelCycles oddWheelCycle).edge k := colEquiv.symm_apply_apply _
  rwa [hc]

theorem oddWheelCoveredEdges_stellar_covered :
    ∀ e ∈ oddWheelCoveredEdges, ∃ i : {i : WheelCycleIndex // i ≠ oddWheelCycle},
      e ∈ Set.range (numberedWheelCycles i.val).edge := by
  rintro e ⟨k, hk, rfl⟩
  obtain ⟨i, hi, he⟩ := numbered_oddWheelCycle_covered k hk
  exact ⟨⟨i, hi⟩, he⟩

variable {H : SigmaGraph [] []}
  (hf : ∀ i : WheelCycleIndex, i ≠ oddWheelCycle → SigmaRimsFacialCovers H i)

include hf in
theorem odd_covered_edge_distinct_labels (x : H.Dart)
    (hx : Port.label H.jointLabel x ∈ oddWheelCoveredEdges) : H.EdgeHasDistinctHubLabels x := by
  obtain ⟨i, hi⟩ := oddWheelCoveredEdges_stellar_covered _ hx
  exact PortGraph.rim_cover_edge (numberedWheelCycles i.val)
    (fun b => (hf i.val i.property b).2) x hi

variable [IsEmpty H.Joint] (a : H.RimDart (numberedWheelCycles oddWheelCycle))

include hf in
theorem odd_covered_component_common_side
    (v : {v : H.Vertex // (closedSigmaRimCircuit H oddWheelCycle a).OnCircuitVertex v}) :
    ∃ s, ∀ w : {v : H.Vertex // (closedSigmaRimCircuit H oddWheelCycle a).OnCircuitVertex v},
      (closedSigmaRimCircuit H oddWheelCycle a).RestrictedConnected oddWheelCoveredEdges v w →
      ∀ q : H.Dart, q.vertex = w.val → ¬ (closedSigmaRimCircuit H oddWheelCycle a).Marked q →
        (closedSigmaRimCircuit H oddWheelCycle a).Frontier s q :=
  H.covered_rim_component_common_side (numberedWheelCycles oddWheelCycle) a oddWheelCoveredEdges
    (fun i : {i : WheelCycleIndex // i ≠ oddWheelCycle} => numberedWheelCycles i.val)
    (fun i => numberedWheelCycles_intersection_unique oddWheelCycle i.val i.property.symm)
    oddWheelCoveredEdges_stellar_covered (fun i b => (hf i.val i.property b).1) v

include hf in
theorem odd_covered_component_onSide (h : SigmaMinimalState H)
    (v : {v : H.Vertex // (closedSigmaRimCircuit H oddWheelCycle a).OnCircuitVertex v}) :
    ∃ s, ∀ w : {v : H.Vertex // (closedSigmaRimCircuit H oddWheelCycle a).OnCircuitVertex v},
      (closedSigmaRimCircuit H oddWheelCycle a).RestrictedConnected oddWheelCoveredEdges v w →
      ∀ q : H.Dart, q.vertex = w.val → ¬ (closedSigmaRimCircuit H oddWheelCycle a).Marked q →
        (closedSigmaRimCircuit H oddWheelCycle a).OnSide s q := by
  obtain ⟨s, hs⟩ := odd_covered_component_common_side hf a v
  exact ⟨s, fun w hvw q hqv hq =>
    (((closedSigmaRimCircuit H oddWheelCycle a).frontier_iff h.dualEuler s q).mp (hs w hvw q hqv hq)).2.2⟩

end ThomGame.Construction

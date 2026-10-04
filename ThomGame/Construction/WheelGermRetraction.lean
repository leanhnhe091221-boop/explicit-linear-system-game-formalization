module

public import ThomGame.Construction.WheelMinimalRegionDiagrams
public import ThomGame.Construction.WheelDiagramRetractions
public import ThomGame.Pictures.CycleFrontierNeighbourhood

/-!
# Applying the actual stellar retraction to a minimal zero-sign germ

The original frontier lies in the open sun neighbourhood. Thus the
existing retraction fixes this boundary and produces a minimal zero-sign
diagram of exactly the same size, whose relation labels all lie in the
neighbourhood. This supplies the retraction stage of the stellar surgery;
sun normalization and preservation of outer quadrilaterals remain separate.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures

theorem numberedWheelCycle_vertices_in_retraction (i : WheelCycleIndex) :
    ∀ r ∈ Set.range (numberedWheelCycles i).vertex,
      r ∈ Set.range (numberedWheelCycleRetraction i).inclusion.vertex := by
  cases i with
  | inl r => rintro _ ⟨j, rfl⟩; exact ⟨j, rfl⟩
  | inr rj =>
    rcases rj with ⟨r, j⟩
    rintro _ ⟨k, rfl⟩
    exact ⟨k, rfl⟩

theorem closedSigmaRimFrontierWord_in_neighbourhood (G : SigmaGraph [] []) (i : WheelCycleIndex)
    (a : G.RimDart (numberedWheelCycles i)) (s : Bool) :
    ∀ z ∈ (closedSigmaRimCircuit G i a).frontierWord s,
      z ∈ Set.range (numberedWheelCycleRetraction i).inclusion.edge :=
  G.rimSimpleCircuit_frontierWord_in_open (numberedWheelCycles i)
    (numberedWheelCycleRetraction i).inclusion (numberedWheelCycle_vertices_in_retraction i) a s

theorem smoothedSigmaRimGerm_exists_retracted_minimal_diagram {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (t : SigmaGraphWitness d H)
    (hmin : d.Minimal) (hs : d.sign = 1)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (hi : i ≠ oddWheelCycle) :
    ∃ s, ∃ e : SigmaDiagram [] ((closedSigmaRimCircuit H i a).frontierWord (!s)),
      e.size = Fintype.card (smoothedSigmaRimGermGraph t i a s).Hub ∧
      e.sign = 0 ∧ e.Minimal ∧
      ∀ r ∈ e.labels, r ∈ Set.range (numberedWheelCycleRetraction i).inclusion.vertex := by
  obtain ⟨s, g, _, hsize, hzero, hminimal⟩ :=
    smoothedSigmaRimGerm_exists_minimal_zero_sign_diagram t hmin hs i a hi
  have hu : ∀ z ∈ ([] : List (Fin 1889684)),
      z ∈ Set.range (numberedWheelCycleRetraction i).inclusion.edge := by simp
  have hv := closedSigmaRimFrontierWord_in_neighbourhood H i a (!s)
  have hm := retractSigmaDiagram_minimal i hi g hu hv hzero hminimal
  refine ⟨s, retractSigmaDiagram i g hu hv, hm.1.trans hsize,
    retractSigmaDiagram_sign_zero i hi g hu hv, hm.2, ?_⟩
  intro r hr
  exact retractDiagram_labels_mem (numberedWheelCycleRetraction i) (fun _ => rfl)
    (fun _ => rfl) g hu hv hr

theorem closedSigmaRimGerm_exists_retracted_minimal_diagram (d : SigmaDiagram [] [])
    (hmin : d.Minimal) (hs : d.sign = 1)
    (i : WheelCycleIndex) (a : d.graph.RimDart (numberedWheelCycles i)) (hi : i ≠ oddWheelCycle) :
    ∃ s, ∃ e : SigmaDiagram [] ((closedSigmaRimCircuit d.graph i a).frontierWord (!s)),
      e.size = Fintype.card (closedSigmaRimGermGraph d i a s).Hub ∧
      e.sign = 0 ∧ e.Minimal ∧
      ∀ r ∈ e.labels, r ∈ Set.range (numberedWheelCycleRetraction i).inclusion.vertex :=
  smoothedSigmaRimGerm_exists_retracted_minimal_diagram (SigmaGraphWitness.ofDiagram d) hmin hs i a hi

end ThomGame.Construction

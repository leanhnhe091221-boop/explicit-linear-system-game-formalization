module

public import ThomGame.Construction.WheelGermRetraction
public import ThomGame.Pictures.RetractionSunDiagram

/-!
# Character-minimal sun witnesses for the actual stellar germs

The target is the genuine sun presentation. Its boundary maps letter for
letter to the original frontier, has the same length, and contains only
spokes. The witness keeps the germ's hub count and has exactly the
retracted relation multiset. These are the inputs to sun normalization;
facial covers and preservation of outer quadrilaterals are not asserted.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures
open scoped BigOperators

theorem numberedWheelCycleRetraction_rim_range (i : WheelCycleIndex) :
    Set.range (fun j : Fin (wheelCycles i).length =>
      (numberedWheelCycleRetraction i).inclusion.edge (.inr j)) =
        Set.range (numberedWheelCycles i).edge := by
  cases i with
  | inl r => rfl
  | inr rj => cases rj; rfl

theorem sigmaToCycleSun_minimal (i : WheelCycleIndex) (hi : i ≠ oddWheelCycle)
    {u v : List (Fin 1889684)} (d : SigmaDiagram u v)
    (hu : ∀ z ∈ u, z ∈ Set.range (numberedWheelCycleRetraction i).inclusion.edge)
    (hv : ∀ z ∈ v, z ∈ Set.range (numberedWheelCycleRetraction i).inclusion.edge)
    (hd : d.sign = 0) (hmin : d.Minimal) :
    ((sigmaToCycleSun i).diagram d).size = d.size ∧
      ((sigmaToCycleSun i).diagram d).Minimal ∧
      ((sigmaToCycleSun i).diagram d).CharacterMinimal :=
  retractionSunDiagram_minimal (numberedWheelCycleRetraction i) (fun _ => rfl) (fun _ => rfl)
    hu hv d (numberedWheelCycleRetraction_rhs_zero i hi) hd hmin

noncomputable def closedSigmaRimSunFrontierWord (G : SigmaGraph [] []) (i : WheelCycleIndex)
    (a : G.RimDart (numberedWheelCycles i)) (s : Bool) :
    List (Fin (wheelCycles i).length ⊕ Fin (wheelCycles i).length) :=
  ((closedSigmaRimCircuit G i a).frontierWord s).filterMap
    (numberedWheelCycleRetraction i).retract.edge

theorem closedSigmaRimSunFrontierWord_map (G : SigmaGraph [] []) (i : WheelCycleIndex)
    (a : G.RimDart (numberedWheelCycles i)) (s : Bool) :
    (closedSigmaRimSunFrontierWord G i a s).map
      (numberedWheelCycleRetraction i).inclusion.edge =
        (closedSigmaRimCircuit G i a).frontierWord s :=
  sunRetraction_boundary_map (numberedWheelCycleRetraction i)
    (closedSigmaRimFrontierWord_in_neighbourhood G i a s)

theorem closedSigmaRimSunFrontierWord_length (G : SigmaGraph [] []) (i : WheelCycleIndex)
    (a : G.RimDart (numberedWheelCycles i)) (s : Bool) :
    (closedSigmaRimSunFrontierWord G i a s).length =
      ((closedSigmaRimCircuit G i a).frontierWord s).length :=
  sunRetraction_boundary_length (numberedWheelCycleRetraction i)
    (closedSigmaRimFrontierWord_in_neighbourhood G i a s)

theorem closedSigmaRimSunFrontierWord_spokes (G : SigmaGraph [] []) (i : WheelCycleIndex)
    (a : G.RimDart (numberedWheelCycles i)) (s : Bool) :
    ∀ z ∈ closedSigmaRimSunFrontierWord G i a s, ∃ j, z = Sum.inl j := by
  apply sunRetraction_boundary_spokes (numberedWheelCycleRetraction i)
    (closedSigmaRimFrontierWord_in_neighbourhood G i a s)
  intro j hj
  apply closedSigmaRimFrontierWord_no_rim G i a s _ hj
  rw [← numberedWheelCycleRetraction_rim_range]
  exact ⟨j, rfl⟩

theorem smoothedSigmaRimGerm_exists_minimal_sun_diagram_with_sign {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (t : SigmaGraphWitness d H)
    (hmin : d.Minimal) (hs : d.sign = 1)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (hi : i ≠ oddWheelCycle) :
    ∃ s, ∃ e : Diagram (sunPresentation (wheelCycles i).length (fun _ => 0))
        [] (closedSigmaRimSunFrontierWord H i a (!s)),
      (e.labels : Multiset (Fin (wheelCycles i).length)) =
        (∑ h : (smoothedSigmaRimGermGraph t i a s).Hub,
          ([(smoothedSigmaRimGermGraph t i a s).hubLabel h] : Multiset (Fin 1417152))).filterMap
            (numberedWheelCycleRetraction i).retract.vertex ∧
      e.size = Fintype.card (smoothedSigmaRimGermGraph t i a s).Hub ∧
      e.sign = 0 ∧ e.Minimal ∧ e.CharacterMinimal ∧
      (smoothedSigmaRimGermGraph t i a s).sign = 0 := by
  obtain ⟨s, g, hlabels, hsize, hzero, hminimal⟩ :=
    smoothedSigmaRimGerm_exists_minimal_zero_sign_diagram t hmin hs i a hi
  have hu : ∀ z ∈ ([] : List (Fin 1889684)),
      z ∈ Set.range (numberedWheelCycleRetraction i).inclusion.edge := by simp
  have hv := closedSigmaRimFrontierWord_in_neighbourhood H i a (!s)
  have hm := sigmaToCycleSun_minimal i hi g hu hv hzero hminimal
  refine ⟨s, (sigmaToCycleSun i).diagram g, ?_, hm.1.trans hsize, ?_, hm.2.1, hm.2.2,
    ((smoothedSigmaRimGermGraph t i a s).diagram_sign_of_hub_labels hlabels).symm.trans hzero⟩
  · rw [← hlabels, Multiset.filterMap_coe]
    exact Multiset.coe_eq_coe.mpr ((sigmaToCycleSun i).labels_diagram_perm g)
  · exact (sigmaToCycleSun i).sign_diagram_zero g (fun _ _ _ => rfl)

theorem smoothedSigmaRimGerm_exists_minimal_sun_diagram {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (t : SigmaGraphWitness d H)
    (hmin : d.Minimal) (hs : d.sign = 1)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (hi : i ≠ oddWheelCycle) :
    ∃ s, ∃ e : Diagram (sunPresentation (wheelCycles i).length (fun _ => 0))
        [] (closedSigmaRimSunFrontierWord H i a (!s)),
      (e.labels : Multiset (Fin (wheelCycles i).length)) =
        (∑ h : (smoothedSigmaRimGermGraph t i a s).Hub,
          ([(smoothedSigmaRimGermGraph t i a s).hubLabel h] : Multiset (Fin 1417152))).filterMap
            (numberedWheelCycleRetraction i).retract.vertex ∧
      e.size = Fintype.card (smoothedSigmaRimGermGraph t i a s).Hub ∧
      e.sign = 0 ∧ e.Minimal ∧ e.CharacterMinimal := by
  obtain ⟨s, e, hl, hn, hz, hm, hc, _⟩ :=
    smoothedSigmaRimGerm_exists_minimal_sun_diagram_with_sign t hmin hs i a hi
  exact ⟨s, e, hl, hn, hz, hm, hc⟩

theorem closedSigmaRimGerm_exists_minimal_sun_diagram (d : SigmaDiagram [] [])
    (hmin : d.Minimal) (hs : d.sign = 1)
    (i : WheelCycleIndex) (a : d.graph.RimDart (numberedWheelCycles i)) (hi : i ≠ oddWheelCycle) :
    ∃ s, ∃ e : Diagram (sunPresentation (wheelCycles i).length (fun _ => 0))
        [] (closedSigmaRimSunFrontierWord d.graph i a (!s)),
      (e.labels : Multiset (Fin (wheelCycles i).length)) =
        (∑ h : (closedSigmaRimGermGraph d i a s).Hub,
          ([(closedSigmaRimGermGraph d i a s).hubLabel h] : Multiset (Fin 1417152))).filterMap
            (numberedWheelCycleRetraction i).retract.vertex ∧
      e.size = Fintype.card (closedSigmaRimGermGraph d i a s).Hub ∧
      e.sign = 0 ∧ e.Minimal ∧ e.CharacterMinimal :=
  smoothedSigmaRimGerm_exists_minimal_sun_diagram (SigmaGraphWitness.ofDiagram d) hmin hs i a hi

end ThomGame.Construction

module

public import ThomGame.Construction.WheelRegionDiagrams
public import ThomGame.Construction.WheelGermDiagrams
public import ThomGame.Pictures.MinimalRegionDiagrams

/-!
# Minimal region witnesses and minimal zero-sign germs for the actual wheel

Minimality of the closed odd input passes to both factors of its
region-germ decomposition. The stellar zero-sign germ can therefore be
chosen as a genuinely minimal diagram on the original frontier word.
Certified smoothings, including incomplete smoothings, are covered.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures
open scoped BigOperators

theorem smoothedSigmaRimRegion_exists_minimal_diagram {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (t : SigmaGraphWitness d H)
    (hmin : d.Minimal) (hs : d.sign = 1)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (s : Bool) :
    ∃ e : SigmaDiagram ((closedSigmaRimCircuit H i a).frontierWord s) [],
      (e.labels : Multiset (Fin 1417152)) =
        (∑ h : (smoothedSigmaRimRegionGraph t i a s).Hub,
          ([(smoothedSigmaRimRegionGraph t i a s).hubLabel h] : Multiset (Fin 1417152))) ∧
      e.size = Fintype.card (smoothedSigmaRimRegionGraph t i a s).Hub ∧
      e.sign = (smoothedSigmaRimRegionGraph t i a s).sign ∧ e.Minimal := by
  have hw := t.exists_minimal_circuit_diagrams hmin hs
    (closedSigmaRimCircuit H i a) (!s)
  cases s <;> simp only [Bool.not_false, Bool.not_true] at hw ⊢
  all_goals
    obtain ⟨_, e, _, hel, _, hes, _, he, _, hem⟩ := hw
    exact ⟨e, hel, hes, he, hem⟩

theorem closedSigmaRimRegion_exists_minimal_diagram (d : SigmaDiagram [] [])
    (hmin : d.Minimal) (hs : d.sign = 1)
    (i : WheelCycleIndex) (a : d.graph.RimDart (numberedWheelCycles i)) (s : Bool) :
    ∃ e : SigmaDiagram ((closedSigmaRimCircuit d.graph i a).frontierWord s) [],
      (e.labels : Multiset (Fin 1417152)) =
        (∑ h : (closedSigmaRimRegionGraph d i a s).Hub,
          ([(closedSigmaRimRegionGraph d i a s).hubLabel h] : Multiset (Fin 1417152))) ∧
      e.size = Fintype.card (closedSigmaRimRegionGraph d i a s).Hub ∧
      e.sign = (closedSigmaRimRegionGraph d i a s).sign ∧ e.Minimal :=
  smoothedSigmaRimRegion_exists_minimal_diagram (SigmaGraphWitness.ofDiagram d) hmin hs i a s

theorem smoothedSigmaRimGerm_exists_minimal_zero_sign_diagram {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (t : SigmaGraphWitness d H)
    (hmin : d.Minimal) (hs : d.sign = 1)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (hi : i ≠ oddWheelCycle) :
    ∃ s, ∃ e : SigmaDiagram [] ((closedSigmaRimCircuit H i a).frontierWord (!s)),
      (e.labels : Multiset (Fin 1417152)) =
        (∑ h : (smoothedSigmaRimGermGraph t i a s).Hub,
          ([(smoothedSigmaRimGermGraph t i a s).hubLabel h] : Multiset (Fin 1417152))) ∧
      e.size = Fintype.card (smoothedSigmaRimGermGraph t i a s).Hub ∧
      e.sign = 0 ∧ e.Minimal := by
  obtain ⟨s, hzero⟩ := smoothedSigmaRimGermGraph_minimal_exists_sign_zero t hmin hs i a hi
  obtain ⟨g, _, hgl, _, hgs, _, hg, _, hgm, _⟩ :=
    t.exists_minimal_circuit_diagrams hmin hs
      (closedSigmaRimCircuit H i a) s
  exact ⟨s, g, hgl, hgs, hg.trans hzero, hgm⟩

theorem closedSigmaRimGerm_exists_minimal_zero_sign_diagram (d : SigmaDiagram [] [])
    (hmin : d.Minimal) (hs : d.sign = 1)
    (i : WheelCycleIndex) (a : d.graph.RimDart (numberedWheelCycles i)) (hi : i ≠ oddWheelCycle) :
    ∃ s, ∃ e : SigmaDiagram [] ((closedSigmaRimCircuit d.graph i a).frontierWord (!s)),
      (e.labels : Multiset (Fin 1417152)) =
        (∑ h : (closedSigmaRimGermGraph d i a s).Hub,
          ([(closedSigmaRimGermGraph d i a s).hubLabel h] : Multiset (Fin 1417152))) ∧
      e.size = Fintype.card (closedSigmaRimGermGraph d i a s).Hub ∧
      e.sign = 0 ∧ e.Minimal :=
  smoothedSigmaRimGerm_exists_minimal_zero_sign_diagram (SigmaGraphWitness.ofDiagram d) hmin hs i a hi

end ThomGame.Construction

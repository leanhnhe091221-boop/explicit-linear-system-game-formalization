module

public import ThomGame.Construction.WheelMinimalGerm
public import ThomGame.Pictures.CircuitGermDiagram

/-!
# Actual numbered-wheel germ diagrams

Every closed wheel diagram and every certified smoothing has genuine
diagrams for both germs of each lifted rim. Boundary words, relation
multisets, sizes and signs are preserved. For a minimal odd input and a
stellar rim, one of these actual diagrams has sign zero.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures
open scoped BigOperators

theorem closedSigmaRimGerm_exists_diagram (d : SigmaDiagram [] []) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) (s : Bool) :
    ∃ e : SigmaDiagram [] ((closedSigmaRimCircuit d.graph i a).frontierWord (!s)),
      (e.labels : Multiset (Fin 1417152)) =
        (∑ h : (closedSigmaRimGermGraph d i a s).Hub,
          ([(closedSigmaRimGermGraph d i a s).hubLabel h] : Multiset (Fin 1417152))) ∧
      e.size = Fintype.card (closedSigmaRimGermGraph d i a s).Hub ∧
      e.sign = (closedSigmaRimGermGraph d i a s).sign :=
  (closedSigmaRimCircuit d.graph i a).exists_germ_diagram_preserving d.graph_dualEuler s
    (fun _ => by change 0 < 3; omega)

theorem smoothedSigmaRimGerm_exists_diagram {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (t : SigmaGraphWitness d H)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (s : Bool) :
    ∃ e : SigmaDiagram [] ((closedSigmaRimCircuit H i a).frontierWord (!s)),
      (e.labels : Multiset (Fin 1417152)) =
        (∑ h : (smoothedSigmaRimGermGraph t i a s).Hub,
          ([(smoothedSigmaRimGermGraph t i a s).hubLabel h] : Multiset (Fin 1417152))) ∧
      e.size = Fintype.card (smoothedSigmaRimGermGraph t i a s).Hub ∧
      e.sign = (smoothedSigmaRimGermGraph t i a s).sign :=
  (closedSigmaRimCircuit H i a).exists_germ_diagram_preserving
    (t.dualEuler) s (fun _ => by change 0 < 3; omega)

theorem closedSigmaRimGerm_minimal_exists_zero_sign_diagram (d : SigmaDiagram [] [])
    (hmin : d.Minimal) (hs : d.sign = 1) (i : WheelCycleIndex)
    (a : d.graph.RimDart (numberedWheelCycles i)) (hi : i ≠ oddWheelCycle) :
    ∃ s, ∃ e : SigmaDiagram [] ((closedSigmaRimCircuit d.graph i a).frontierWord (!s)),
      (e.labels : Multiset (Fin 1417152)) =
        (∑ h : (closedSigmaRimGermGraph d i a s).Hub,
          ([(closedSigmaRimGermGraph d i a s).hubLabel h] : Multiset (Fin 1417152))) ∧
      e.size = Fintype.card (closedSigmaRimGermGraph d i a s).Hub ∧ e.sign = 0 := by
  obtain ⟨s, hzero⟩ := closedSigmaRimGermGraph_minimal_exists_sign_zero d hmin hs i a hi
  obtain ⟨e, he, hsize, hsign⟩ := closedSigmaRimGerm_exists_diagram d i a s
  exact ⟨s, e, he, hsize, hsign.trans hzero⟩

theorem smoothedSigmaRimGerm_minimal_exists_zero_sign_diagram {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (t : SigmaGraphWitness d H)
    (hmin : d.Minimal) (hs : d.sign = 1) (i : WheelCycleIndex)
    (a : H.RimDart (numberedWheelCycles i)) (hi : i ≠ oddWheelCycle) :
    ∃ s, ∃ e : SigmaDiagram [] ((closedSigmaRimCircuit H i a).frontierWord (!s)),
      (e.labels : Multiset (Fin 1417152)) =
        (∑ h : (smoothedSigmaRimGermGraph t i a s).Hub,
          ([(smoothedSigmaRimGermGraph t i a s).hubLabel h] : Multiset (Fin 1417152))) ∧
      e.size = Fintype.card (smoothedSigmaRimGermGraph t i a s).Hub ∧ e.sign = 0 := by
  obtain ⟨s, hzero⟩ := smoothedSigmaRimGermGraph_minimal_exists_sign_zero t hmin hs i a hi
  obtain ⟨e, he, hsize, hsign⟩ := smoothedSigmaRimGerm_exists_diagram t i a s
  exact ⟨s, e, he, hsize, hsign.trans hzero⟩

end ThomGame.Construction

module

public import ThomGame.Construction.WheelOddPathMeasure

/-!
# When all covered paths are good, every remaining exceptional rim is independent

A rim containing any covered edge contains a whole lifted path, hence
its unique seed. A good seed makes that entire canonical rim a facial
cover. Consequently all other rims use only the two independent labels.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures PortGraph RibbonConnectivity
open scoped Classical

variable {H : SigmaGraph [] []} [IsEmpty H.Joint]
  (hf : ∀ i : WheelCycleIndex, i ≠ oddWheelCycle → SigmaRimsFacialCovers H i)
  (a : H.RimDart (numberedWheelCycles oddWheelCycle))

theorem oddPath_seed_on_rim_of_hub (h : H.LabelHub (oddCoveredRowPath.vertex 0)) (i : Fin 4)
    (hi : (closedSigmaRimCircuit H oddWheelCycle a).OnCircuitVertex
      (.inr (.inl (oddCoveredRowPath.hub H (oddCoveredRowPath_cover hf) h i)))) :
    (closedSigmaRimCircuit H oddWheelCycle a).OnCircuitVertex (.inr (.inl h.val)) := by
  induction i using Fin.induction with
  | zero => exact hi
  | succ i ih =>
    let x := oddCoveredRowPath.liftedExit H (oddCoveredRowPath_cover hf) h i
    have hl : Port.label H.jointLabel x ∈ Set.range (numberedWheelCycles oddWheelCycle).edge :=
      oddWheelCoveredEdges_subset (oddCoveredRowPath_edges ▸
        ⟨i, (oddCoveredRowPath.liftedExit_label H (oddCoveredRowPath_cover hf) h i).symm⟩)
    have hm : (closedSigmaRimCircuit H oddWheelCycle a).Marked (H.pairing.twin x) :=
      H.rimSimpleCircuit_marked_of_vertex_label (numberedWheelCycles oddWheelCycle) a
        ((oddCoveredRowPath.liftedExit_twin_vertex H (oddCoveredRowPath_cover hf) h i).symm ▸ hi)
        ((H.pairing.label_twin x).symm ▸ hl)
    exact ih ((oddCoveredRowPath.liftedExit_vertex H (oddCoveredRowPath_cover hf) h i) ▸
      (closedSigmaRimCircuit H oddWheelCycle a).marked_onCircuitVertex
        (((closedSigmaRimCircuit H oddWheelCycle a).marked_twin_iff x).mp hm))

include hf in
theorem oddPath_seed_on_rim_of_covered_port (x : H.Dart)
    (hx : (closedSigmaRimCircuit H oddWheelCycle a).Marked x)
    (hl : Port.label H.jointLabel x ∈ oddWheelCoveredEdges) :
    ∃ h : H.LabelHub (oddCoveredRowPath.vertex 0),
      (closedSigmaRimCircuit H oddWheelCycle a).OnCircuitVertex (.inr (.inl h.val)) := by
  obtain ⟨g, k, p, q, hp, _, _, _⟩ := odd_covered_edge_distinct_labels hf x hl
  obtain ⟨i, hi⟩ := (show Port.label H.jointLabel x ∈ Set.range oddCoveredRowPath.edge from
    oddCoveredRowPath_edges.symm ▸ hl)
  have he : numberedSystem.column (H.hubLabel g) p = oddCoveredRowPath.edge i :=
    (SolutionGroup.rowGraph_port_label numberedSystem H g p).symm.trans
      ((congrArg (Port.label H.jointLabel) hp).symm.trans hi.symm)
  have hinc := (numberedSystem.mem_hypergraph_incidence (H.hubLabel g) (oddCoveredRowPath.edge i)).mpr ⟨p, he⟩
  have hv : H.hubLabel g ∈ Set.range oddCoveredRowPath.vertex := by
    rcases (oddCoveredRowPath.incident (H.hubLabel g) i).mp hinc with hv | hv
    · exact ⟨i.castSucc, hv.symm⟩
    · exact ⟨i.succ, hv.symm⟩
  obtain ⟨⟨h, j⟩, hj⟩ := (oddCoveredRowPath.hubEquiv H (oddCoveredRowPath_cover hf)).surjective ⟨g, hv⟩
  have hgj : oddCoveredRowPath.hub H (oddCoveredRowPath_cover hf) h j = g := congrArg Subtype.val hj
  refine ⟨h, oddPath_seed_on_rim_of_hub hf a h j ?_⟩
  have hpv : x.vertex = .inr (.inl g) := congrArg Port.vertex hp
  have hg : (closedSigmaRimCircuit H oddWheelCycle a).OnCircuitVertex (.inr (.inl g)) :=
    hpv ▸ (closedSigmaRimCircuit H oddWheelCycle a).marked_onCircuitVertex hx
  exact hgj.symm ▸ hg

include hf in
theorem oddPath_good_of_covered_port
    (hEuler : eulerDefect H.pairing.perm H.circuitStep = 0)
    (hgood : ∀ h, OddPathGood H h) (x : H.Dart)
    (hx : (closedSigmaRimCircuit H oddWheelCycle a).Marked x)
    (hl : Port.label H.jointLabel x ∈ oddWheelCoveredEdges) :
    (∃ side, (closedSigmaRimCircuit H oddWheelCycle a).BoundsFaceOrbit side) ∧
      (closedSigmaRimCircuit H oddWheelCycle a).IsLabelCover := by
  obtain ⟨h, hh⟩ := oddPath_seed_on_rim_of_covered_port hf a x hx hl
  have hm : (closedSigmaRimCircuit H oddWheelCycle a).Marked (oddPathSeedPort H h) :=
    H.rimSimpleCircuit_marked_of_vertex_label (numberedWheelCycles oddWheelCycle) a hh
      ⟨1, (oddPathSeedPort_label H h).symm⟩
  exact (H.rimFacialCoverAt_iff_circuit
    (numberedWheelCycles oddWheelCycle).empty_boundary_no_rim
    (numberedWheelCycles oddWheelCycle).empty_boundary_no_rim (closedSigmaRimCircuit H oddWheelCycle a)
    (H.rimSimpleCircuit_rim (numberedWheelCycles oddWheelCycle)
      (numberedWheelCycles oddWheelCycle).empty_boundary_no_rim
      (numberedWheelCycles oddWheelCycle).empty_boundary_no_rim a)
    (H.dualEuler_eq_twice_components hEuler) hm).mp (hgood h)

def OddRimIndependentOnly (H : SigmaGraph [] [])
    (a : H.RimDart (numberedWheelCycles oddWheelCycle)) : Prop :=
  ∀ i : Fin (closedSigmaRimCircuit H oddWheelCycle a).length,
    ∃ k : Fin 5, k.val < 2 ∧
      (numberedWheelCycles oddWheelCycle).edge k =
        Port.label H.jointLabel ((closedSigmaRimCircuit H oddWheelCycle a).dart i)

include hf in
theorem oddRim_facial_cover_or_independent
    (hEuler : eulerDefect H.pairing.perm H.circuitStep = 0) (hgood : ∀ h, OddPathGood H h) :
    ((∃ side, (closedSigmaRimCircuit H oddWheelCycle a).BoundsFaceOrbit side) ∧
      (closedSigmaRimCircuit H oddWheelCycle a).IsLabelCover) ∨ OddRimIndependentOnly H a := by
  by_cases hc : ∃ i : Fin (closedSigmaRimCircuit H oddWheelCycle a).length,
      Port.label H.jointLabel ((closedSigmaRimCircuit H oddWheelCycle a).dart i) ∈ oddWheelCoveredEdges
  · obtain ⟨i, hi⟩ := hc
    exact Or.inl (oddPath_good_of_covered_port hf a hEuler hgood _ ⟨(i, false), rfl⟩ hi)
  · refine Or.inr fun i => ?_
    obtain ⟨k, hk⟩ := H.rimSimpleCircuit_rim (numberedWheelCycles oddWheelCycle)
      (numberedWheelCycles oddWheelCycle).empty_boundary_no_rim
      (numberedWheelCycles oddWheelCycle).empty_boundary_no_rim a i
    have hn : ¬ 2 ≤ k.val := fun he => hc ⟨i, k, he, hk⟩
    exact ⟨k, by omega, hk⟩

end ThomGame.Construction

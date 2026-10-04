module

public import ThomGame.Construction.WheelCopyObstruction
public import ThomGame.Pictures.CircuitCopyEulerSwitch
public import ThomGame.Pictures.RowEdgeSwitchFaces

/-!
# Lemma 11.9 for every constellation cycle with a private edge

An actual noncopy rim supplies two cuts over a private base label.
The switched graph is Euler-saturated, preserves every facial cover,
has the same full character and hub count, and has exactly one more
rim component. Maximality excludes that case. In particular all the
actual numbered pentagon rims, including the exceptional one, are copies.
-/

@[expose] public section
namespace ThomGame.Construction.SigmaMaximalRimState

open Pictures PortGraph RibbonConnectivity
open scoped Classical

variable {H : SigmaGraph [] []} [IsEmpty H.Joint] (h : SigmaMaximalRimState H)

include h in
theorem private_noncopy_surgery (j : WheelCycleIndex)
    (hp : Hypergraph.HasPrivateEdge numberedWheelCycles j)
    (a : H.RimDart (numberedWheelCycles j)) (hn : ¬ (closedSigmaRimCircuit H j a).IsLabelCopy) :
    ∃ s : H.RowEdgeSwitch,
      eulerDefect s.graph.pairing.perm s.graph.circuitStep = 0 ∧
      (∀ k : WheelCycleIndex, SigmaRimsFacialCovers s.graph k) ∧
      s.graph.totalRimCount numberedWheelCycles = H.totalRimCount numberedWheelCycles + 1 := by
  obtain ⟨e, ⟨l, hl⟩, he⟩ := hp
  obtain ⟨s, ⟨i, k, _, hi, hk⟩, hlabel, hEuler⟩ :=
    (closedSigmaRimCircuit H j a).exists_noncopy_euler_switch (numberedWheelCycles j)
      (H.rimSimpleCircuit_rim (numberedWheelCycles j) (by simp) (by simp) a)
      (h.covers j a).2 hn h.euler (h.covers j a).1 l
  have hprivate (m : WheelCycleIndex) (hm : m ≠ j) :
      Port.label H.jointLabel s.first ∉ Set.range (numberedWheelCycles m).edge :=
    fun hx => hm (he m ((hlabel.trans hl) ▸ hx))
  have ha : Port.label H.jointLabel s.first ∈ Set.range (numberedWheelCycles j).edge :=
    ⟨l, hlabel.symm⟩
  have hsame := s.rimWalk_sameCycle_of_canonical_cuts (numberedWheelCycles j) a hi hk ha
  refine ⟨s, hEuler, ?_, s.totalRimCount_split_private numberedWheelCycles j
    (s.rimCount_split_of_canonical_cuts (numberedWheelCycles j) a hi hk) hprivate⟩
  intro m b
  refine ⟨?_, s.rim_covers (numberedWheelCycles m) (fun z => (h.covers m z).2) b⟩
  apply s.rim_faces_of_refines (numberedWheelCycles m) ?_ (fun z => (h.covers m z).1) b
  intro x y hxy
  by_cases hm : m = j
  · subst m
    exact s.rimWalk_refines (numberedWheelCycles j) ha hsame hxy
  · rw [s.rimWalk_of_avoids (numberedWheelCycles m) (hprivate m hm)] at hxy
    exact hxy

include h in
theorem private_copies (j : WheelCycleIndex) (hp : Hypergraph.HasPrivateEdge numberedWheelCycles j) :
    SigmaRimsFacialCopies H j := by
  intro a
  refine ⟨(h.covers j a).1, ?_⟩
  by_contra hn
  obtain ⟨s, hEuler, hfaces, hcount⟩ := h.private_noncopy_surgery j hp a hn
  have hm := h.maximal s.graph inferInstance hEuler s.character s.hub_card hfaces
  omega

include h in
theorem pentagon_copies (r : WheelIndex) (j : Fin (wheelFamily.size r)) :
    SigmaRimsFacialCopies H (.inr ⟨r, j⟩) :=
  h.private_copies _ (numbered_pentagon_private_edge r j)

end ThomGame.Construction.SigmaMaximalRimState

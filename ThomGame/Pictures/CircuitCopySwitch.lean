module

public import ThomGame.Pictures.RowEdgeSwitch

/-!
# A noncopy facial cover supplies the actual edge-switch input

For any prescribed base edge, choose two distinct occurrences. Their
source hub labels and row slots agree by the proved global orientation.
They therefore define an actual same-row edge switch, with both cuts
on one original face on a common side of the two edges.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv
open scoped Classical

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  {G : SolutionGroup.RowGraph A [] []} [IsEmpty G.Joint]
  (C : G.SimpleCircuit) (γ : Hypergraph.Cycle A.hypergraph)
  (hl : ∀ i : Fin C.length, Port.label G.jointLabel (C.dart i) ∈ Set.range γ.edge)
  (hc : C.IsLabelCover)

include hl hc in
theorem exists_noncopy_switch (hn : ¬ C.IsLabelCopy) (j : Fin γ.length) :
    ∃ s : G.RowEdgeSwitch,
      (∃ i k : Fin C.length, i ≠ k ∧ s.first = C.dart i ∧ s.second = C.dart k) ∧
      Port.label G.jointLabel s.first = γ.edge j := by
  obtain ⟨i, k, hik, hi, hk, hedge⟩ := C.noncopy_repeats_every_edge γ hl hc hn j
  have hlabel := hi.trans hk.symm
  have hrow := C.cover_hub_labels_eq_of_edge_labels_eq γ hl hc hlabel
  obtain ⟨p, hp⟩ := C.port_eq_hubAt i false
  obtain ⟨q, hq⟩ := C.port_eq_hubAt k false
  change C.dart i = .hub (C.hubAt i) p at hp
  change C.dart k = .hub (C.hubAt k) q at hq
  have he : Port.label G.jointLabel (.hub (C.hubAt i) p : G.Dart) =
      Port.label G.jointLabel (.hub (C.hubAt k) q : G.Dart) :=
    (congrArg (Port.label G.jointLabel) hp).symm.trans
      (hlabel.trans (congrArg (Port.label G.jointLabel) hq))
  have hpq : p = q := A.column_injective (G.hubLabel (C.hubAt k))
    ((SolutionGroup.rowGraph_port_label A G _ p).symm.trans
      ((G.row_same_hubLabel_port_label hrow p).symm.trans
        (he.trans (SolutionGroup.rowGraph_port_label A G _ q))))
  subst q
  let s : G.RowEdgeSwitch := {
    left := C.hubAt i
    right := C.hubAt k
    slot := p
    same_row := hrow
    different_edges := fun he => hedge
      ((congrArg G.pairing.edge hp).trans (he.trans (congrArg G.pairing.edge hq).symm)) }
  exact ⟨s, ⟨i, k, hik, hp.symm, hq.symm⟩, (congrArg (Port.label G.jointLabel) hp).symm.trans hi⟩

include hl hc in
theorem exists_noncopy_facial_switch (hn : ¬ C.IsLabelCopy)
    (hf : ∃ side, C.BoundsFaceOrbit side) (j : Fin γ.length) :
    ∃ s : G.RowEdgeSwitch,
      C.Marked s.first ∧ C.Marked s.second ∧ Port.label G.jointLabel s.first = γ.edge j ∧
      (G.circuitStep.SameCycle s.first s.second ∨
        G.circuitStep.SameCycle (G.pairing.twin s.first) (G.pairing.twin s.second)) := by
  obtain ⟨s, ⟨i, k, _, hi, hk⟩, hlabel⟩ := C.exists_noncopy_switch γ hl hc hn j
  refine ⟨s, ⟨(i, false), hi.symm⟩, ⟨(k, false), hk.symm⟩, hlabel, ?_⟩
  obtain ⟨side, hside⟩ := hf
  cases side
  · exact Or.inl (((hside _).mpr ⟨i, hi.symm⟩).trans ((hside _).mpr ⟨k, hk.symm⟩).symm)
  · apply Or.inr
    have ht (l : Fin C.length) : C.port (finRotate C.length l, true) = G.pairing.twin (C.dart l) := by
      change G.pairing.twin (C.dart ((finRotate C.length).symm (finRotate C.length l))) = _
      rw [Equiv.symm_apply_apply]
    exact ((hside _).mpr ⟨finRotate C.length i, (ht i).trans (congrArg G.pairing.twin hi).symm⟩).trans
      ((hside _).mpr ⟨finRotate C.length k, (ht k).trans (congrArg G.pairing.twin hk).symm⟩).symm

end ThomGame.Pictures.PortGraph.SimpleCircuit

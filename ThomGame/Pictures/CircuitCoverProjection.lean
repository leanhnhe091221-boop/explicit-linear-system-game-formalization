module

public import ThomGame.Pictures.CircuitCoverEdges
public import ThomGame.Pictures.CycleIntersectionTurns
public import ThomGame.Pictures.CircuitHubPorts

/-!
# A genuine labelled circuit cover traverses the base cycle consistently

The actual edge and hub labels determine maps into the indexed base
cycle. Distinct hub labels across every edge prevent a reversal.
Consequently the edge-index map intertwines cyclic advancement with
one fixed orientation of the base cycle.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv
open scoped Classical

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  {G : SolutionGroup.RowGraph A [] []} [IsEmpty G.Joint]
  (C : G.SimpleCircuit) (γ : Hypergraph.Cycle A.hypergraph)
  (hl : ∀ i : Fin C.length, Port.label G.jointLabel (C.dart i) ∈ Set.range γ.edge)

noncomputable def coverEdgeIndex (i : Fin C.length) : Fin γ.length := (hl i).choose

omit [IsEmpty G.Joint] in
theorem coverEdgeIndex_label (i : Fin C.length) :
    γ.edge (C.coverEdgeIndex γ hl i) = Port.label G.jointLabel (C.dart i) := (hl i).choose_spec

include hl in
theorem cover_hub_label (i : Fin C.length) : G.hubLabel (C.hubAt i) ∈ Set.range γ.vertex := by
  obtain ⟨p, hp⟩ := C.port_eq_hubAt i false
  apply γ.closed (hl i)
  apply (A.mem_hypergraph_incidence _ _).mpr
  exact ⟨p, (SolutionGroup.rowGraph_port_label A G _ p).symm.trans
    (congrArg (Port.label G.jointLabel) hp).symm⟩

noncomputable def coverVertexIndex (i : Fin C.length) : Fin γ.length := (C.cover_hub_label γ hl i).choose

theorem coverVertexIndex_label (i : Fin C.length) :
    γ.vertex (C.coverVertexIndex γ hl i) = G.hubLabel (C.hubAt i) :=
  (C.cover_hub_label γ hl i).choose_spec

theorem coverEdgeIndex_source (i : Fin C.length) :
    C.coverEdgeIndex γ hl i = C.coverVertexIndex γ hl i ∨
      C.coverEdgeIndex γ hl i = finRotate γ.length (C.coverVertexIndex γ hl i) := by
  apply (γ.incident_index_iff _ _).mp
  rw [C.coverVertexIndex_label, C.coverEdgeIndex_label]
  obtain ⟨p, hp⟩ := C.port_eq_hubAt i false
  exact (A.mem_hypergraph_incidence _ _).mpr ⟨p,
    (SolutionGroup.rowGraph_port_label A G _ p).symm.trans
      (congrArg (Port.label G.jointLabel) hp).symm⟩

theorem coverEdgeIndex_target (i : Fin C.length) :
    C.coverEdgeIndex γ hl i = C.coverVertexIndex γ hl (finRotate C.length i) ∨
      C.coverEdgeIndex γ hl i = finRotate γ.length (C.coverVertexIndex γ hl (finRotate C.length i)) := by
  apply (γ.incident_index_iff _ _).mp
  rw [C.coverVertexIndex_label, C.coverEdgeIndex_label]
  obtain ⟨q, hq⟩ := C.port_eq_hubAt (finRotate C.length i) true
  change G.pairing.twin (C.dart ((finRotate C.length).symm (finRotate C.length i))) = _ at hq
  rw [Equiv.symm_apply_apply] at hq
  apply (A.mem_hypergraph_incidence _ _).mpr
  exact ⟨q, (SolutionGroup.rowGraph_port_label A G _ q).symm.trans
    ((congrArg (Port.label G.jointLabel) hq).symm.trans (G.pairing.label_twin _))⟩

theorem coverEdgeIndex_next_ne (i : Fin C.length) :
    C.coverEdgeIndex γ hl (finRotate C.length i) ≠ C.coverEdgeIndex γ hl i := by
  intro he
  have hlabels : Port.label G.jointLabel (C.dart (finRotate C.length i)) =
      Port.label G.jointLabel (G.pairing.twin (C.dart i)) :=
    (C.coverEdgeIndex_label γ hl _).symm.trans
      ((congrArg γ.edge he).trans ((C.coverEdgeIndex_label γ hl i).trans (G.pairing.label_twin _).symm))
  exact C.next_ne_twin i (G.row_label_injective_at_vertex (C.next_vertex i) hlabels)

variable (hc : C.IsLabelCover)

include hc in
theorem coverVertexIndex_next_ne (i : Fin C.length) :
    C.coverVertexIndex γ hl (finRotate C.length i) ≠ C.coverVertexIndex γ hl i := by
  intro he
  obtain ⟨h, k, p, q, hp, hq, _, hne⟩ := hc i
  have hh : C.hubAt i = h := Sum.inl.inj (Sum.inr.inj
    ((C.hubAt_vertex i).symm.trans (congrArg Port.vertex hp)))
  have hk : C.hubAt (finRotate C.length i) = k := Sum.inl.inj (Sum.inr.inj
    ((C.hubAt_vertex _).symm.trans ((C.next_vertex i).trans (congrArg Port.vertex hq))))
  apply hne
  exact (congrArg G.hubLabel hh).symm.trans
    ((C.coverVertexIndex_label γ hl i).symm.trans
      ((congrArg γ.vertex he.symm).trans
        ((C.coverVertexIndex_label γ hl _).trans (congrArg G.hubLabel hk))))

include hc in
theorem cover_step_forward (i : Fin C.length)
    (hf : C.coverEdgeIndex γ hl i = finRotate γ.length (C.coverVertexIndex γ hl i)) :
    C.coverVertexIndex γ hl (finRotate C.length i) = C.coverEdgeIndex γ hl i ∧
      C.coverEdgeIndex γ hl (finRotate C.length i) =
        finRotate γ.length (C.coverVertexIndex γ hl (finRotate C.length i)) := by
  have hv : C.coverVertexIndex γ hl (finRotate C.length i) = C.coverEdgeIndex γ hl i := by
    rcases C.coverEdgeIndex_target γ hl i with ht | ht
    · exact ht.symm
    · exact (C.coverVertexIndex_next_ne γ hl hc i ((finRotate γ.length).injective (ht.symm.trans hf))).elim
  refine ⟨hv, ?_⟩
  exact (C.coverEdgeIndex_source γ hl (finRotate C.length i)).resolve_left
    (fun he => C.coverEdgeIndex_next_ne γ hl i (he.trans hv))

include hc in
theorem cover_step_backward (i : Fin C.length)
    (hf : C.coverEdgeIndex γ hl i = C.coverVertexIndex γ hl i) :
    C.coverVertexIndex γ hl (finRotate C.length i) =
        (finRotate γ.length).symm (C.coverEdgeIndex γ hl i) ∧
      C.coverEdgeIndex γ hl (finRotate C.length i) = C.coverVertexIndex γ hl (finRotate C.length i) := by
  have hv : C.coverEdgeIndex γ hl i = finRotate γ.length (C.coverVertexIndex γ hl (finRotate C.length i)) := by
    rcases C.coverEdgeIndex_target γ hl i with ht | ht
    · exact (C.coverVertexIndex_next_ne γ hl hc i (ht.symm.trans hf)).elim
    · exact ht
  refine ⟨(congrArg (finRotate γ.length).symm hv).trans ((finRotate γ.length).symm_apply_apply _)
    |>.symm, ?_⟩
  exact (C.coverEdgeIndex_source γ hl (finRotate C.length i)).resolve_right
    (fun he => C.coverEdgeIndex_next_ne γ hl i (he.trans hv.symm))

include hc in
theorem cover_orientation :
    (∀ i, C.coverEdgeIndex γ hl i = finRotate γ.length (C.coverVertexIndex γ hl i)) ∨
      (∀ i, C.coverEdgeIndex γ hl i = C.coverVertexIndex γ hl i) := by
  have propagate (P : Fin C.length → Prop) (h0 : P 0) (hn : ∀ i, P i → P (finRotate C.length i)) :
      ∀ i, P i := by
    intro i
    obtain ⟨k, hk⟩ := (finRotate_sameCycle (0 : Fin C.length) i).exists_nat_pow_eq
    rw [← hk]
    clear hk
    induction k with
    | zero => exact h0
    | succ k ih =>
      rw [pow_succ', Perm.mul_apply]
      exact hn _ ih
  rcases C.coverEdgeIndex_source γ hl 0 with hb | hf
  · have hall := propagate (fun i => C.coverEdgeIndex γ hl i = C.coverVertexIndex γ hl i) hb
      (fun i hi => (C.cover_step_backward γ hl hc i hi).2)
    exact Or.inr hall
  · have hall := propagate
      (fun i => C.coverEdgeIndex γ hl i = finRotate γ.length (C.coverVertexIndex γ hl i)) hf
      (fun i hi => (C.cover_step_forward γ hl hc i hi).2)
    exact Or.inl hall

include hc in
theorem coverEdgeIndex_semiconj :
    Function.Semiconj (C.coverEdgeIndex γ hl) (finRotate C.length) (finRotate γ.length) ∨
      Function.Semiconj (C.coverEdgeIndex γ hl) (finRotate C.length) (finRotate γ.length).symm := by
  rcases C.cover_orientation γ hl hc with hf | hb
  · exact Or.inl fun i => (C.cover_step_forward γ hl hc i (hf i)).2.trans
      (congrArg (finRotate γ.length) (C.cover_step_forward γ hl hc i (hf i)).1)
  · exact Or.inr fun i => (C.cover_step_backward γ hl hc i (hb i)).2.trans
      (C.cover_step_backward γ hl hc i (hb i)).1

include hc in
theorem coverVertexIndex_eq_of_edgeIndex_eq {i j : Fin C.length}
    (he : C.coverEdgeIndex γ hl i = C.coverEdgeIndex γ hl j) :
    C.coverVertexIndex γ hl i = C.coverVertexIndex γ hl j := by
  rcases C.cover_orientation γ hl hc with hf | hb
  · exact (finRotate γ.length).injective ((hf i).symm.trans (he.trans (hf j)))
  · exact (hb i).symm.trans (he.trans (hb j))

include hl hc in
theorem cover_hub_labels_eq_of_edge_labels_eq {i j : Fin C.length}
    (he : Port.label G.jointLabel (C.dart i) = Port.label G.jointLabel (C.dart j)) :
    G.hubLabel (C.hubAt i) = G.hubLabel (C.hubAt j) := by
  have he' := γ.edge.injective ((C.coverEdgeIndex_label γ hl i).trans
    (he.trans (C.coverEdgeIndex_label γ hl j).symm))
  exact (C.coverVertexIndex_label γ hl i).symm.trans
    ((congrArg γ.vertex (C.coverVertexIndex_eq_of_edgeIndex_eq γ hl hc he')).trans
      (C.coverVertexIndex_label γ hl j))

end ThomGame.Pictures.PortGraph.SimpleCircuit

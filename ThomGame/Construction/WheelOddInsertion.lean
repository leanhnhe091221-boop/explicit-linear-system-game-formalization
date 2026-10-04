module

public import ThomGame.Construction.WheelOddPathCopies
public import ThomGame.Pictures.RowPairInsertionRims

/-!
# The actual exceptional pentagon's two-edge insertion

The covered path ends at vertices 4 and 1. Its two adjacent independent
edges are slots 1 and 2 of the actual odd row, while slot 0 is an ordinary
generator, absent from every wheel rim. All three labels are proved to
be absent from other constellation cycles. The input ports for insertion
are chosen on the actual lifted path, not on an abstract copy.
-/

@[expose] public section
namespace ThomGame.Wheel.Family

variable {R V : Type*} (F : Family R V)

theorem b_mem_pentagon (r s : R) (j : Fin (F.size r)) (i : Fin (F.size s)) :
    F.aux r j 1 ∈ F.pentagonEdges s i ↔
      (⟨s, i⟩ : (t : R) × Fin (F.size t)) = ⟨r, j⟩ := by
  classical
  by_cases hsr : s = r
  · subst s
    simp [F.pentagon_mem_iff, aux, eq_comm]
  · have hrs := Ne.symm hsr
    simp [F.pentagon_mem_iff, aux, hrs, hsr]

theorem ordinary_not_central (x : V) (r : R) : Sum.inl x ∉ F.centralEdges r := by
  rintro ⟨j, hj⟩
  cases hj

theorem ordinary_not_pentagon (x : V) (r : R) (j : Fin (F.size r)) :
    Sum.inl x ∉ F.pentagonEdges r j := by
  simp [F.pentagon_mem_iff, aux]

theorem pentagon_base_column_one (r : R) (j : Fin (F.size r)) :
    F.system.column ⟨r, j, 0⟩ 1 = F.pentagonRim r j 0 := rfl

theorem pentagon_base_column_two (r : R) (j : Fin (F.size r)) :
    F.system.column ⟨r, j, 0⟩ 2 = F.pentagonRim r j 1 := rfl

theorem pentagon_base_column_zero (r : R) (j : Fin (F.size r)) :
    F.system.column ⟨r, j, 0⟩ 0 = .inl (F.letter r j) := rfl

end ThomGame.Wheel.Family

namespace ThomGame.Pictures.PortGraph.RowPath

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  (C : Hypergraph.Cycle A.hypergraph) (start n : Nat) (hn : start + n < C.length)

theorem segment_first_incident :
    C.edge (cycleVertexIndex C start n hn 0) ∈
      A.hypergraph.incidence ((ofCycleSegment C start n hn).vertex 0) :=
  (C.incident_iff _ _).mpr (Or.inl rfl)

theorem segment_after_last_incident :
    C.edge (finRotate C.length (cycleVertexIndex C start n hn (Fin.last n))) ∈
      A.hypergraph.incidence ((ofCycleSegment C start n hn).vertex (Fin.last n)) :=
  (C.incident_iff _ _).mpr (Or.inr (congrArg C.vertex
    ((finRotate C.length).symm_apply_apply _).symm))

end ThomGame.Pictures.PortGraph.RowPath

namespace ThomGame.Construction

open Pictures PortGraph
open scoped Classical

theorem numbered_column_eq (r : Row) (k : Fin 3) :
    numberedSystem.column (rowEquiv r) k = colEquiv (system.column r k) :=
  system.reindex_column rowEquiv colEquiv r k

theorem numbered_pentagon_edge (r : WheelIndex) (j : Fin (wheelFamily.size r)) (k : Fin 5) :
    (numberedWheelCycles (.inr ⟨r, j⟩)).edge k =
      colEquiv ((wheelCycles (.inr ⟨r, j⟩)).edge k) := rfl

theorem ordinary_not_wheelCycle (x : Ordinary) (i : WheelCycleIndex) :
    Sum.inl x ∉ Set.range (wheelCycles i).edge := by
  rcases i with r | ⟨r, j⟩
  · exact wheelFamily.ordinary_not_central x r
  · exact wheelFamily.ordinary_not_pentagon x r j

theorem pentagon_first_edge_private (r : WheelIndex) (j : Fin (wheelFamily.size r))
    (i : WheelCycleIndex) (hi : i ≠ .inr ⟨r, j⟩) :
    wheelFamily.aux r j 0 ∉ Set.range (wheelCycles i).edge := by
  rcases i with t | ⟨t, k⟩
  · intro he
    exact (by decide +kernel : (0 : Fin 4) ≠ 3)
      ((wheelFamily.aux_mem_central r t j 0).mp he).2
  · intro he
    exact hi (congrArg Sum.inr ((wheelFamily.a_mem_pentagon r t j k).mp he))

theorem pentagon_second_edge_private (r : WheelIndex) (j : Fin (wheelFamily.size r))
    (i : WheelCycleIndex) (hi : i ≠ .inr ⟨r, j⟩) :
    wheelFamily.aux r j 1 ∉ Set.range (wheelCycles i).edge := by
  rcases i with t | ⟨t, k⟩
  · intro he
    exact (by decide +kernel : (1 : Fin 4) ≠ 3)
      ((wheelFamily.aux_mem_central r t j 1).mp he).2
  · intro he
    exact hi (congrArg Sum.inr ((wheelFamily.b_mem_pentagon r t j k).mp he))

theorem odd_row_column_one :
    numberedSystem.column (rowEquiv oddRow) 1 = (numberedWheelCycles oddWheelCycle).edge 0 := by
  exact (numbered_column_eq oddRow 1).trans
    ((congrArg colEquiv (wheelFamily.pentagon_base_column_one none 0)).trans
      (numbered_pentagon_edge none 0 0).symm)

theorem odd_row_column_two :
    numberedSystem.column (rowEquiv oddRow) 2 = (numberedWheelCycles oddWheelCycle).edge 1 := by
  exact (numbered_column_eq oddRow 2).trans
    ((congrArg colEquiv (wheelFamily.pentagon_base_column_two none 0)).trans
      (numbered_pentagon_edge none 0 1).symm)

theorem odd_row_column_zero :
    numberedSystem.column (rowEquiv oddRow) 0 = colEquiv (.inl (wheelFamily.letter none 0)) :=
  (numbered_column_eq oddRow 0).trans (congrArg colEquiv (wheelFamily.pentagon_base_column_zero none 0))

theorem odd_row_spoke_not_cycle (i : WheelCycleIndex) :
    numberedSystem.column (rowEquiv oddRow) 0 ∉ Set.range (numberedWheelCycles i).edge := by
  rw [odd_row_column_zero, numberedWheelCycles_edge_range, colEquiv.symm_apply_apply]
  exact ordinary_not_wheelCycle _ i

theorem odd_row_columns_not_other_cycle (i : WheelCycleIndex) (hi : i ≠ oddWheelCycle)
    (k : Fin 3) : numberedSystem.column (rowEquiv oddRow) k ∉ Set.range (numberedWheelCycles i).edge := by
  have he : numberedSystem.column (rowEquiv oddRow) k = colEquiv (system.column oddRow k) :=
    numbered_column_eq oddRow k
  rw [he, numberedWheelCycles_edge_range, colEquiv.symm_apply_apply]
  fin_cases k
  · exact ordinary_not_wheelCycle _ i
  · exact pentagon_first_edge_private none 0 i hi
  · exact pentagon_second_edge_private none 0 i hi

theorem oddPath_first_cut_incident :
    numberedSystem.column (rowEquiv oddRow) 1 ∈
      numberedSystem.hypergraph.incidence (oddCoveredRowPath.vertex 3) := by
  have ht := RowPath.segment_after_last_incident (numberedWheelCycles oddWheelCycle) 1 3
    (by decide +kernel : 1 + 3 < (numberedWheelCycles oddWheelCycle).length)
  have he : finRotate (numberedWheelCycles oddWheelCycle).length
      (RowPath.cycleVertexIndex (numberedWheelCycles oddWheelCycle) 1 3 (by decide +kernel) (Fin.last 3)) = 0 := by
    change finRotate 5 (4 : Fin 5) = 0
    decide +kernel
  rw [he] at ht
  exact odd_row_column_one.symm ▸ ht

theorem oddPath_second_cut_incident :
    numberedSystem.column (rowEquiv oddRow) 2 ∈
      numberedSystem.hypergraph.incidence (oddCoveredRowPath.vertex 0) := by
  have ht := RowPath.segment_first_incident (numberedWheelCycles oddWheelCycle) 1 3
    (by decide +kernel : 1 + 3 < (numberedWheelCycles oddWheelCycle).length)
  exact odd_row_column_two.symm ▸ ht

variable {H : SigmaGraph [] []} [IsEmpty H.Joint]
  (hf : ∀ i : WheelCycleIndex, i ≠ oddWheelCycle → SigmaRimsFacialCovers H i)
  (h : H.LabelHub (oddCoveredRowPath.vertex 0))

noncomputable def oddPathInsertion : H.RowPairInsertion where
  row := rowEquiv oddRow
  first := H.rowLabelPort (oddCoveredRowPath.vertex 3)
    (numberedSystem.column (rowEquiv oddRow) 1) oddPath_first_cut_incident
    ⟨oddCoveredRowPath.hub H (oddCoveredRowPath_cover hf) h 3,
      oddCoveredRowPath.hub_label H (oddCoveredRowPath_cover hf) h 3⟩
  second := H.rowLabelPort (oddCoveredRowPath.vertex 0)
    (numberedSystem.column (rowEquiv oddRow) 2) oddPath_second_cut_incident h
  first_label := H.rowLabelPort_label _ _ _ _
  second_label := H.rowLabelPort_label _ _ _ _

theorem oddPathInsertion_first_vertex :
    (oddPathInsertion hf h).first.vertex =
      .inr (.inl (oddCoveredRowPath.hub H (oddCoveredRowPath_cover hf) h 3)) := rfl

theorem oddPathInsertion_second_vertex :
    (oddPathInsertion hf h).second.vertex = .inr (.inl h.val) := rfl

noncomputable def oddPathInsertedGraph (orientation : Bool) : SigmaGraph [] [] :=
  (oddPathInsertion hf h).graph orientation

instance oddPathInsertedGraph_joint_isEmpty (orientation : Bool) :
    IsEmpty (oddPathInsertedGraph hf h orientation).Joint := inferInstanceAs (IsEmpty H.Joint)

theorem oddPathInsertedGraph_hub_card (orientation : Bool) :
    Fintype.card (oddPathInsertedGraph hf h orientation).Hub = Fintype.card H.Hub + 2 :=
  (oddPathInsertion hf h).graph_hub_card orientation

theorem oddPathInsertedGraph_character (orientation : Bool) (r : Fin 1417152) :
    (oddPathInsertedGraph hf h orientation).character r = H.character r :=
  (oddPathInsertion hf h).graph_character orientation r

theorem oddPathInsertedGraph_sign (orientation : Bool) :
    (oddPathInsertedGraph hf h orientation).sign = H.sign :=
  (oddPathInsertion hf h).graph_sign orientation

theorem oddPathInsertedGraph_spoke (orientation b : Bool) :
    (oddPathInsertedGraph hf h orientation).pairing.twin ((oddPathInsertion hf h).fresh b 0) =
      (oddPathInsertion hf h).fresh (!b) 0 := (oddPathInsertion hf h).twin_spoke b

theorem oddPathInsertion_other_rim_avoids (i : WheelCycleIndex) (hi : i ≠ oddWheelCycle)
    (a : H.RimDart (numberedWheelCycles i)) (j : Fin (closedSigmaRimCircuit H i a).length) :
    Port.label H.jointLabel ((closedSigmaRimCircuit H i a).dart j) ≠
        numberedSystem.column (oddPathInsertion hf h).row 1 ∧
      Port.label H.jointLabel ((closedSigmaRimCircuit H i a).dart j) ≠
        numberedSystem.column (oddPathInsertion hf h).row 2 := by
  have hm := H.rimSimpleCircuit_rim (numberedWheelCycles i)
    (numberedWheelCycles i).empty_boundary_no_rim (numberedWheelCycles i).empty_boundary_no_rim a j
  exact ⟨fun he => odd_row_columns_not_other_cycle i hi 1 (he ▸ hm),
    fun he => odd_row_columns_not_other_cycle i hi 2 (he ▸ hm)⟩

/-- Every old rim of another constellation cycle retains its face and cover.
This statement transports the actual circuit; classification of all new
rims is a separate assertion. -/
theorem oddPathInsertion_preserves_other_face (orientation : Bool)
    (i : WheelCycleIndex) (hi : i ≠ oddWheelCycle) (a : H.RimDart (numberedWheelCycles i)) :
    let C := (oddPathInsertion hf h).oldCircuit orientation (closedSigmaRimCircuit H i a)
      (oddPathInsertion_other_rim_avoids hf h i hi a)
    (∃ side, C.BoundsFaceOrbit side) ∧ C.IsLabelCover := by
  obtain ⟨⟨side, hs⟩, hc⟩ := hf i hi a
  exact ⟨⟨side, (oddPathInsertion hf h).oldCircuit_face orientation _ _ side hs⟩,
    (oddPathInsertion hf h).oldCircuit_cover orientation _ _ hc⟩

/-- The complete family is preserved: every target rim of a stellar
index comes from a unique old rim dart via the actual port equivalence. -/
theorem oddPathInsertedGraph_stellar_facial_covers (orientation : Bool)
    (i : WheelCycleIndex) (hi : i ≠ oddWheelCycle) :
    SigmaRimsFacialCovers (oddPathInsertedGraph hf h orientation) i :=
  (oddPathInsertion hf h).all_rims_facial_covers orientation (numberedWheelCycles i)
    (odd_row_columns_not_other_cycle i hi) (hf i hi)

end ThomGame.Construction

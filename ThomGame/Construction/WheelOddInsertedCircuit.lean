module

public import ThomGame.Construction.WheelOddInsertionEuler
public import ThomGame.Pictures.CircuitFaceSteps

/-!
# The new simple pentagon in the actual exceptional insertion

The circuit consists of the new row vertex, the four original lifted
path vertices, and their actual paired ports. Its vertices and edge
labels enumerate the exceptional pentagon exactly once.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures PortGraph
open scoped Classical

variable {H : SigmaGraph [] []} [IsEmpty H.Joint]
  (hf : ∀ i : WheelCycleIndex, i ≠ oddWheelCycle → SigmaRimsFacialCovers H i)
  (h : H.LabelHub (oddCoveredRowPath.vertex 0))

noncomputable def oddInsertedOldDart : Fin 4 → H.Dart :=
  Fin.lastCases (oddPathInsertion hf h).first
    (oddCoveredRowPath.liftedExit H (oddCoveredRowPath_cover hf) h)

theorem oddInsertedOldDart_castSucc (i : Fin 3) :
    oddInsertedOldDart hf h i.castSucc =
      oddCoveredRowPath.liftedExit H (oddCoveredRowPath_cover hf) h i :=
  Fin.lastCases_castSucc i

theorem oddInsertedOldDart_last :
    oddInsertedOldDart hf h (Fin.last 3) = (oddPathInsertion hf h).first :=
  Fin.lastCases_last

theorem oddInsertedOldDart_vertex (i : Fin 4) :
    (oddInsertedOldDart hf h i).vertex =
      .inr (.inl (oddCoveredRowPath.hub H (oddCoveredRowPath_cover hf) h i)) := by
  cases i using Fin.lastCases with
  | last =>
    exact (congrArg Port.vertex (oddInsertedOldDart_last hf h)).trans
      (oddPathInsertion_first_vertex hf h)
  | cast i =>
    exact (congrArg Port.vertex (oddInsertedOldDart_castSucc hf h i)).trans
      (oddCoveredRowPath.liftedExit_vertex H (oddCoveredRowPath_cover hf) h i)

theorem oddInsertedOldDart_label (i : Fin 4) :
    Port.label H.jointLabel (oddInsertedOldDart hf h i) =
      (numberedWheelCycles oddWheelCycle).edge (finRotate 5 i.succ) := by
  cases i using Fin.lastCases with
  | last =>
    exact (congrArg (Port.label H.jointLabel) (oddInsertedOldDart_last hf h)).trans
      ((oddPathInsertion hf h).first_label.trans odd_row_column_one)
  | cast i =>
    rw [oddInsertedOldDart_castSucc]
    exact (oddCoveredRowPath.liftedExit_label H (oddCoveredRowPath_cover hf) h i).trans
      (congrArg (numberedWheelCycles oddWheelCycle).edge (by
        apply Fin.ext
        change 1 + i.val + 1 = (finRotate 5 i.castSucc.succ).val
        fin_cases i <;> rfl))

noncomputable def oddInsertedHub : Fin 5 → H.Hub ⊕ Bool :=
  Fin.cases (.inr false) (fun i => .inl (oddCoveredRowPath.hub H (oddCoveredRowPath_cover hf) h i))

noncomputable def oddInsertedDart : Fin 5 → (oddPathInsertion hf h).Dart :=
  Fin.cases ((oddPathInsertion hf h).fresh false 2)
    (fun i => (oddPathInsertion hf h).old (oddInsertedOldDart hf h i))

theorem oddInsertedHub_label (i : Fin 5) :
    (oddPathInsertion hf h).hubLabel (oddInsertedHub hf h i) =
      (numberedWheelCycles oddWheelCycle).vertex i := by
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    change H.hubLabel (oddCoveredRowPath.hub H (oddCoveredRowPath_cover hf) h i) = _
    apply (oddCoveredRowPath.hub_label H (oddCoveredRowPath_cover hf) h i).trans
    apply congrArg (numberedWheelCycles oddWheelCycle).vertex
    apply Fin.ext
    change 1 + i.val = i.val + 1
    omega

theorem oddInsertedHub_injective : Function.Injective (oddInsertedHub hf h) := by
  intro i j he
  apply (numberedWheelCycles oddWheelCycle).vertex.injective
  exact (oddInsertedHub_label hf h i).symm.trans
    ((congrArg (oddPathInsertion hf h).hubLabel he).trans (oddInsertedHub_label hf h j))

theorem oddInsertedDart_vertex (i : Fin 5) :
    (oddInsertedDart hf h i).vertex = .inr (.inl (oddInsertedHub hf h i)) := by
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    change ((oddPathInsertion hf h).old (oddInsertedOldDart hf h i)).vertex =
      .inr (.inl (.inl (oddCoveredRowPath.hub H (oddCoveredRowPath_cover hf) h i)))
    have hv := oddInsertedOldDart_vertex hf h i
    generalize oddInsertedOldDart hf h i = x at hv ⊢
    cases x <;> simp_all [RowPairInsertion.old, Port.vertex]

theorem oddInsertedDart_label (i : Fin 5) :
    Port.label H.jointLabel (oddInsertedDart hf h i) =
      (numberedWheelCycles oddWheelCycle).edge (finRotate 5 i) := by
  cases i using Fin.cases with
  | zero => exact ((oddPathInsertion hf h).fresh_label false 2).trans odd_row_column_two
  | succ i => exact ((oddPathInsertion hf h).old_label _).trans (oddInsertedOldDart_label hf h i)

theorem oddInsertedDart_vertex_injective :
    Function.Injective (fun i => (oddInsertedDart hf h i).vertex) := by
  intro i j he
  change (oddInsertedDart hf h i).vertex = (oddInsertedDart hf h j).vertex at he
  rw [oddInsertedDart_vertex hf h i, oddInsertedDart_vertex hf h j] at he
  exact oddInsertedHub_injective hf h (Sum.inl.inj (Sum.inr.inj he))

theorem oddInsertedDart_label_injective :
    Function.Injective (fun i => Port.label H.jointLabel (oddInsertedDart hf h i)) := by
  intro i j he
  change Port.label H.jointLabel (oddInsertedDart hf h i) = Port.label H.jointLabel (oddInsertedDart hf h j) at he
  rw [oddInsertedDart_label hf h i, oddInsertedDart_label hf h j] at he
  exact (finRotate 5).injective ((numberedWheelCycles oddWheelCycle).edge.injective he)

theorem oddPath_liftedExit_avoids (i : Fin 3) :
    Port.label H.jointLabel (oddCoveredRowPath.liftedExit H (oddCoveredRowPath_cover hf) h i) ≠
      numberedSystem.column (oddPathInsertion hf h).row 1 ∧
    Port.label H.jointLabel (oddCoveredRowPath.liftedExit H (oddCoveredRowPath_cover hf) h i) ≠
      numberedSystem.column (oddPathInsertion hf h).row 2 := by
  have hm : Port.label H.jointLabel
      (oddCoveredRowPath.liftedExit H (oddCoveredRowPath_cover hf) h i) ∈
        Set.range oddCoveredRowPath.edge :=
    ⟨i, (oddCoveredRowPath.liftedExit_label H (oddCoveredRowPath_cover hf) h i).symm⟩
  exact ⟨fun he => oddPathInsertion_first_not_covered hf h
      (((oddPathInsertion hf h).first_label.symm ▸ he) ▸ hm),
    fun he => oddPathInsertion_second_not_covered hf h
      (((oddPathInsertion hf h).second_label.symm ▸ he) ▸ hm)⟩

theorem oddInsertedDart_next_vertex (o : Bool) (i : Fin 5) :
    (oddInsertedDart hf h (finRotate 5 i)).vertex =
      ((oddPathInsertedGraph hf h o).pairing.twin (oddInsertedDart hf h i)).vertex := by
  fin_cases i
  · change ((oddPathInsertion hf h).old (oddInsertedOldDart hf h 0)).vertex =
      ((oddPathInsertedGraph hf h o).pairing.twin ((oddPathInsertion hf h).fresh false 2)).vertex
    rw [show (oddPathInsertedGraph hf h o).pairing.twin ((oddPathInsertion hf h).fresh false 2) =
      (oddPathInsertion hf h).old (oddPathInsertion hf h).second from
        (oddPathInsertion hf h).twin_fresh_two false]
    apply ((oddPathInsertion hf h).old_vertex_iff _ _).mpr
    exact (oddInsertedOldDart_vertex hf h 0).trans (oddPathInsertion_second_vertex hf h).symm
  · change ((oddPathInsertion hf h).old (oddInsertedOldDart hf h 1)).vertex =
      ((oddPathInsertedGraph hf h o).pairing.twin ((oddPathInsertion hf h).old
        (oddCoveredRowPath.liftedExit H (oddCoveredRowPath_cover hf) h (0 : Fin 3)))).vertex
    exact (((oddPathInsertion hf h).old_vertex_iff _ _).mpr
      ((oddInsertedOldDart_vertex hf h 1).trans
        (oddCoveredRowPath.liftedExit_twin_vertex H (oddCoveredRowPath_cover hf) h (0 : Fin 3)).symm)).trans
      (congrArg Port.vertex ((oddPathInsertion hf h).twin_old_of_label o _
        (oddPath_liftedExit_avoids hf h 0).1 (oddPath_liftedExit_avoids hf h 0).2)).symm
  · change ((oddPathInsertion hf h).old (oddInsertedOldDart hf h 2)).vertex =
      ((oddPathInsertedGraph hf h o).pairing.twin ((oddPathInsertion hf h).old
        (oddCoveredRowPath.liftedExit H (oddCoveredRowPath_cover hf) h (1 : Fin 3)))).vertex
    exact (((oddPathInsertion hf h).old_vertex_iff _ _).mpr
      ((oddInsertedOldDart_vertex hf h 2).trans
        (oddCoveredRowPath.liftedExit_twin_vertex H (oddCoveredRowPath_cover hf) h (1 : Fin 3)).symm)).trans
      (congrArg Port.vertex ((oddPathInsertion hf h).twin_old_of_label o _
        (oddPath_liftedExit_avoids hf h 1).1 (oddPath_liftedExit_avoids hf h 1).2)).symm
  · change ((oddPathInsertion hf h).old (oddInsertedOldDart hf h 3)).vertex =
      ((oddPathInsertedGraph hf h o).pairing.twin ((oddPathInsertion hf h).old
        (oddCoveredRowPath.liftedExit H (oddCoveredRowPath_cover hf) h (2 : Fin 3)))).vertex
    exact (((oddPathInsertion hf h).old_vertex_iff _ _).mpr
      ((oddInsertedOldDart_vertex hf h 3).trans
        (oddCoveredRowPath.liftedExit_twin_vertex H (oddCoveredRowPath_cover hf) h (2 : Fin 3)).symm)).trans
      (congrArg Port.vertex ((oddPathInsertion hf h).twin_old_of_label o _
        (oddPath_liftedExit_avoids hf h 2).1 (oddPath_liftedExit_avoids hf h 2).2)).symm
  · change ((oddPathInsertion hf h).fresh false 2).vertex =
      ((oddPathInsertedGraph hf h o).pairing.twin ((oddPathInsertion hf h).old
        (oddPathInsertion hf h).first)).vertex
    rw [show (oddPathInsertedGraph hf h o).pairing.twin ((oddPathInsertion hf h).old
      (oddPathInsertion hf h).first) = (oddPathInsertion hf h).fresh false 1 from
        (oddPathInsertion hf h).twin_first]
    rfl

@[reducible] noncomputable def oddInsertedCircuit (o : Bool) :
    (oddPathInsertedGraph hf h o).SimpleCircuit where
  length := 5
  length_pos := by decide +kernel
  dart := ⟨oddInsertedDart hf h, fun _ _ he => oddInsertedDart_vertex_injective hf h
    (congrArg Port.vertex he)⟩
  vertex_injective := oddInsertedDart_vertex_injective hf h
  edge_injective := by
    intro i j he
    apply oddInsertedDart_label_injective hf h
    rcases ((oddPathInsertedGraph hf h o).pairing.edge_eq_iff _ _).mp he with he | he
    · exact congrArg (Port.label H.jointLabel) he
    · exact (congrArg (Port.label H.jointLabel) he).trans
        ((oddPathInsertedGraph hf h o).pairing.label_twin _)
  next_vertex := oddInsertedDart_next_vertex hf h o
  next_ne_twin := by
    intro i he
    have hi := oddInsertedDart_label_injective hf h
      ((congrArg (Port.label H.jointLabel) he).trans
        ((oddPathInsertedGraph hf h o).pairing.label_twin _))
    have hn : finRotate 5 i ≠ i := by fin_cases i <;> decide +kernel
    exact hn hi

end ThomGame.Construction

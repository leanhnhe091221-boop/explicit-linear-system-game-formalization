module

public import ThomGame.Construction.WheelOddInsertion
public import ThomGame.Pictures.RowPairInsertionEuler
public import ThomGame.Pictures.RowPathCircuit

/-!
# Euler saturation for the actual exceptional pentagon insertion

The lifted three-edge path has all external ports on one side of its rim.
Its two remaining endpoint ports therefore select one old face. Choosing
the corresponding orientation of the two inserted vertices preserves
Euler saturation and component count. No minimality of the new graph is
assumed or needed.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures PortGraph RibbonConnectivity
open scoped Classical

theorem oddPath_edge_not_covered (i : Fin 5) (hi : i.val < 2) :
    (numberedWheelCycles oddWheelCycle).edge i ∉ Set.range oddCoveredRowPath.edge := by
  rw [oddCoveredRowPath_edges]
  rintro ⟨j, hj, he⟩
  have hji := (numberedWheelCycles oddWheelCycle).edge.injective he
  have hv := congrArg Fin.val hji
  omega

variable {H : SigmaGraph [] []} [IsEmpty H.Joint]
  (hf : ∀ i : WheelCycleIndex, i ≠ oddWheelCycle → SigmaRimsFacialCovers H i)
  (a : H.RimDart (numberedWheelCycles oddWheelCycle))
  (h : H.LabelHub (oddCoveredRowPath.vertex 0))
  (hh : (closedSigmaRimCircuit H oddWheelCycle a).OnCircuitVertex (.inr (.inl h.val)))

theorem oddPathInsertion_first_not_covered :
    Port.label H.jointLabel (oddPathInsertion hf h).first ∉ Set.range oddCoveredRowPath.edge := by
  rw [(oddPathInsertion hf h).first_label]
  change numberedSystem.column (rowEquiv oddRow) 1 ∉ _
  rw [odd_row_column_one]
  exact oddPath_edge_not_covered 0 (by decide +kernel)

theorem oddPathInsertion_second_not_covered :
    Port.label H.jointLabel (oddPathInsertion hf h).second ∉ Set.range oddCoveredRowPath.edge := by
  rw [(oddPathInsertion hf h).second_label]
  change numberedSystem.column (rowEquiv oddRow) 2 ∉ _
  rw [odd_row_column_two]
  exact oddPath_edge_not_covered 1 (by decide +kernel)

include hh in
theorem oddPathInsertion_first_marked :
    (closedSigmaRimCircuit H oddWheelCycle a).Marked (oddPathInsertion hf h).first := by
  apply H.rimSimpleCircuit_marked_of_vertex_label (numberedWheelCycles oddWheelCycle) a
  · rw [oddPathInsertion_first_vertex]
    exact oddPath_hubs_on_rim hf a h hh 3
  · exact ⟨0, ((oddPathInsertion hf h).first_label.trans odd_row_column_one).symm⟩

include hh in
theorem oddPathInsertion_second_marked :
    (closedSigmaRimCircuit H oddWheelCycle a).Marked (oddPathInsertion hf h).second := by
  apply H.rimSimpleCircuit_marked_of_vertex_label (numberedWheelCycles oddWheelCycle) a
  · rw [oddPathInsertion_second_vertex]
    exact hh
  · exact ⟨1, ((oddPathInsertion hf h).second_label.trans odd_row_column_two).symm⟩

include hh in
theorem oddPath_liftedExit_marked (i : Fin 3) :
    (closedSigmaRimCircuit H oddWheelCycle a).Marked
      (oddCoveredRowPath.liftedExit H (oddCoveredRowPath_cover hf) h i) := by
  apply H.rimSimpleCircuit_marked_of_vertex_label (numberedWheelCycles oddWheelCycle) a
  · exact (oddCoveredRowPath.liftedExit_vertex H (oddCoveredRowPath_cover hf) h i).symm ▸
      oddPath_hubs_on_rim hf a h hh i.castSucc
  · apply oddWheelCoveredEdges_subset
    rw [← oddCoveredRowPath_edges]
    exact ⟨i, (oddCoveredRowPath.liftedExit_label H (oddCoveredRowPath_cover hf) h i).symm⟩

include hh in
theorem oddPathInsertion_exists_same_face :
    ∃ o : Bool, H.circuitStep.SameCycle
      ((oddPathInsertion hf h).cutLeft o) ((oddPathInsertion hf h).cutRight o) := by
  obtain ⟨side, hs⟩ := oddPath_common_side hf a h hh
  exact oddCoveredRowPath.exists_face_orientation H (oddCoveredRowPath_cover hf) h
    (oddPathInsertion hf h).second (oddPathInsertion hf h).first
    (oddPathInsertion_second_vertex hf h) (oddPathInsertion_first_vertex hf h)
    (oddPathInsertion_second_not_covered hf h) (oddPathInsertion_first_not_covered hf h)
    (closedSigmaRimCircuit H oddWheelCycle a) (by decide +kernel)
    (oddPathInsertion_second_marked hf a h hh) (oddPathInsertion_first_marked hf a h hh)
    (oddPath_liftedExit_marked hf a h hh) side hs

include hh in
/-- The actual Figure 19(b) operation is available inside any Euler-saturated
stellar-normalized input. The original minimum-size assumption is absent. -/
theorem oddPathInsertedGraph_exists_euler
    (hEuler : eulerDefect H.pairing.perm H.circuitStep = 0) :
    ∃ o : Bool,
      eulerDefect (oddPathInsertedGraph hf h o).pairing.perm
        (oddPathInsertedGraph hf h o).circuitStep = 0 ∧
      Nat.card (Component (oddPathInsertedGraph hf h o).pairing.perm
        (oddPathInsertedGraph hf h o).circuitStep) =
          Nat.card (Component H.pairing.perm H.circuitStep) ∧
      (oddPathInsertedGraph hf h o).character = H.character ∧
      (oddPathInsertedGraph hf h o).sign = H.sign ∧
      Fintype.card (oddPathInsertedGraph hf h o).Hub = Fintype.card H.Hub + 2 ∧
      ∀ i : WheelCycleIndex, i ≠ oddWheelCycle →
        SigmaRimsFacialCovers (oddPathInsertedGraph hf h o) i := by
  obtain ⟨o, ho⟩ := oddPathInsertion_exists_same_face hf a h hh
  exact ⟨o, (oddPathInsertion hf h).eulerDefect_eq_zero o hEuler ho,
    (oddPathInsertion hf h).component_card_eq_of_same_face o hEuler ho,
    funext (oddPathInsertedGraph_character hf h o), oddPathInsertedGraph_sign hf h o,
    oddPathInsertedGraph_hub_card hf h o, oddPathInsertedGraph_stellar_facial_covers hf h o⟩

end ThomGame.Construction

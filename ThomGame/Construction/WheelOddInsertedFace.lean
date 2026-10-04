module

public import ThomGame.Construction.WheelOddInsertedCircuit
public import ThomGame.Pictures.CircuitHubPorts

/-!
# The new exceptional pentagon is an actual facial copy

The common empty side along the old lifted path fixes one orientation
of the inserted row pair. The same orientation preserves Euler
saturation and makes the new five-edge circuit exactly one face orbit.
Its hub and edge labels enumerate the actual exceptional pentagon.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} [IsEmpty G.Joint] (C : G.SimpleCircuit)

theorem isLabelCover_of_neighbor_labels
    (hl : ∀ i, G.hubLabel (C.hubAt i) ≠ G.hubLabel (C.hubAt (finRotate C.length i))) :
    C.IsLabelCover := by
  intro i
  obtain ⟨p, hp⟩ := C.port_eq_hubAt i false
  obtain ⟨q, hq⟩ := C.port_eq_hubAt (finRotate C.length i) true
  have ht : G.pairing.twin (C.dart i) = .hub (C.hubAt (finRotate C.length i)) q := by
    simpa only [port, incoming, Equiv.symm_apply_apply] using hq
  exact ⟨C.hubAt i, C.hubAt (finRotate C.length i), p, q, hp, ht,
    fun he => hl i (congrArg G.hubLabel he), hl i⟩

end ThomGame.Pictures.PortGraph.SimpleCircuit

namespace ThomGame.Construction

open Pictures PortGraph RibbonConnectivity
open scoped Classical BigOperators

variable {H : SigmaGraph [] []} [IsEmpty H.Joint]
  (hf : ∀ i : WheelCycleIndex, i ≠ oddWheelCycle → SigmaRimsFacialCovers H i)
  (h : H.LabelHub (oddCoveredRowPath.vertex 0))

theorem oddInsertedCircuit_hubAt (o : Bool) (i : Fin 5) :
    (oddInsertedCircuit hf h o).hubAt i = oddInsertedHub hf h i := by
  have he := ((oddInsertedCircuit hf h o).hubAt_vertex i).symm.trans
    (oddInsertedDart_vertex hf h i)
  exact Sum.inl.inj (Sum.inr.inj he)

theorem oddInsertedCircuit_cover (o : Bool) : (oddInsertedCircuit hf h o).IsLabelCover := by
  apply (oddInsertedCircuit hf h o).isLabelCover_of_neighbor_labels
  intro i he
  rw [oddInsertedCircuit_hubAt, oddInsertedCircuit_hubAt] at he
  change (oddPathInsertion hf h).hubLabel (oddInsertedHub hf h i) =
    (oddPathInsertion hf h).hubLabel (oddInsertedHub hf h (finRotate 5 i)) at he
  rw [oddInsertedHub_label, oddInsertedHub_label] at he
  have hi := (numberedWheelCycles oddWheelCycle).vertex.injective he
  have hn : i ≠ finRotate 5 i :=
    (show ∀ j : Fin 5, j ≠ finRotate 5 j from by decide +kernel) i
  exact hn hi

theorem oddInsertedCircuit_port_zero_false (o : Bool) :
    (oddInsertedCircuit hf h o).port (0, false) = (oddPathInsertion hf h).fresh false 2 := rfl

theorem oddInsertedCircuit_port_zero_true (o : Bool) :
    (oddInsertedCircuit hf h o).port (0, true) = (oddPathInsertion hf h).fresh false 1 :=
  (oddPathInsertion hf h).twin_first

theorem oddInsertedCircuit_port_succ_false (o : Bool) (i : Fin 4) :
    (oddInsertedCircuit hf h o).port (i.succ, false) =
      (oddPathInsertion hf h).old (oddInsertedOldDart hf h i) := rfl

theorem oddInsertedCircuit_port_succ_true (o : Bool) (i : Fin 4) :
    (oddInsertedCircuit hf h o).port (i.succ, true) =
      (oddPathInsertion hf h).old
        (oddCoveredRowPath.liftedEntry H (oddCoveredRowPath_cover hf) h (oddPathInsertion hf h).second i) := by
  fin_cases i
  · exact (oddPathInsertion hf h).twin_fresh_two false
  · exact (oddPathInsertion hf h).twin_old_of_label o _
      (oddPath_liftedExit_avoids hf h 0).1 (oddPath_liftedExit_avoids hf h 0).2
  · exact (oddPathInsertion hf h).twin_old_of_label o _
      (oddPath_liftedExit_avoids hf h 1).1 (oddPath_liftedExit_avoids hf h 1).2
  · exact (oddPathInsertion hf h).twin_old_of_label o _
      (oddPath_liftedExit_avoids hf h 2).1 (oddPath_liftedExit_avoids hf h 2).2

theorem oddInsertedCircuit_face_of_corners (o : Bool)
    (hr : ∀ i : Fin 4,
      H.rotation (if o then oddInsertedOldDart hf h i else
        oddCoveredRowPath.liftedEntry H (oddCoveredRowPath_cover hf) h (oddPathInsertion hf h).second i) =
      (if o then oddCoveredRowPath.liftedEntry H (oddCoveredRowPath_cover hf) h (oddPathInsertion hf h).second i
        else oddInsertedOldDart hf h i)) :
    (oddInsertedCircuit hf h o).BoundsFaceOrbit o := by
  apply (oddInsertedCircuit hf h o).boundsFaceOrbit_of_corner_rotation
  intro i
  cases i using Fin.cases with
  | zero =>
    cases o
    · simp only [Bool.not_false]
      rw [oddInsertedCircuit_port_zero_true hf h false, oddInsertedCircuit_port_zero_false hf h false]
      rfl
    · simp only [Bool.not_true]
      rw [oddInsertedCircuit_port_zero_false hf h true, oddInsertedCircuit_port_zero_true hf h true]
      rfl
  | succ i =>
    cases o
    · simp only [Bool.not_false]
      rw [oddInsertedCircuit_port_succ_true hf h false i, oddInsertedCircuit_port_succ_false hf h false i]
      exact ((oddPathInsertion hf h).rotation_old false _).trans
        (congrArg (oddPathInsertion hf h).old (hr i))
    · simp only [Bool.not_true]
      rw [oddInsertedCircuit_port_succ_false hf h true i, oddInsertedCircuit_port_succ_true hf h true i]
      exact ((oddPathInsertion hf h).rotation_old true _).trans
        (congrArg (oddPathInsertion hf h).old (hr i))

variable (a : H.RimDart (numberedWheelCycles oddWheelCycle))
  (hh : (closedSigmaRimCircuit H oddWheelCycle a).OnCircuitVertex (.inr (.inl h.val)))

noncomputable def oddInsertionMarkedPath : (closedSigmaRimCircuit H oddWheelCycle a).MarkedPath :=
  oddCoveredRowPath.markedPath H (oddCoveredRowPath_cover hf) h
    (oddPathInsertion hf h).second (oddPathInsertion hf h).first
    (oddPathInsertion_second_vertex hf h) (oddPathInsertion_first_vertex hf h)
    (oddPathInsertion_second_not_covered hf h) (oddPathInsertion_first_not_covered hf h)
    (closedSigmaRimCircuit H oddWheelCycle a) (by decide +kernel)
    (oddPathInsertion_second_marked hf a h hh) (oddPathInsertion_first_marked hf a h hh)
    (oddPath_liftedExit_marked hf a h hh)

include hh in
theorem oddInsertedCircuit_exists_face_and_same_face : ∃ o : Bool,
    H.circuitStep.SameCycle ((oddPathInsertion hf h).cutLeft o) ((oddPathInsertion hf h).cutRight o) ∧
    (oddInsertedCircuit hf h o).BoundsFaceOrbit o := by
  obtain ⟨s, hs⟩ := oddPath_common_side hf a h hh
  have hext : ∀ i, ∀ z : H.Dart, z.vertex = ((oddInsertionMarkedPath hf h a hh).entry i).vertex →
      ¬ (closedSigmaRimCircuit H oddWheelCycle a).Marked z →
        (closedSigmaRimCircuit H oddWheelCycle a).Frontier s z := by
    intro i z hz hn
    exact hs i z (hz.trans (oddCoveredRowPath.liftedEntry_vertex H (oddCoveredRowPath_cover hf) h
      (oddPathInsertion hf h).second (oddPathInsertion_second_vertex hf h) i)) hn
  obtain ⟨o, ho, hr, ht⟩ := (oddInsertionMarkedPath hf h a hh).exists_face_orientation_and_corners s hext
  refine ⟨o, ho, oddInsertedCircuit_face_of_corners hf h o ?_⟩
  intro i
  cases i using Fin.lastCases with
  | last => exact ht
  | cast i =>
    rw [oddInsertedOldDart_castSucc]
    exact hr i

include hh in
/-- A single actual insertion simultaneously creates the facial pentagon,
preserves Euler saturation and character, and preserves every stellar cover. -/
theorem oddInsertedCircuit_exists_facial_copy
    (hEuler : eulerDefect H.pairing.perm H.circuitStep = 0) :
    ∃ o : Bool,
      eulerDefect (oddPathInsertedGraph hf h o).pairing.perm
        (oddPathInsertedGraph hf h o).circuitStep = 0 ∧
      (oddPathInsertedGraph hf h o).character = H.character ∧
      (oddInsertedCircuit hf h o).BoundsFaceOrbit o ∧
      (oddInsertedCircuit hf h o).IsLabelCover ∧
      (∀ i : Fin 5, (oddPathInsertedGraph hf h o).hubLabel ((oddInsertedCircuit hf h o).hubAt i) =
        (numberedWheelCycles oddWheelCycle).vertex i) ∧
      (∀ i : Fin 5, Port.label (oddPathInsertedGraph hf h o).jointLabel ((oddInsertedCircuit hf h o).dart i) =
        (numberedWheelCycles oddWheelCycle).edge (finRotate 5 i)) ∧
      ∀ i : WheelCycleIndex, i ≠ oddWheelCycle → SigmaRimsFacialCovers (oddPathInsertedGraph hf h o) i := by
  obtain ⟨o, ho, hfC⟩ := oddInsertedCircuit_exists_face_and_same_face hf h a hh
  refine ⟨o, (oddPathInsertion hf h).eulerDefect_eq_zero o hEuler ho,
    funext (oddPathInsertedGraph_character hf h o), hfC, oddInsertedCircuit_cover hf h o, ?_,
    oddInsertedDart_label hf h, oddPathInsertedGraph_stellar_facial_covers hf h o⟩
  intro i
  rw [oddInsertedCircuit_hubAt]
  exact oddInsertedHub_label hf h i

include hh in
/-- Euler realization supplies an actual closed diagram with exactly the
inserted relation multiset. This does not assert a graph isomorphism. -/
theorem oddInsertedCircuit_exists_diagram
    (hEuler : eulerDefect H.pairing.perm H.circuitStep = 0) :
    ∃ (o : Bool) (d : SigmaDiagram [] []),
      SigmaGraphWitness d (oddPathInsertedGraph hf h o) ∧
      d.size = Fintype.card H.Hub + 2 ∧ d.sign = H.sign ∧
      (d.labels : Multiset (Fin 1417152)) =
        (∑ x : H.Hub, ([H.hubLabel x] : Multiset (Fin 1417152))) +
          [rowEquiv oddRow, rowEquiv oddRow] ∧
      (oddInsertedCircuit hf h o).BoundsFaceOrbit o := by
  obtain ⟨o, ho, hc⟩ := oddInsertedCircuit_exists_face_and_same_face hf h a hh
  have he := (oddPathInsertion hf h).eulerDefect_eq_zero o hEuler ho
  obtain ⟨d, hd, hsize, hsign⟩ := (oddPathInsertedGraph hf h o).exists_closed_diagram_of_saturated_preserving
    (fun _ => by change 0 < 3; decide +kernel)
    ((oddPathInsertedGraph hf h o).rotationEuler_saturated_iff.mpr he)
  exact ⟨o, d, ⟨he, hsize.symm, hsign.symm⟩,
    hsize.trans (oddPathInsertedGraph_hub_card hf h o),
    hsign.trans (oddPathInsertedGraph_sign hf h o),
    hd.trans ((oddPathInsertion hf h).graph_relations o), hc⟩

end ThomGame.Construction

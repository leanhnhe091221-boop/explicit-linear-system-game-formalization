module

public import ThomGame.Construction.WheelOddPathMeasure

/-!
# An exceptional insertion strictly decreases the unfinished-path count

The chosen path becomes part of the new facial pentagon. Any previously
good path lies on a circuit disjoint from the cut edges and remains good.
The actual old/new seed bijection then gives an injection from new bad
seeds to old bad seeds whose image omits the chosen seed.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures PortGraph RibbonConnectivity
open scoped Classical

variable {H : SigmaGraph [] []} [IsEmpty H.Joint]
  (hf : ∀ i : WheelCycleIndex, i ≠ oddWheelCycle → SigmaRimsFacialCovers H i)
  (h : H.LabelHub (oddCoveredRowPath.vertex 0)) (hbad : ¬ OddPathGood H h)

include hbad in
theorem oddPath_good_circuit_avoids_cuts (C : H.SimpleCircuit)
    (hl : ∀ i : Fin C.length, Port.label H.jointLabel (C.dart i) ∈ Set.range (numberedWheelCycles oddWheelCycle).edge)
    (hface : ∃ side, C.BoundsFaceOrbit side) (hcover : C.IsLabelCover) :
    ¬ C.Marked (oddPathInsertion hf h).first ∧ ¬ C.Marked (oddPathInsertion hf h).second := by
  let D := closedSigmaRimCircuit H oddWheelCycle (oddPathSeedRim H h)
  have hs : D.Marked (oddPathSeedPort H h) := ⟨(0, false), rfl⟩
  have ha : D.Marked (oddPathInsertion hf h).first :=
    oddPathInsertion_first_marked hf (oddPathSeedRim H h) h (oddPathSeedRim_onCircuit H h)
  refine ⟨fun hc => hbad ?_, fun hc => hbad ?_⟩
  · exact H.rimFacialCoverAt_of_marked
      (numberedWheelCycles oddWheelCycle).empty_boundary_no_rim
      (numberedWheelCycles oddWheelCycle).empty_boundary_no_rim D
      (H.rimSimpleCircuit_rim (numberedWheelCycles oddWheelCycle)
        (numberedWheelCycles oddWheelCycle).empty_boundary_no_rim
        (numberedWheelCycles oddWheelCycle).empty_boundary_no_rim (oddPathSeedRim H h))
      ha hs ⟨C, hl, hface, hcover, hc⟩
  · exact ⟨C, hl, hface, hcover, hc⟩

include hbad in
theorem oddInserted_preserves_good_seed (o : Bool) (k : H.LabelHub (oddCoveredRowPath.vertex 0))
    (hk : OddPathGood H k) :
    OddPathGood (oddPathInsertedGraph hf h o) (oddInsertedSeedEquiv hf h o k) := by
  obtain ⟨C, hl, ⟨side, hface⟩, hcover, hm⟩ := hk
  obtain ⟨ha, hb⟩ := oddPath_good_circuit_avoids_cuts hf h hbad C hl ⟨side, hface⟩ hcover
  let D := (oddPathInsertion hf h).disjointCircuit o C ha hb
  refine ⟨D, ?_, ⟨side, (oddPathInsertion hf h).disjointCircuit_face o C ha hb side hface⟩,
    (oddPathInsertion hf h).disjointCircuit_cover o C ha hb hcover, ?_⟩
  · intro i
    change Port.label H.jointLabel ((oddPathInsertion hf h).old (C.dart i)) ∈ _
    rw [(oddPathInsertion hf h).old_label]
    exact hl i
  · rw [oddInsertedSeedPort]
    exact ((oddPathInsertion hf h).disjointCircuit_marked o C ha hb _).mpr hm

theorem oddInserted_selected_seed_good (o : Bool)
    (hc : (oddInsertedCircuit hf h o).BoundsFaceOrbit o) :
    OddPathGood (oddPathInsertedGraph hf h o) (oddInsertedSeedEquiv hf h o h) := by
  refine ⟨oddInsertedCircuit hf h o, fun i => ⟨finRotate 5 i, (oddInsertedDart_label hf h i).symm⟩,
    ⟨o, hc⟩, oddInsertedCircuit_cover hf h o, ?_⟩
  rw [oddInsertedSeedPort]
  exact ⟨(1, true), oddInsertedCircuit_port_succ_true hf h o (0 : Fin 4)⟩

noncomputable def oddUnfinishedPathPullback (o : Bool) :
    OddUnfinishedPath (oddPathInsertedGraph hf h o) → OddUnfinishedPath H := fun k =>
  ⟨(oddInsertedSeedEquiv hf h o).symm k.val, fun hk => k.property (by
    have hg := oddInserted_preserves_good_seed hf h hbad o ((oddInsertedSeedEquiv hf h o).symm k.val) hk
    simpa only [Equiv.apply_symm_apply] using hg)⟩

theorem oddUnfinishedPathPullback_injective (o : Bool) :
    Function.Injective (oddUnfinishedPathPullback hf h hbad o) := by
  intro k l he
  apply Subtype.ext
  exact (oddInsertedSeedEquiv hf h o).symm.injective (congrArg Subtype.val he)

theorem oddUnfinishedPathPullback_omits (o : Bool)
    (hc : (oddInsertedCircuit hf h o).BoundsFaceOrbit o) :
    (⟨h, hbad⟩ : OddUnfinishedPath H) ∉ Set.range (oddUnfinishedPathPullback hf h hbad o) := by
  rintro ⟨k, hk⟩
  have he : (oddInsertedSeedEquiv hf h o).symm k.val = h := congrArg Subtype.val hk
  have hg := oddInserted_selected_seed_good hf h o hc
  have hv : (oddInsertedSeedEquiv hf h o) h = k.val :=
    (congrArg (oddInsertedSeedEquiv hf h o) he).symm.trans
      ((oddInsertedSeedEquiv hf h o).apply_symm_apply k.val)
  exact k.property (hv ▸ hg)

include hbad in
theorem oddUnfinishedPathCount_insert_lt (o : Bool)
    (hc : (oddInsertedCircuit hf h o).BoundsFaceOrbit o) :
    oddUnfinishedPathCount (oddPathInsertedGraph hf h o) < oddUnfinishedPathCount H := by
  simp only [oddUnfinishedPathCount, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_injective_of_notMem (oddUnfinishedPathPullback hf h hbad o)
    (oddUnfinishedPathPullback_injective hf h hbad o) (oddUnfinishedPathPullback_omits hf h hbad o hc)

include hbad in
theorem oddPathInsertion_exists_decreasing
    (hEuler : eulerDefect H.pairing.perm H.circuitStep = 0) :
    ∃ o : Bool,
      eulerDefect (oddPathInsertedGraph hf h o).pairing.perm (oddPathInsertedGraph hf h o).circuitStep = 0 ∧
      (oddPathInsertedGraph hf h o).character = H.character ∧
      oddUnfinishedPathCount (oddPathInsertedGraph hf h o) < oddUnfinishedPathCount H ∧
      ∀ i : WheelCycleIndex, i ≠ oddWheelCycle → SigmaRimsFacialCovers (oddPathInsertedGraph hf h o) i := by
  obtain ⟨o, ho, hc⟩ := oddInsertedCircuit_exists_face_and_same_face hf h
    (oddPathSeedRim H h) (oddPathSeedRim_onCircuit H h)
  exact ⟨o, (oddPathInsertion hf h).eulerDefect_eq_zero o hEuler ho,
    funext (oddPathInsertedGraph_character hf h o), oddUnfinishedPathCount_insert_lt hf h hbad o hc,
    oddPathInsertedGraph_stellar_facial_covers hf h o⟩

end ThomGame.Construction

module

public import ThomGame.Pictures.RowPathCovers
public import ThomGame.Pictures.CircuitPathFaces

/-!
# The actual lifted row path gives a marked circuit path

The listed path darts are chosen from the already proved original edge
lifts. Distinct path labels exclude reversal at internal corners, and
endpoint labels outside the path exclude reversal at its ends.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.RowPath

open scoped Classical

variable {R S : Type*} {A : SparseSystem R S}
  (P : RowPath A) (G : SolutionGroup.RowGraph A [] []) [IsEmpty G.Joint]
  (hc : ∀ x : G.Dart, Port.label G.jointLabel x ∈ Set.range P.edge → G.EdgeHasDistinctHubLabels x)
  (h : G.LabelHub (P.vertex 0))

noncomputable def liftedExit (i : Fin P.length) : G.Dart := (P.lift_edge G hc h i).choose

theorem liftedExit_vertex (i : Fin P.length) :
    (P.liftedExit G hc h i).vertex = .inr (.inl (P.hub G hc h i.castSucc)) :=
  (P.lift_edge G hc h i).choose_spec.1

theorem liftedExit_twin_vertex (i : Fin P.length) :
    (G.pairing.twin (P.liftedExit G hc h i)).vertex = .inr (.inl (P.hub G hc h i.succ)) :=
  (P.lift_edge G hc h i).choose_spec.2.1

theorem liftedExit_label (i : Fin P.length) : Port.label G.jointLabel (P.liftedExit G hc h i) = P.edge i :=
  (P.lift_edge G hc h i).choose_spec.2.2

noncomputable def liftedEntry (start : G.Dart) : Fin (P.length + 1) → G.Dart :=
  Fin.cases start (fun i => G.pairing.twin (P.liftedExit G hc h i))

theorem liftedEntry_zero (start : G.Dart) : P.liftedEntry G hc h start 0 = start := rfl

theorem liftedEntry_succ (start : G.Dart) (i : Fin P.length) :
    P.liftedEntry G hc h start i.succ = G.pairing.twin (P.liftedExit G hc h i) := rfl

variable (start finish : G.Dart)
  (hvStart : start.vertex = .inr (.inl (P.hub G hc h 0)))
  (hvFinish : finish.vertex = .inr (.inl (P.hub G hc h (Fin.last P.length))))
  (hStart : Port.label G.jointLabel start ∉ Set.range P.edge)
  (hFinish : Port.label G.jointLabel finish ∉ Set.range P.edge)

include hvStart in
theorem liftedEntry_vertex (i : Fin (P.length + 1)) :
    (P.liftedEntry G hc h start i).vertex = .inr (.inl (P.hub G hc h i)) := by
  cases i using Fin.cases with
  | zero => exact hvStart
  | succ i => exact P.liftedExit_twin_vertex G hc h i

theorem liftedEntry_label_cases (i : Fin (P.length + 1)) :
    (i = 0 ∧ Port.label G.jointLabel (P.liftedEntry G hc h start i) = Port.label G.jointLabel start) ∨
      ∃ j : Fin P.length, j.val + 1 = i.val ∧
        Port.label G.jointLabel (P.liftedEntry G hc h start i) = P.edge j := by
  cases i using Fin.cases with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  | succ j =>
    refine Or.inr ⟨j, rfl, ?_⟩
    rw [P.liftedEntry_succ, G.pairing.label_twin, P.liftedExit_label]

include hStart in
theorem lifted_corner_ne (i : Fin P.length) :
    P.liftedExit G hc h i ≠ P.liftedEntry G hc h start i.castSucc := by
  intro he
  have hl := congrArg (Port.label G.jointLabel) he
  rw [P.liftedExit_label] at hl
  rcases P.liftedEntry_label_cases G hc h start i.castSucc with ⟨_, hs⟩ | ⟨j, hj, hs⟩
  · exact hStart ⟨i, hl.trans hs⟩
  · have hij := P.edge.injective (hl.trans hs)
    have hv := congrArg Fin.val hij
    have hh : j.val + 1 = i.val := hj
    omega

include hFinish in
theorem lifted_terminal_ne (hn : 0 < P.length) :
    finish ≠ P.liftedEntry G hc h start (Fin.last P.length) := by
  intro he
  have hl := congrArg (Port.label G.jointLabel) he
  rcases P.liftedEntry_label_cases G hc h start (Fin.last P.length) with ⟨hz, _⟩ | ⟨j, _, hs⟩
  · have hz' := congrArg Fin.val hz
    change P.length = 0 at hz'
    omega
  · exact hFinish ⟨j, (hl.trans hs).symm⟩

variable (C : G.SimpleCircuit) (hn : 0 < P.length)
  (hmStart : C.Marked start) (hmFinish : C.Marked finish)
  (hmExit : ∀ i : Fin P.length, C.Marked (P.liftedExit G hc h i))

noncomputable def markedPath : C.MarkedPath where
  length := P.length
  entry := P.liftedEntry G hc h start
  exit := P.liftedExit G hc h
  terminal := finish
  entry_marked i := by
    cases i using Fin.cases with
    | zero => exact hmStart
    | succ i => exact (C.marked_twin_iff _).mpr (hmExit i)
  exit_marked := hmExit
  terminal_marked := hmFinish
  corner_vertex i := (P.liftedExit_vertex G hc h i).trans (P.liftedEntry_vertex G hc h start hvStart i.castSucc).symm
  corner_ne := P.lifted_corner_ne G hc h start hStart
  cross _ := rfl
  terminal_vertex := hvFinish.trans (P.liftedEntry_vertex G hc h start hvStart (Fin.last P.length)).symm
  terminal_ne := P.lifted_terminal_ne G hc h start finish hFinish hn

include hvStart hvFinish hStart hFinish hn hmStart hmFinish hmExit in
theorem exists_face_orientation (s : Bool)
    (hext : ∀ i, ∀ z : G.Dart, z.vertex = .inr (.inl (P.hub G hc h i)) → ¬ C.Marked z → C.Frontier s z) :
    ∃ o : Bool, G.circuitStep.SameCycle (if o then start else finish)
      (G.pairing.twin (if o then finish else start)) := by
  let p := P.markedPath G hc h start finish hvStart hvFinish hStart hFinish C hn hmStart hmFinish hmExit
  exact p.exists_face_orientation s (fun i z hz hzM =>
    hext i z (hz.trans (P.liftedEntry_vertex G hc h start hvStart i)) hzM)

end ThomGame.Pictures.PortGraph.RowPath

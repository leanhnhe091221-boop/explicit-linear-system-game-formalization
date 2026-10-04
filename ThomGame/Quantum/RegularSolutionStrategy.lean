module

public import ThomGame.Quantum.LinearSystemObservables
public import ThomGame.Quantum.RegularCentralState
public import ThomGame.Groups.PaperSolutionGroup

/-! A concrete perfect commuting strategy from a nontrivial solution-group involution. -/

@[expose] public section
namespace ThomGame.Quantum

variable {R C : Type*} (S : SparseSystem R C)

noncomputable def regularSolutionObservables
    (hJ : SolutionGroup.Paper.J S ≠ 1) :
    LinearSystemObservables S (GroupHilbert (SolutionGroup.Paper.GroupOf S)) where
  state := GroupHilbert.centralState (SolutionGroup.Paper.J S)
  norm_state := GroupHilbert.centralState_norm _ hJ
  left c := GroupHilbert.left (SolutionGroup.Paper.x S c)
  right c := GroupHilbert.right (SolutionGroup.Paper.x S c)
  left_selfAdjoint c := GroupHilbert.left_selfAdjoint _ (SolutionGroup.Paper.x_sq S c)
  right_selfAdjoint c := GroupHilbert.right_selfAdjoint _ (SolutionGroup.Paper.x_sq S c)
  left_square c := GroupHilbert.left_square _ (SolutionGroup.Paper.x_sq S c)
  right_square c := GroupHilbert.right_square _ (SolutionGroup.Paper.x_sq S c)
  cross c d := GroupHilbert.left_right_commute _ _
  row_commute r i j := by
    change GroupHilbert.left _ * GroupHilbert.left _ = GroupHilbert.left _ * GroupHilbert.left _
    rw [← GroupHilbert.left_mul, ← GroupHilbert.left_mul, (SolutionGroup.Paper.row_commutes S r i j).eq]
  row_state r := by
    rw [← GroupHilbert.left_mul, ← GroupHilbert.left_mul, SolutionGroup.Paper.row_product]
    rcases bit_cases (S.rhs r) with hb | hb
    · simp [hb, GroupHilbert.left_one, bitSign_zero]
    · simp [hb, GroupHilbert.left_centralState _ (SolutionGroup.Paper.J_sq S), bitSign_one]
  consistent_state c := GroupHilbert.left_right_centralState _ _
    (SolutionGroup.Paper.x_sq S c) (SolutionGroup.Paper.J_commutes_x S c)

noncomputable def regularSolutionStrategy (hJ : SolutionGroup.Paper.J S ≠ 1) :
    CommutingStrategy R C (Fin 3 → ZMod 2) (ZMod 2)
      (GroupHilbert (SolutionGroup.Paper.GroupOf S)) :=
  (regularSolutionObservables S hJ).strategy

theorem regularSolutionStrategy_state (hJ : SolutionGroup.Paper.J S ≠ 1) :
    (regularSolutionStrategy S hJ).state =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
        (GroupHilbert.delta 1 - GroupHilbert.delta (SolutionGroup.Paper.J S)) := rfl

theorem regularSolutionStrategy_born (hJ : SolutionGroup.Paper.J S ≠ 1)
    (r : R) (c : C) (a : Fin 3 → ZMod 2) (b : ZMod 2) :
    (regularSolutionStrategy S hJ).correlation r c a b =
      ‖(bitProjection (GroupHilbert.left (SolutionGroup.Paper.x S (S.column r 0))) (a 0) *
        bitProjection (GroupHilbert.left (SolutionGroup.Paper.x S (S.column r 1))) (a 1) *
        bitProjection (GroupHilbert.left (SolutionGroup.Paper.x S (S.column r 2))) (a 2))
        (bitProjection (GroupHilbert.right (SolutionGroup.Paper.x S c)) b
          (GroupHilbert.centralState (SolutionGroup.Paper.J S)))‖ ^ 2 := rfl

theorem regularSolutionStrategy_rejected_zero (hJ : SolutionGroup.Paper.J S ≠ 1)
    (r : R) (i : Fin 3) (a : Fin 3 → ZMod 2) (b : ZMod 2) (h : ¬ S.Accepts r i a b) :
    (regularSolutionStrategy S hJ).correlation r (S.column r i) a b = 0 :=
  (regularSolutionObservables S hJ).rejected_probability_zero r i a b h

theorem regularSolutionStrategy_perfect [Fintype R] [Nonempty R] [Fintype C] [LinearOrder C]
    (hJ : SolutionGroup.Paper.J S ≠ 1) :
    S.incidenceGame.success (regularSolutionStrategy S hJ).correlation = 1 :=
  (regularSolutionObservables S hJ).perfect_success

end ThomGame.Quantum

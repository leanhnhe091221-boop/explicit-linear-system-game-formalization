module

public import ThomGame.Analysis.PaperSolutionApproximation
public import ThomGame.Quantum.BinaryMeasurement

/-! Lift actual solution matrices to the free group, with J exactly minus the identity,
and verify all five literal classes of paper relator words. -/

@[expose] public section
namespace ThomGame.Analysis

open Quantum

variable {R C : Type*} {d : Nat}

noncomputable def negativeCentralAssignment (x : C → UnitaryMatrix d) :
    MatrixAssignment (SolutionGroup.Generator C) d :=
  FreeGroup.lift (fun a => a.elim (-1) x)

theorem negativeCentralAssignment_none (x : C → UnitaryMatrix d) :
    negativeCentralAssignment x (FreeGroup.of none) = -1 := by
  simp [negativeCentralAssignment]

theorem negativeCentralAssignment_some (x : C → UnitaryMatrix d) (c : C) :
    negativeCentralAssignment x (FreeGroup.of (some c)) = x c := by
  simp [negativeCentralAssignment]

theorem negativeCentralAssignment_row (S : SparseSystem R C) (x : C → UnitaryMatrix d) (r : R) :
    negativeCentralAssignment x (FreeGroup.mk (SolutionGroup.rowWord S r)) =
      x (S.column r 0) * x (S.column r 1) * x (S.column r 2) := by
  simp only [← assignment_word_eval, SolutionGroup.rowWord, Word.eval_append,
    SolutionGroup.variableWord, Word.eval_generator, negativeCentralAssignment_some]

theorem negativeCentralAssignment_rhs_val (S : SparseSystem R C) (x : C → UnitaryMatrix d) (r : R) :
    (negativeCentralAssignment x (FreeGroup.mk (SolutionGroup.rhsWord S r))).val =
      bitSign (S.rhs r) • 1 := by
  rcases bit_cases (S.rhs r) with hb | hb <;>
    simp [SolutionGroup.rhsWord, hb, ← assignment_word_eval, SolutionGroup.centralWord,
      negativeCentralAssignment_none, bitSign_zero, bitSign_one, Unitary.coe_neg]

theorem negativeCentralAssignment_isApprox (S : SparseSystem R C) (x : C → UnitaryMatrix d)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hs : ∀ c, hsNorm ((x c).val * (x c).val - 1) ≤ δ)
    (hr : ∀ r, hsNorm ((x (S.column r 0)).val * (x (S.column r 1)).val *
      (x (S.column r 2)).val - bitSign (S.rhs r) • 1) ≤ δ)
    (hc : ∀ r i j, hsNorm ((x (S.column r i)).val * (x (S.column r j)).val -
      (x (S.column r j)).val * (x (S.column r i)).val) ≤ δ) :
    IsApproxRepresentation (SolutionGroup.Paper.relators S) δ (negativeCentralAssignment x) := by
  rintro _ ⟨tag, rfl⟩
  cases tag with
  | centralSquare =>
    simpa [← assignment_word_eval, SolutionGroup.Paper.relatorWord,
      SolutionGroup.centralWord, negativeCentralAssignment_none] using hδ
  | variableSquare c =>
    have hsc : unitaryLength (x c * x c) ≤ δ := hs c
    simpa only [← assignment_word_eval, SolutionGroup.Paper.relatorWord,
      Word.eval_append, SolutionGroup.variableWord, Word.eval_generator,
      negativeCentralAssignment_some] using hsc
  | centralCommutes c =>
    simpa [← assignment_word_eval, SolutionGroup.Paper.relatorWord, Word.eval_commutator,
      SolutionGroup.centralWord, SolutionGroup.variableWord, negativeCentralAssignment_none,
      negativeCentralAssignment_some] using hδ
  | rowCommutes r p =>
    rw [← assignment_word_eval]
    simp only [SolutionGroup.Paper.relatorWord, Word.eval_commutator,
      SolutionGroup.variableWord, Word.eval_generator, negativeCentralAssignment_some]
    rw [← unitaryDist_swap]
    exact hc r p.val.1 p.val.2
  | rowEquation r =>
    rw [← assignment_word_eval]
    simp only [SolutionGroup.Paper.relatorWord, Word.equation, Word.eval_append,
      Word.eval_inverse, assignment_word_eval]
    rw [← unitaryDist_eq_length]
    unfold unitaryDist
    rw [negativeCentralAssignment_row, negativeCentralAssignment_rhs_val]
    exact hr r

end ThomGame.Analysis

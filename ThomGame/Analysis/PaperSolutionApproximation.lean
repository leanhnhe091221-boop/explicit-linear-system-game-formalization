module

public import ThomGame.Analysis.SolutionRowApproximation
public import ThomGame.Groups.PaperSolutionGroup

/-! The paper's commutator conventions have exactly the same matrix defect bound. -/

@[expose] public section
namespace ThomGame.Analysis

variable {R C : Type*} {d : Nat}

theorem assignment_commutator_swap {α : Type*} (f : MatrixAssignment α d) (u v : Word α) :
    unitaryLength (f (FreeGroup.mk (Word.commutator u v))) =
      unitaryLength (f (FreeGroup.mk (Word.commutator v u))) := by
  simp only [← assignment_word_eval, Word.eval_commutator]
  exact unitaryLength_commutator_swap _ _

theorem paper_approx_nonneg (S : SparseSystem R C) {δ : ℝ}
    (f : MatrixAssignment (SolutionGroup.Generator C) d)
    (hf : IsApproxRepresentation (SolutionGroup.Paper.relators S) δ f) : 0 ≤ δ :=
  (unitaryLength_nonneg _).trans (hf _ ⟨.centralSquare, rfl⟩)

theorem paper_approx_to_solution (S : SparseSystem R C) {δ : ℝ}
    (f : MatrixAssignment (SolutionGroup.Generator C) d)
    (hf : IsApproxRepresentation (SolutionGroup.Paper.relators S) δ f) :
    IsApproxRepresentation (SolutionGroup.relators S) δ f := by
  have hδ := paper_approx_nonneg S f hf
  rintro _ ⟨tag, rfl⟩
  cases tag with
  | centralSquare => exact hf _ ⟨.centralSquare, rfl⟩
  | variableSquare c => exact hf _ ⟨.variableSquare c, rfl⟩
  | centralCommutes c =>
    change unitaryLength (f (FreeGroup.mk (Word.commutator SolutionGroup.centralWord
      (SolutionGroup.variableWord c)))) ≤ δ
    rw [assignment_commutator_swap]
    exact hf _ ⟨.centralCommutes c, rfl⟩
  | rowCommutes r i j =>
    rcases lt_trichotomy i j with h | rfl | h
    · exact hf _ ⟨.rowCommutes r ⟨(i, j), h⟩, rfl⟩
    · simpa [← assignment_word_eval, SolutionGroup.relatorWord, Word.eval_commutator,
        mul_assoc] using hδ
    · change unitaryLength (f (FreeGroup.mk (Word.commutator
        (SolutionGroup.variableWord (S.column r i))
        (SolutionGroup.variableWord (S.column r j))))) ≤ δ
      rw [assignment_commutator_swap]
      exact hf _ ⟨.rowCommutes r ⟨(j, i), h⟩, rfl⟩
  | rowEquation r => exact hf _ ⟨.rowEquation r, rfl⟩

theorem solution_approx_to_paper (S : SparseSystem R C) {δ : ℝ}
    (f : MatrixAssignment (SolutionGroup.Generator C) d)
    (hf : IsApproxRepresentation (SolutionGroup.relators S) δ f) :
    IsApproxRepresentation (SolutionGroup.Paper.relators S) δ f := by
  rintro _ ⟨tag, rfl⟩
  cases tag with
  | centralSquare => exact hf _ ⟨.centralSquare, rfl⟩
  | variableSquare c => exact hf _ ⟨.variableSquare c, rfl⟩
  | centralCommutes c =>
    change unitaryLength (f (FreeGroup.mk (Word.commutator (SolutionGroup.variableWord c)
      SolutionGroup.centralWord))) ≤ δ
    rw [assignment_commutator_swap]
    exact hf _ ⟨.centralCommutes c, rfl⟩
  | rowCommutes r p => exact hf _ ⟨.rowCommutes r p.val.1 p.val.2, rfl⟩
  | rowEquation r => exact hf _ ⟨.rowEquation r, rfl⟩

theorem paper_approx_iff_solution (S : SparseSystem R C) (δ : ℝ)
    (f : MatrixAssignment (SolutionGroup.Generator C) d) :
    IsApproxRepresentation (SolutionGroup.Paper.relators S) δ f ↔
      IsApproxRepresentation (SolutionGroup.relators S) δ f :=
  ⟨paper_approx_to_solution S f, solution_approx_to_paper S f⟩

theorem paper_approximatelyTrivial_iff_solution (S : SparseSystem R C)
    (w : FreeGroup (SolutionGroup.Generator C)) :
    ApproximatelyTrivial (SolutionGroup.Paper.relators S) w ↔
      ApproximatelyTrivial (SolutionGroup.relators S) w := by
  simp only [ApproximatelyTrivial, paper_approx_iff_solution]

theorem paper_ordered_approx_to_original [LinearOrder C] (S : SparseSystem R C) {δ : ℝ}
    (f : MatrixAssignment (SolutionGroup.Generator C) d)
    (hf : IsApproxRepresentation (SolutionGroup.Paper.relators S.ordered) δ f) :
    IsApproxRepresentation (SolutionGroup.relators S) (4 * δ) f :=
  solution_approx_permute S.orderedPermutation.symm f (paper_approx_to_solution S.ordered f hf)

theorem original_approx_to_paper_ordered [LinearOrder C] (S : SparseSystem R C) {δ : ℝ}
    (f : MatrixAssignment (SolutionGroup.Generator C) d)
    (hf : IsApproxRepresentation (SolutionGroup.relators S) δ f) :
    IsApproxRepresentation (SolutionGroup.Paper.relators S.ordered) (4 * δ) f :=
  solution_approx_to_paper S.ordered f (solution_approx_permute S.orderedPermutation f hf)

theorem paper_ordered_approximatelyTrivial [LinearOrder C] (S : SparseSystem R C)
    (w : FreeGroup (SolutionGroup.Generator C))
    (h : ApproximatelyTrivial (SolutionGroup.relators S) w) :
    ApproximatelyTrivial (SolutionGroup.Paper.relators S.ordered) w :=
  (paper_approximatelyTrivial_iff_solution S.ordered w).mpr
    (solution_approximatelyTrivial_permute S.orderedPermutation w h)

end ThomGame.Analysis

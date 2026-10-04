module

public import ThomGame.Analysis.SolutionRowApproximation
public import ThomGame.Groups.SolutionGroupReindex

/-! Renumbering solution generators preserves every approximate relator bound. -/

@[expose] public section
namespace ThomGame.Analysis

variable {R C R' C' : Type*} {d : ℕ}

noncomputable def reindexedMatrixAssignment (cols : C ≃ C')
    (f : MatrixAssignment (SolutionGroup.Generator C') d) :
    MatrixAssignment (SolutionGroup.Generator C) d :=
  f.comp (FreeGroup.map (Option.map cols))

@[simp] theorem reindexedMatrixAssignment_of (cols : C ≃ C')
    (f : MatrixAssignment (SolutionGroup.Generator C') d) (c : Option C) :
    reindexedMatrixAssignment cols f (FreeGroup.of c) = f (FreeGroup.of (c.map cols)) := by
  simp [reindexedMatrixAssignment]

theorem isApprox_reindexedMatrixAssignment (S : SparseSystem R C)
    (rows : R ≃ R') (cols : C ≃ C') {δ : ℝ}
    (f : MatrixAssignment (SolutionGroup.Generator C') d)
    (hf : IsApproxRepresentation (SolutionGroup.relators (S.reindex rows cols)) δ f) :
    IsApproxRepresentation (SolutionGroup.relators S) δ (reindexedMatrixAssignment cols f) := by
  rintro _ ⟨tag, rfl⟩
  cases tag with
  | centralSquare =>
    simpa [← assignment_word_eval, SolutionGroup.relatorWord, SolutionGroup.centralWord]
      using hf _ ⟨.centralSquare, rfl⟩
  | variableSquare c =>
    simpa [← assignment_word_eval, SolutionGroup.relatorWord, SolutionGroup.variableWord]
      using hf _ ⟨.variableSquare (cols c), rfl⟩
  | centralCommutes c =>
    simpa [← assignment_word_eval, SolutionGroup.relatorWord, SolutionGroup.variableWord,
      SolutionGroup.centralWord]
      using hf _ ⟨.centralCommutes (cols c), rfl⟩
  | rowCommutes r i j =>
    simpa [← assignment_word_eval, SolutionGroup.relatorWord, SolutionGroup.variableWord,
      SparseSystem.reindex_column]
      using hf _ ⟨.rowCommutes (rows r) i j, rfl⟩
  | rowEquation r =>
    have h := hf _ ⟨.rowEquation (rows r), rfl⟩
    by_cases hr : S.rhs r = 1 <;>
      simpa [← assignment_word_eval, SolutionGroup.relatorWord, SolutionGroup.rowWord,
        SolutionGroup.rhsWord, SolutionGroup.variableWord, SolutionGroup.centralWord,
        Word.equation, SparseSystem.reindex_column, SparseSystem.reindex_rhs, hr] using h

end ThomGame.Analysis

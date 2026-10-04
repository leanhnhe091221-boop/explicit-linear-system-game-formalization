module

public import ThomGame.Finite.SparseSystem

/-! Reindexing a sparse system preserves its equations and classical solutions. -/

@[expose] public section
namespace ThomGame.SparseSystem

variable {R C R' C' : Type*} (S : ThomGame.SparseSystem R C)

def reindex (rows : R ≃ R') (cols : C ≃ C') : ThomGame.SparseSystem R' C' where
  column r i := cols (S.column (rows.symm r) i)
  column_injective r := cols.injective.comp (S.column_injective (rows.symm r))
  rhs r := S.rhs (rows.symm r)

theorem reindex_column (rows : R ≃ R') (cols : C ≃ C') (r : R) (i : Fin 3) :
    (S.reindex rows cols).column (rows r) i = cols (S.column r i) := by
  simp [reindex]

theorem reindex_rhs (rows : R ≃ R') (cols : C ≃ C') (r : R) :
    (S.reindex rows cols).rhs (rows r) = S.rhs r := by
  simp [reindex]

theorem reindex_matrix [DecidableEq C] [DecidableEq C']
    (rows : R ≃ R') (cols : C ≃ C') (r : R) (c : C) :
    (S.reindex rows cols).matrix (rows r) (cols c) = S.matrix r c := by
  simp [matrix, reindex, cols.injective.eq_iff]

theorem reindex_satisfies_iff (rows : R ≃ R') (cols : C ≃ C') (x : C' → ZMod 2) :
    (S.reindex rows cols).Satisfies x ↔ S.Satisfies (x ∘ cols) := by
  constructor
  · intro h r
    simpa [reindex, Function.comp_def] using h (rows r)
  · intro h r
    simpa [reindex, Function.comp_def] using h (rows.symm r)

theorem reindex_no_solution (rows : R ≃ R') (cols : C ≃ C')
    (h : ¬ ∃ x, S.Satisfies x) : ¬ ∃ x, (S.reindex rows cols).Satisfies x := by
  rintro ⟨x, hx⟩
  exact h ⟨x ∘ cols, (S.reindex_satisfies_iff rows cols x).mp hx⟩

end ThomGame.SparseSystem

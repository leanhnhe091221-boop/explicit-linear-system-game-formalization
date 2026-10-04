module

public import ThomGame.Analysis.ApproxRepresentation
public import ThomGame.Analysis.UnitaryTriplePermutation
public import ThomGame.Groups.SolutionGroupRowOrdering

/-! The same free-group assignment transports between row orders with factor four. -/

@[expose] public section
namespace ThomGame.Analysis

variable {R C : Type*} {d : Nat}

theorem assignment_word_eval {α : Type*} (f : MatrixAssignment α d) (w : Word α) :
    Word.eval (fun a => f (FreeGroup.of a)) w = f (FreeGroup.mk w) := by
  simp only [Word.eval, assignment_eq_lift]

theorem solution_approx_nonneg (S : SparseSystem R C) {δ : ℝ}
    (f : MatrixAssignment (SolutionGroup.Generator C) d)
    (hf : IsApproxRepresentation (SolutionGroup.relators S) δ f) : 0 ≤ δ :=
  (unitaryLength_nonneg _).trans (hf _ ⟨.centralSquare, rfl⟩)

theorem solution_approx_commutator (S : SparseSystem R C) {δ : ℝ}
    (f : MatrixAssignment (SolutionGroup.Generator C) d)
    (hf : IsApproxRepresentation (SolutionGroup.relators S) δ f) (r : R) (i j : Fin 3) :
    unitaryLength (f (FreeGroup.of (some (S.column r i))) *
      f (FreeGroup.of (some (S.column r j))) *
      (f (FreeGroup.of (some (S.column r i))))⁻¹ *
      (f (FreeGroup.of (some (S.column r j))))⁻¹) ≤ δ := by
  have h := hf _ ⟨.rowCommutes r i j, rfl⟩
  rw [← assignment_word_eval] at h
  simpa only [SolutionGroup.relatorWord, Word.eval_commutator, SolutionGroup.variableWord,
    Word.eval_generator] using h

theorem solution_approx_row (S : SparseSystem R C) {δ : ℝ}
    (f : MatrixAssignment (SolutionGroup.Generator C) d)
    (hf : IsApproxRepresentation (SolutionGroup.relators S) δ f) (r : R) :
    unitaryDist (f (FreeGroup.mk (SolutionGroup.rowWord S r)))
      (f (FreeGroup.mk (SolutionGroup.rhsWord S r))) ≤ δ := by
  have h := hf _ ⟨.rowEquation r, rfl⟩
  rw [unitaryDist_eq_length, ← assignment_word_eval, ← assignment_word_eval]
  rw [← assignment_word_eval] at h
  simpa only [SolutionGroup.relatorWord, Word.equation, Word.eval_append,
    Word.eval_inverse] using h

theorem solution_row_permutation_error {S T : SparseSystem R C}
    (p : S.RowPermutation T) {δ : ℝ} (f : MatrixAssignment (SolutionGroup.Generator C) d)
    (hf : IsApproxRepresentation (SolutionGroup.relators S) δ f) (r : R) :
    unitaryDist (f (FreeGroup.mk (SolutionGroup.rowWord T r)))
      (f (FreeGroup.mk (SolutionGroup.rowWord S r))) ≤ 3 * δ := by
  have h := unitaryTriple_perm_bound
    (fun i => f (FreeGroup.of (some (S.column r i)))) (p.slots r) δ
    (solution_approx_nonneg S f hf) (solution_approx_commutator S f hf r)
  simpa only [← assignment_word_eval, SolutionGroup.rowWord, Word.eval_append,
    SolutionGroup.variableWord, Word.eval_generator, p.column_eq] using h

theorem solution_approx_permute {S T : SparseSystem R C}
    (p : S.RowPermutation T) {δ : ℝ} (f : MatrixAssignment (SolutionGroup.Generator C) d)
    (hf : IsApproxRepresentation (SolutionGroup.relators S) δ f) :
    IsApproxRepresentation (SolutionGroup.relators T) (4 * δ) f := by
  have hδ := solution_approx_nonneg S f hf
  have hle : δ ≤ 4 * δ := by linarith
  rintro _ ⟨tag, rfl⟩
  cases tag with
  | centralSquare => exact (hf _ ⟨.centralSquare, rfl⟩).trans hle
  | variableSquare c => exact (hf _ ⟨.variableSquare c, rfl⟩).trans hle
  | centralCommutes c => exact (hf _ ⟨.centralCommutes c, rfl⟩).trans hle
  | rowCommutes r i j =>
    have h := hf _ ⟨.rowCommutes r (p.slots r i) (p.slots r j), rfl⟩
    simpa only [SolutionGroup.relatorWord, p.column_eq] using h.trans hle
  | rowEquation r =>
    have ht := unitaryDist_triangle (f (FreeGroup.mk (SolutionGroup.rowWord T r)))
      (f (FreeGroup.mk (SolutionGroup.rowWord S r)))
      (f (FreeGroup.mk (SolutionGroup.rhsWord S r)))
    have hp := solution_row_permutation_error p f hf r
    have hr := solution_approx_row S f hf r
    have hh : unitaryDist (f (FreeGroup.mk (SolutionGroup.rowWord T r)))
        (f (FreeGroup.mk (SolutionGroup.rhsWord S r))) ≤ 4 * δ := by linarith
    rw [← assignment_word_eval]
    simpa only [unitaryDist_eq_length, ← assignment_word_eval, SolutionGroup.relatorWord,
      Word.equation, Word.eval_append, Word.eval_inverse, SolutionGroup.rhsWord, p.rhs_eq]
      using hh

theorem solution_approximatelyTrivial_permute {S T : SparseSystem R C}
    (p : S.RowPermutation T) (w : FreeGroup (SolutionGroup.Generator C))
    (h : ApproximatelyTrivial (SolutionGroup.relators S) w) :
    ApproximatelyTrivial (SolutionGroup.relators T) w := by
  intro η hη
  obtain ⟨δ, hδ, hh⟩ := h η hη
  refine ⟨δ / 4, by positivity, ?_⟩
  intro d hd f hf
  apply hh d hd f
  have hp := solution_approx_permute p.symm f hf
  convert hp using 1
  ring

end ThomGame.Analysis

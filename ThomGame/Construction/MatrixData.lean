module

public import ThomGame.Construction.Numbering
public import Mathlib.Data.Matrix.Basic

/-!
# The explicitly numbered matrix and right-hand side

The entry theorem below gives the three column numbers for every row, in the
same formulas as the supplied generator. Sorting the three numbers for a
Matrix Market file does not change the matrix entry predicate.
-/

@[expose] public section
namespace ThomGame.Construction

/-- The actual binary matrix, with the paper's exact dimensions. -/
def A : Matrix (Fin 1417152) (Fin 1889684) (ZMod 2) := numberedSystem.matrix

/-- The actual binary right-hand side. -/
def b : Fin 1417152 → ZMod 2 := numberedSystem.rhs

theorem next_position_val (r : WheelIndex) (j : Fin (wheelFamily.size r)) :
    (finRotate (wheelFamily.size r) j).val = (j.val + 1) % wheelFamily.size r := by
  rw [finRotate_apply]
  change (j.val + 1 % wheelFamily.size r) % wheelFamily.size r = _
  have hs := wheelFamily.size_ge_two r
  rw [Nat.mod_eq_of_lt (show 1 < wheelFamily.size r by omega)]

/-- The three source triples at one word position, before sorting for output. -/
def sourceTriples (r : WheelIndex) (j : Fin (wheelFamily.size r)) : Fin 3 → Fin 3 → Nat :=
  let q := offset r + j.val
  let next := offset r + (j.val + 1) % wheelFamily.size r
  ![![ordinaryNumber (wheelFamily.letter r j), 148 + 4 * q + 1, 148 + 4 * q + 2],
    ![148 + 4 * q + 2, 148 + 4 * q + 3, 148 + 4 * next + 1],
    ![148 + 4 * q + 3, 148 + 4 * q + 4, 148 + 4 * next + 4]]

theorem sourceTriples_column (r : WheelIndex) (j : Fin (wheelFamily.size r))
    (k i : Fin 3) :
    colNumber (system.column ⟨r, j, k⟩ i) = sourceTriples r j k i := by
  fin_cases k <;> fin_cases i <;>
    simp [system, Wheel.Family.system, Wheel.Family.columns, Wheel.Family.aux,
      colNumber, sourceTriples, Nat.add_assoc]
  all_goals simpa only [finRotate_apply] using next_position_val r j

theorem sourceTriples_injective (r : WheelIndex) (j : Fin (wheelFamily.size r)) (k : Fin 3) :
    Function.Injective (sourceTriples r j k) := by
  intro a b h
  apply system.column_injective ⟨r, j, k⟩
  apply colNumber_injective
  simpa only [sourceTriples_column] using h

theorem numbered_column_formula (r : WheelIndex) (j : Fin (wheelFamily.size r))
    (k i : Fin 3) :
    (numberedSystem.column (rowEquiv ⟨r, j, k⟩) i).val + 1 = sourceTriples r j k i :=
  (numbered_column ⟨r, j, k⟩ i).trans (sourceTriples_column r j k i)

/-- Exact entry-by-entry correspondence with the source triple formulas. -/
theorem A_eq_one_iff (r : WheelIndex) (j : Fin (wheelFamily.size r)) (k : Fin 3)
    (c : Fin 1889684) :
    A (rowEquiv ⟨r, j, k⟩) c = 1 ↔ ∃ i : Fin 3, sourceTriples r j k i = c.val + 1 := by
  rw [A, numberedSystem.matrix_eq_one_iff]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [← numbered_column_formula, hi]
  · rintro ⟨i, hi⟩
    refine ⟨i, Fin.ext ?_⟩
    have hc := (numbered_column_formula r j k i).trans hi
    omega

theorem A_zero_or_one (r : Fin 1417152) (c : Fin 1889684) :
    A r c = 0 ∨ A r c = 1 := numberedSystem.matrix_zero_or_one r c

theorem A_nonzero_count :
    Fintype.card {p : Fin 1417152 × Fin 1889684 // A p.1 p.2 ≠ 0} = 4251456 :=
  numberedSystem.nonzero_card_fin

theorem b_odd : numberedSystem.rhs (rowEquiv oddRow) = 1 := by
  rw [numbered_rhs]
  rfl

/-- Exactly one one-based right-hand-side coordinate is 1. -/
theorem b_formula (r : Fin 1417152) : b r = if r.val + 1 = 1417141 then 1 else 0 := by
  obtain ⟨s, rfl⟩ := rowEquiv.surjective r
  change numberedSystem.rhs (rowEquiv s) = _
  rw [numbered_rhs, rowEquiv_number]
  by_cases hs : s = oddRow
  · subst s
    rw [odd_row_number]
    rfl
  · have hn : rowNumber s ≠ 1417141 := by
      intro h
      exact hs (rowNumber_injective (h.trans odd_row_number.symm))
    rw [ite_eq_right hn]
    by_contra h
    exact hs ((rhs_ne_zero_iff s).mp h)

/-- There is no solution of the concrete numbered matrix equation. -/
theorem A_b_no_solution : ¬ ∃ x, IsLinearSolution A b x := by
  rintro ⟨x, hx⟩
  exact numbered_no_solution ⟨x, (numberedSystem.satisfies_iff_linear_solution x).mpr hx⟩

end ThomGame.Construction

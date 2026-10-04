module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.ZMod.Basic

/-!
# A finite linear-system obstruction

The sum of the rows of the paper's binary linear system is the inconsistent
equation `0 = 1`. This file proves the general algebraic implication. It does
not yet assert that the concrete generated matrix satisfies the hypotheses.
-/

@[expose] public section

namespace ThomGame

open scoped BigOperators

/-- A solution of a finite linear system over a semiring. -/
def IsLinearSolution {R Row Col : Type*} [Semiring R] [Fintype Col]
    (A : Row → Col → R) (b : Row → R) (x : Col → R) : Prop :=
  ∀ r, ∑ c, A r c * x c = b r

/-- Summing all equations rules out a solution when the column sums vanish
but the sum of the right-hand side does not. -/
theorem no_solution_of_column_sums_zero
    {R Row Col : Type*} [Semiring R] [Fintype Row] [Fintype Col]
    (A : Row → Col → R) (b : Row → R)
    (hcol : ∀ c, ∑ r, A r c = 0)
    (hrhs : ∑ r, b r ≠ 0) :
    ¬ ∃ x, IsLinearSolution A b x := by
  rintro ⟨x, hx⟩
  apply hrhs
  calc
    ∑ r, b r = ∑ r, ∑ c, A r c * x c :=
      Finset.sum_congr rfl fun r _ ↦ (hx r).symm
    _ = ∑ c, ∑ r, A r c * x c := Finset.sum_comm
    _ = ∑ c, (∑ r, A r c) * x c := by
      simp_rw [Finset.sum_mul]
    _ = 0 := by simp [hcol]

/-- Binary specialization, with the odd total right-hand side written as `1`. -/
theorem binary_no_solution_of_column_sums_zero
    {Row Col : Type*} [Fintype Row] [Fintype Col]
    (A : Row → Col → ZMod 2) (b : Row → ZMod 2)
    (hcol : ∀ c, ∑ r, A r c = 0)
    (hrhs : ∑ r, b r = 1) :
    ¬ ∃ x, IsLinearSolution A b x :=
  no_solution_of_column_sums_zero A b hcol (by rw [hrhs]; exact one_ne_zero)

end ThomGame

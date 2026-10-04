module

public import ThomGame.Finite.SparseSystem
public import ThomGame.Finite.WheelParity
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Tactic.FinCases

/-!
# Sparse systems built from wagon wheels

Rows are indexed by a wheel, a position in its cyclic word, and one of the
three equation families. Four fresh auxiliary variables are allocated at
each position. These are the exact incidences of equations (14)--(16).
-/

@[expose] public section

namespace ThomGame.Wheel

open scoped BigOperators

structure Family (R V : Type*) where
  size : R → Nat
  size_ge_two : ∀ r, 2 ≤ size r
  letter : (r : R) → Fin (size r) → V
  parity : R → ZMod 2

namespace Family

variable {R V : Type*} (F : Family R V)

instance size_neZero (r : R) : NeZero (F.size r) :=
  ⟨by have := F.size_ge_two r; omega⟩

abbrev Row := (r : R) × (Fin (F.size r) × Fin 3)
abbrev Auxiliary := (r : R) × (Fin (F.size r) × Fin 4)
abbrev Col := V ⊕ F.Auxiliary

def aux (r : R) (j : Fin (F.size r)) (k : Fin 4) : F.Col := .inr ⟨r, j, k⟩

def columns (r : R) (j : Fin (F.size r)) : Fin 3 → Fin 3 → F.Col :=
  ![![.inl (F.letter r j), F.aux r j 0, F.aux r j 1],
    ![F.aux r j 1, F.aux r j 2, F.aux r (finRotate (F.size r) j) 0],
    ![F.aux r j 2, F.aux r j 3, F.aux r (finRotate (F.size r) j) 3]]

theorem next_ne_self (r : R) (j : Fin (F.size r)) :
    finRotate (F.size r) j ≠ j := by
  rw [finRotate_apply]
  intro h
  have hz : (1 : Fin (F.size r)) = 0 := add_left_cancel (h.trans (add_zero j).symm)
  have hv := congrArg Fin.val hz
  have hn := F.size_ge_two r
  change 1 % F.size r = 0 at hv
  rw [Nat.mod_eq_of_lt (by omega)] at hv
  exact Nat.one_ne_zero hv

theorem columns_injective (r : R) (j : Fin (F.size r)) (k : Fin 3) :
    Function.Injective (F.columns r j k) := by
  intro a b hab
  have hnext := F.next_ne_self r j
  fin_cases k <;> fin_cases a <;> fin_cases b <;>
    simp_all [columns, aux]

/-- The sparse binary system of the entire family. -/
def system : SparseSystem F.Row F.Col where
  column r := F.columns r.1 r.2.1 r.2.2
  column_injective r := F.columns_injective r.1 r.2.1 r.2.2
  rhs r := if r.2.1 = 0 ∧ r.2.2 = 0 then F.parity r.1 else 0

/-- Restricting a full-system solution to one wheel gives its three equations. -/
theorem satisfies_wheel {x : F.Col → ZMod 2} (hx : F.system.Satisfies x) (r : R) :
    Wheel.Satisfies (fun j => x (.inl (F.letter r j))) (F.parity r)
      (fun j => x (F.aux r j 0)) (fun j => x (F.aux r j 1))
      (fun j => x (F.aux r j 2)) (fun j => x (F.aux r j 3)) := by
  intro j
  have h₀ := hx ⟨r, j, 0⟩
  have h₁ := hx ⟨r, j, 1⟩
  have h₂ := hx ⟨r, j, 2⟩
  simp only [system, columns, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two] at h₀ h₁ h₂
  constructor
  · simpa [add_assoc] using h₀
  constructor
  · simpa [add_assoc] using h₁
  · simpa [add_assoc] using h₂

/-- A single odd wheel with zero ordinary-letter sum obstructs the full system. -/
theorem no_solution_of_odd_zero_sum (r : R) (hp : F.parity r = 1)
    (hletters : ∀ x : V → ZMod 2, ∑ j, x (F.letter r j) = 0) :
    ¬ ∃ x, F.system.Satisfies x := by
  rintro ⟨x, hx⟩
  have h := sum_letters_eq_parity (F.satisfies_wheel hx r)
  rw [hletters (fun v => x (.inl v)), hp] at h
  exact zero_ne_one h

theorem no_perfect_of_odd_zero_sum (r : R) (hp : F.parity r = 1)
    (hletters : ∀ x : V → ZMod 2, ∑ j, x (F.letter r j) = 0) :
    ¬ ∃ alice bob, F.system.PerfectDeterministic alice bob := by
  rw [F.system.exists_perfect_iff_exists_solution]
  exact F.no_solution_of_odd_zero_sum r hp hletters

def totalLength [Fintype R] : Nat := ∑ r, F.size r

theorem row_card [Fintype R] : Fintype.card F.Row = 3 * F.totalLength := by
  simp [Row, Fintype.card_sigma, Fintype.card_prod, totalLength, Finset.sum_mul,
    Nat.mul_comm]

theorem col_card [Fintype R] [Fintype V] :
    Fintype.card F.Col = Fintype.card V + 4 * F.totalLength := by
  simp [Col, Auxiliary, Fintype.card_sum, Fintype.card_sigma, Fintype.card_prod,
    totalLength, Finset.sum_mul, Nat.mul_comm]

end Family
end ThomGame.Wheel

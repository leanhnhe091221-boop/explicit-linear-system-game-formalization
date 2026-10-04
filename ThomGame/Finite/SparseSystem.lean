module

public import ThomGame.Finite.Classical
public import Mathlib.Data.Fintype.BigOperators

/-!
# Binary systems with three distinct variables in each row

The three slots in a row give both its sparse matrix representation and
the coordinates of Alice's answer. Incidence questions are indexed by
`Row × Fin 3`; the injectivity field ensures that these are actual distinct
row-column incidences. Numerical file indexing is a separate conversion.
-/

@[expose] public section

namespace ThomGame

open scoped BigOperators

/-- A binary linear system with exactly three distinct columns per row. -/
structure SparseSystem (Row Col : Type*) where
  column : Row → Fin 3 → Col
  column_injective : ∀ r, Function.Injective (column r)
  rhs : Row → ZMod 2

namespace SparseSystem

variable {Row Col : Type*} (S : SparseSystem Row Col)

/-- An assignment satisfies the three-variable equation in every row. -/
def Satisfies (x : Col → ZMod 2) : Prop :=
  ∀ r, ∑ i, x (S.column r i) = S.rhs r

/-- The incidence-distributed game's acceptance predicate. -/
def Accepts (r : Row) (i : Fin 3) (a : Fin 3 → ZMod 2) (b : ZMod 2) : Prop :=
  (∑ j, a j = S.rhs r) ∧ a i = b

/-- Perfect deterministic play, quantified over every incidence question. -/
def PerfectDeterministic (alice : Row → Fin 3 → ZMod 2) (bob : Col → ZMod 2) : Prop :=
  ∀ r i, S.Accepts r i (alice r) (bob (S.column r i))

/-- A solution gives a perfect deterministic strategy by restriction to rows. -/
theorem perfect_of_satisfies {x : Col → ZMod 2} (hx : S.Satisfies x) :
    S.PerfectDeterministic (fun r i ↦ x (S.column r i)) x := by
  intro r i
  exact ⟨hx r, rfl⟩

/-- In a perfect deterministic strategy, Bob's answers solve the system. -/
theorem satisfies_of_perfect {alice : Row → Fin 3 → ZMod 2} {bob : Col → ZMod 2}
    (h : S.PerfectDeterministic alice bob) : S.Satisfies bob := by
  intro r
  calc
    ∑ i, bob (S.column r i) = ∑ i, alice r i :=
      Finset.sum_congr rfl fun i _ ↦ (h r i).2.symm
    _ = S.rhs r := (h r 0).1

/-- Classical perfect play and solvability refer to the same assignment. -/
theorem exists_perfect_iff_exists_solution :
    (∃ alice bob, S.PerfectDeterministic alice bob) ↔ ∃ x, S.Satisfies x := by
  constructor
  · rintro ⟨alice, bob, h⟩
    exact ⟨bob, S.satisfies_of_perfect h⟩
  · rintro ⟨x, hx⟩
    exact ⟨(fun r i ↦ x (S.column r i)), x, S.perfect_of_satisfies hx⟩

/-- The matrix represented by the three column slots. -/
def matrix [DecidableEq Col] (r : Row) (c : Col) : ZMod 2 :=
  ∑ i, if S.column r i = c then 1 else 0

theorem matrix_at_column [DecidableEq Col] (r : Row) (i : Fin 3) :
    S.matrix r (S.column r i) = 1 := by
  simp [matrix, (S.column_injective r).eq_iff]

theorem matrix_ne_zero_iff [DecidableEq Col] (r : Row) (c : Col) :
    S.matrix r c ≠ 0 ↔ ∃ i, S.column r i = c := by
  constructor
  · intro h
    by_contra hn
    have hzero : S.matrix r c = 0 := by
      simp only [not_exists] at hn
      simp [matrix, hn]
    exact h hzero
  · rintro ⟨i, rfl⟩
    rw [S.matrix_at_column]
    exact one_ne_zero

theorem matrix_eq_one_iff [DecidableEq Col] (r : Row) (c : Col) :
    S.matrix r c = 1 ↔ ∃ i, S.column r i = c := by
  constructor
  · intro h
    apply (S.matrix_ne_zero_iff r c).mp
    rw [h]
    exact one_ne_zero
  · rintro ⟨i, rfl⟩
    exact S.matrix_at_column r i

theorem matrix_zero_or_one [DecidableEq Col] (r : Row) (c : Col) :
    S.matrix r c = 0 ∨ S.matrix r c = 1 := by
  by_cases h : S.matrix r c = 0
  · exact Or.inl h
  · exact Or.inr ((S.matrix_eq_one_iff r c).mpr ((S.matrix_ne_zero_iff r c).mp h))

/-- Exactly one nonzero matrix entry for every row slot. -/
theorem nonzero_card [Fintype Row] [Fintype Col] [DecidableEq Col] :
    Fintype.card {p : Row × Col // S.matrix p.1 p.2 ≠ 0} = 3 * Fintype.card Row := by
  classical
  let f : Row × Fin 3 → {p : Row × Col // S.matrix p.1 p.2 ≠ 0} :=
    fun p => ⟨(p.1, S.column p.1 p.2), (S.matrix_ne_zero_iff _ _).mpr ⟨p.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨r, i⟩ ⟨s, j⟩ h
      have hrs : r = s := congrArg (fun p => p.val.1) h
      subst s
      have hij : S.column r i = S.column r j := congrArg (fun p => p.val.2) h
      exact Prod.ext rfl (S.column_injective r hij)
    · rintro ⟨⟨r, c⟩, h⟩
      obtain ⟨i, rfl⟩ := (S.matrix_ne_zero_iff r c).mp h
      exact ⟨(r, i), rfl⟩
  rw [← Fintype.card_congr (Equiv.ofBijective f hf)]
  simp [Fintype.card_prod, Nat.mul_comm]

theorem nonzero_card_fin {m n : Nat} (T : SparseSystem (Fin m) (Fin n)) :
    Fintype.card {p : Fin m × Fin n // T.matrix p.1 p.2 ≠ 0} = 3 * m := by
  rw [T.nonzero_card, Fintype.card_fin]

/-- Sparse row evaluation agrees with ordinary matrix multiplication. -/
theorem matrix_row_sum [Fintype Col] [DecidableEq Col]
    (r : Row) (x : Col → ZMod 2) :
    ∑ c, S.matrix r c * x c = ∑ i, x (S.column r i) := by
  simp only [matrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

/-- The sparse and matrix notions of solution coincide. -/
theorem satisfies_iff_linear_solution [Fintype Col] [DecidableEq Col]
    (x : Col → ZMod 2) :
    S.Satisfies x ↔ IsLinearSolution S.matrix S.rhs x := by
  simp only [Satisfies, IsLinearSolution, S.matrix_row_sum]

end SparseSystem

end ThomGame

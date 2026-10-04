module

public import ThomGame.Finite.Classical
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Parity of a wagon wheel

These are equations (14)--(16) of the paper, before flattening the indices.
The sum of the three families cancels all auxiliary variables in characteristic
two. In particular, the final odd wheel, whose word is `u v u v`, is already
classically inconsistent. No quantum conclusion follows from this alone.
-/

@[expose] public section

namespace ThomGame.Wheel

open scoped BigOperators

/-- The three families of equations for one nonempty wheel. -/
def Satisfies {n : ℕ} [NeZero n] (s : Fin n → ZMod 2) (p : ZMod 2)
    (a b c d : Fin n → ZMod 2) : Prop :=
  ∀ j,
    (s j + a j + b j = if j = 0 then p else 0) ∧
    (b j + c j + a (finRotate n j) = 0) ∧
    (c j + d j + d (finRotate n j) = 0)

/-- Every solution of a wheel has the prescribed parity on its ordinary letters. -/
theorem sum_letters_eq_parity {n : ℕ} [NeZero n]
    {s a b c d : Fin n → ZMod 2} {p : ZMod 2}
    (h : Satisfies s p a b c d) : ∑ j, s j = p := by
  have h₁ := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ ↦ (h j).1)
  have h₂ := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ ↦ (h j).2.1)
  have h₃ := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ ↦ (h j).2.2)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Finset.sum_const_zero] at h₁ h₂ h₃
  rw [Equiv.sum_comp (finRotate n) a] at h₂
  rw [Equiv.sum_comp (finRotate n) d] at h₃
  have htwo : (2 : ZMod 2) = 0 := rfl
  linear_combination (norm := (ring_nf; simp [htwo])) h₁ + h₂ + h₃

/-- An odd wheel cannot be solved if its ordinary letter values sum to zero. -/
theorem no_solution_of_zero_sum {n : ℕ} [NeZero n]
    (s : Fin n → ZMod 2) (hs : ∑ j, s j = 0) :
    ¬ ∃ a b c d, Satisfies s 1 a b c d := by
  rintro ⟨a, b, c, d, h⟩
  have hp := sum_letters_eq_parity h
  rw [hs] at hp
  exact zero_ne_one hp

/-- The four ordinary letters of the paper's final wheel, after evaluation. -/
def doubledPair (u v : ZMod 2) : Fin 4 → ZMod 2 := ![u, v, u, v]

theorem sum_doubledPair (u v : ZMod 2) : ∑ j, doubledPair u v j = 0 := by
  simp [doubledPair, Fin.sum_univ_succ]
  ring_nf
  have htwo : (2 : ZMod 2) = 0 := rfl
  simp [htwo]

/-- The ordinary variables may be assigned arbitrarily; the odd final wheel
still has no assignment of its sixteen auxiliary variables. -/
theorem no_solution_odd_doubledPair (u v : ZMod 2) :
    ¬ ∃ a b c d, Satisfies (doubledPair u v) 1 a b c d :=
  no_solution_of_zero_sum (doubledPair u v) (sum_doubledPair u v)

end ThomGame.Wheel

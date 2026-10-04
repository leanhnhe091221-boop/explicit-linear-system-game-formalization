module

public import Mathlib.Data.Fintype.BigOperators

/-! # Decomposing a finite sum at two possibly equal distinguished points -/

@[expose] public section
namespace ThomGame.Finite

open scoped Classical BigOperators

theorem sum_except_two {A M : Type*} [Fintype A] [AddCommMonoid M]
    (f : A → M) (a b : A) :
    (∑ x : {x : A // x ≠ a ∧ x ≠ b}, f x.val) + f a + (if a = b then 0 else f b) =
      ∑ x : A, f x := by
  have he : (∑ x : {x : A // x ≠ a ∧ x ≠ b}, f x.val) =
      ∑ x ∈ ({a, b} : Finset A)ᶜ, f x :=
    (Finset.sum_subtype _ (by intro x; simp) f).symm
  rw [he]
  have h := Finset.sum_compl_add_sum ({a, b} : Finset A) f
  by_cases hab : a = b
  · subst b
    simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self a), Finset.sum_singleton,
      ite_true, add_zero] using h
  · simpa only [Finset.sum_pair hab, hab, ite_false, add_assoc] using h

theorem sum_except_two_of_eq {A M : Type*} [Fintype A] [AddCommMonoid M]
    (f : A → M) (a b : A) (hab : a = b) :
    (∑ x : {x : A // x ≠ a ∧ x ≠ b}, f x.val) + f a = ∑ x : A, f x := by
  have h := sum_except_two f a b
  rw [ite_eq_left hab, add_zero] at h
  exact h

theorem sum_except_two_of_ne {A M : Type*} [Fintype A] [AddCommMonoid M]
    (f : A → M) (a b : A) (hab : a ≠ b) :
    (∑ x : {x : A // x ≠ a ∧ x ≠ b}, f x.val) + f a + f b = ∑ x : A, f x := by
  have h := sum_except_two f a b
  rw [ite_eq_right hab] at h
  exact h

end ThomGame.Finite

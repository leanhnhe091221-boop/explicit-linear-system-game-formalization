module

public import ThomGame.Pictures.OrbitEnumeration

/-! # Indexed orbit enumeration commutes with a permutation equivalence -/

@[expose] public section
namespace ThomGame.Pictures.OrbitEnumeration

variable {A B : Type*} [Finite A] [Finite B]
  (f : Equiv.Perm A) (g : Equiv.Perm B) (e : A ≃ B)
  (he : ∀ a, g (e a) = e (f a))

include he in
omit [Finite A] [Finite B] in
theorem pow_congr (k : Nat) (a : A) : (g ^ k) (e a) = e ((f ^ k) a) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, he, pow_succ', Equiv.Perm.mul_apply]

include he in
omit [Finite A] [Finite B] in
theorem length_congr (a : A) : length f a = length g (e a) := by
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro k
  change (f ^ k) a = a ↔ (g ^ k) (e a) = e a
  rw [pow_congr f g e he]
  exact e.injective.eq_iff.symm

omit [Finite A] [Finite B] in
theorem dart_congr (a : A) (i : Fin (length f a)) :
    dart g (e a) (finCongr (length_congr f g e he a) i) = e (dart f a i) :=
  pow_congr f g e he i.val a

end ThomGame.Pictures.OrbitEnumeration

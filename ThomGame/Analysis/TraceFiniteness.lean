module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Group.Hom.Basic

/-!
# Faithful traces exclude proper isometries

For a star ring, cyclicity and faithfulness of an additive trace suffice
to prove that every element with `star a * a = 1` also satisfies
`a * star a = 1`. Apply faithfulness to the complementary projection.
-/

@[expose] public section
namespace ThomGame.Analysis

variable {A B : Type*} [Ring A] [StarRing A] [AddCommGroup B]

theorem mul_star_eq_one_of_faithful_trace (τ : A →+ B)
    (hcyclic : ∀ a b, τ (a * b) = τ (b * a))
    (hfaithful : ∀ a, τ (star a * a) = 0 → a = 0)
    (a : A) (ha : star a * a = 1) : a * star a = 1 := by
  let p := 1 - a * star a
  have hpstar : star p = p := by simp only [p, star_sub, star_one, star_mul, star_star]
  have hprod : (a * star a) * (a * star a) = a * star a := by
    calc
      (a * star a) * (a * star a) = a * (star a * a) * star a := by simp only [mul_assoc]
      _ = a * star a := by rw [ha, mul_one]
  have hpsq : p * p = p := by
    simp only [p, mul_sub, sub_mul, mul_one, one_mul, hprod, sub_self, sub_zero]
  have hpzero : p = 0 := by
    apply hfaithful
    rw [hpstar, hpsq]
    simp only [p, map_sub, hcyclic a (star a), ha, sub_self]
  exact (sub_eq_zero.mp hpzero).symm

end ThomGame.Analysis

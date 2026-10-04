module

public import ThomGame.Pictures.ComponentSums
public import ThomGame.Pictures.ComponentEuler

/-! # Component quotients and Euler counts under transport and disjoint union -/

@[expose] public section
namespace ThomGame.Pictures.RibbonConnectivity

open Equiv FiniteReturn

variable {A B : Type*} (p f : Perm A) (q g : Perm B)

def componentCongrEquiv (e : A ≃ B)
    (hp : ∀ x, q (e x) = e (p x)) (hf : ∀ x, g (e x) = e (f x)) :
    Component p f ≃ Component q g :=
  Quotient.congr e (connected_congr p f q g e hp hf)

def sumComponentEquiv : Component (Equiv.sumCongr p q) (Equiv.sumCongr f g) ≃
    Component p f ⊕ Component q g where
  toFun := Quotient.lift (Sum.elim (fun a => .inl (component p f a))
    (fun b => .inr (component q g b))) (by
      rintro (a | a) (b | b) h
      · exact congrArg Sum.inl ((component_eq_iff p f a b).mpr ((connected_sum_inl p f q g a b).mp h))
      · exact (not_connected_sum p f q g a b h).elim
      · exact (not_connected_sum p f q g b a h.symm).elim
      · exact congrArg Sum.inr ((component_eq_iff q g a b).mpr ((connected_sum_inr p f q g a b).mp h)))
  invFun := Sum.elim
    (Quotient.lift (fun a => component (Equiv.sumCongr p q) (Equiv.sumCongr f g) (.inl a)) (by
      intro a b h
      exact (component_eq_iff _ _ _ _).mpr ((connected_sum_inl p f q g a b).mpr h)))
    (Quotient.lift (fun b => component (Equiv.sumCongr p q) (Equiv.sumCongr f g) (.inr b)) (by
      intro a b h
      exact (component_eq_iff _ _ _ _).mpr ((connected_sum_inr p f q g a b).mpr h)))
  left_inv c := Quotient.inductionOn c (by rintro (a | b) <;> rfl)
  right_inv c := by
    rcases c with c | c
    · exact Quotient.inductionOn c fun _ => rfl
    · exact Quotient.inductionOn c fun _ => rfl

variable [Finite A] [Finite B]

theorem component_card_sum :
    Nat.card (Component (Equiv.sumCongr p q) (Equiv.sumCongr f g)) =
      Nat.card (Component p f) + Nat.card (Component q g) := by
  rw [Nat.card_congr (sumComponentEquiv p f q g), Nat.card_sum]

theorem eulerCount_congr (e : A ≃ B)
    (hp : ∀ x, q (e x) = e (p x)) (hf : ∀ x, g (e x) = e (f x)) :
    eulerCount p f = eulerCount q g := by
  have hr : ∀ x, (g * q) (e x) = e ((f * p) x) := by
    intro x
    simp only [Perm.mul_apply, hp, hf]
  unfold eulerCount
  rw [Nat.card_congr (orbitEquiv (f * p) (g * q) e hr),
    Nat.card_congr (orbitEquiv p q e hp), Nat.card_congr (orbitEquiv f g e hf)]

theorem eulerDefect_congr (e : A ≃ B)
    (hp : ∀ x, q (e x) = e (p x)) (hf : ∀ x, g (e x) = e (f x)) :
    eulerDefect p f = eulerDefect q g := by
  unfold eulerDefect
  rw [eulerCount_congr p f q g e hp hf, Nat.card_congr (componentCongrEquiv p f q g e hp hf)]

theorem eulerCount_sum :
    eulerCount (Equiv.sumCongr p q) (Equiv.sumCongr f g) = eulerCount p f + eulerCount q g := by
  have hm : Equiv.sumCongr f g * Equiv.sumCongr p q = Equiv.sumCongr (f * p) (g * q) := by
    ext x
    cases x <;> rfl
  unfold eulerCount
  rw [hm, orbit_card_sum, orbit_card_sum, orbit_card_sum]
  push_cast
  omega

theorem eulerDefect_sum :
    eulerDefect (Equiv.sumCongr p q) (Equiv.sumCongr f g) = eulerDefect p f + eulerDefect q g := by
  unfold eulerDefect
  rw [eulerCount_sum, component_card_sum]
  push_cast
  omega

end ThomGame.Pictures.RibbonConnectivity

module

public import ThomGame.Pictures.BoundaryComponents

/-! # Components and marked boundary circuits of disjoint unions -/

@[expose] public section
namespace ThomGame.Pictures.RibbonConnectivity

open Equiv

variable {A B : Type*} (p f : Perm A) (q g : Perm B)

theorem connected_sum_inl (x y : A) :
    Connected (Equiv.sumCongr p q) (Equiv.sumCongr f g) (.inl x) (.inl y) ↔ Connected p f x y := by
  constructor
  · intro h
    apply h.lift (Sum.elim id (fun _ => x)) ⟨Connected.refl, Connected.symm, Connected.trans⟩
    · rintro (a | b)
      · exact Connected.edge a
      · exact Connected.refl x
    · rintro (a | b)
      · exact Connected.circuit a
      · exact Connected.refl x
  · exact Connected.map Sum.inl (fun _ => rfl) (fun _ => rfl)

theorem connected_sum_inr (x y : B) :
    Connected (Equiv.sumCongr p q) (Equiv.sumCongr f g) (.inr x) (.inr y) ↔ Connected q g x y := by
  constructor
  · intro h
    apply h.lift (Sum.elim (fun _ => x) id) ⟨Connected.refl, Connected.symm, Connected.trans⟩
    · rintro (a | b)
      · exact Connected.refl x
      · exact Connected.edge b
    · rintro (a | b)
      · exact Connected.refl x
      · exact Connected.circuit b
  · exact Connected.map Sum.inr (fun _ => rfl) (fun _ => rfl)

theorem not_connected_sum (x : A) (y : B) :
    ¬ Connected (Equiv.sumCongr p q) (Equiv.sumCongr f g) (.inl x) (.inr y) := by
  intro h
  have he : (true : Bool) = false := h.invariant (Sum.elim (fun _ => true) (fun _ => false))
    (by rintro (a | b) <;> rfl) (by rintro (a | b) <;> rfl)
  cases he

variable [Finite A] [Finite B]

theorem SeesComponents.sum {M : A → Prop} {N : B → Prop}
    (h : SeesComponents p f M) (k : SeesComponents q g N) :
    SeesComponents (Equiv.sumCongr p q) (Equiv.sumCongr f g) (Sum.elim M N) := by
  rintro ⟨x | x, hx⟩ ⟨y | y, hy⟩
  · exact (connected_sum_inl p f q g x y).trans
      ((h ⟨x, hx⟩ ⟨y, hy⟩).trans (FiniteReturn.sum_sameCycle_inl f g x y).symm)
  · exact iff_of_false (not_connected_sum p f q g x y) (FiniteReturn.sum_not_sameCycle f g x y)
  · exact iff_of_false (fun h => not_connected_sum p f q g y x h.symm)
      (fun h => FiniteReturn.sum_not_sameCycle f g y x h.symm)
  · exact (connected_sum_inr p f q g x y).trans
      ((k ⟨x, hx⟩ ⟨y, hy⟩).trans (FiniteReturn.sum_sameCycle_inr f g x y).symm)

end ThomGame.Pictures.RibbonConnectivity

module

public import ThomGame.Pictures.FiniteReturn

/-! # Orbit equivalences under transport and disjoint union -/

@[expose] public section
namespace ThomGame.Pictures.FiniteReturn

variable {A B : Type*} [Finite A] [Finite B]

omit [Finite A] [Finite B] in
theorem congrAdvances (f : Equiv.Perm A) (g : Equiv.Perm B) (e : A ≃ B)
    (h : ∀ a, g (e a) = e (f a)) : Advances g f e.toEmbedding :=
  fun a => Or.inl (h a).symm

theorem sameCycle_congr (f : Equiv.Perm A) (g : Equiv.Perm B) (e : A ≃ B)
    (h : ∀ a, g (e a) = e (f a)) (a b : A) :
    f.SameCycle a b ↔ g.SameCycle (e a) (e b) :=
  (congrAdvances f g e h).sameCycle_iff a b

noncomputable def orbitEquiv (f : Equiv.Perm A) (g : Equiv.Perm B) (e : A ≃ B)
    (h : ∀ a, g (e a) = e (f a)) : Orbit f ≃ Orbit g :=
  Equiv.ofBijective (congrAdvances f g e h).orbitMap
    ⟨(congrAdvances f g e h).orbitMap_injective,
      (congrAdvances f g e h).orbitMap_surjective_iff.mpr (fun b =>
        ⟨e.symm b, by simpa using (Equiv.Perm.SameCycle.refl g b)⟩)⟩

theorem orbitEquiv_orbit (f : Equiv.Perm A) (g : Equiv.Perm B) (e : A ≃ B)
    (h : ∀ a, g (e a) = e (f a)) (a : A) :
    orbitEquiv f g e h (orbit f a) = orbit g (e a) := rfl

omit [Finite A] [Finite B] in
theorem sum_pow (f : Equiv.Perm A) (g : Equiv.Perm B) (n : Nat) (x : A ⊕ B) :
    (Equiv.sumCongr f g ^ n) x = Sum.map (f ^ n) (g ^ n) x := by
  induction n with
  | zero => cases x <;> rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    cases x <;> simp [pow_succ']

theorem sum_sameCycle_inl (f : Equiv.Perm A) (g : Equiv.Perm B) (a b : A) :
    Equiv.Perm.SameCycle (Equiv.sumCongr f g) (.inl a) (.inl b) ↔ f.SameCycle a b := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [sum_pow] at hn
    exact ⟨(n : Int), by simpa using (Sum.inl.inj hn)⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n : Int), by simp [sum_pow, hn]⟩

theorem sum_sameCycle_inr (f : Equiv.Perm A) (g : Equiv.Perm B) (a b : B) :
    Equiv.Perm.SameCycle (Equiv.sumCongr f g) (.inr a) (.inr b) ↔ g.SameCycle a b := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [sum_pow] at hn
    exact ⟨(n : Int), by simpa using (Sum.inr.inj hn)⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n : Int), by simp [sum_pow, hn]⟩

theorem sum_not_sameCycle (f : Equiv.Perm A) (g : Equiv.Perm B) (a : A) (b : B) :
    ¬ Equiv.Perm.SameCycle (Equiv.sumCongr f g) (.inl a) (.inr b) := by
  intro h
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [sum_pow] at hn
  cases hn

def sumOrbitEquiv (f : Equiv.Perm A) (g : Equiv.Perm B) :
    Orbit (Equiv.sumCongr f g) ≃ Orbit f ⊕ Orbit g where
  toFun := Quotient.lift (Sum.elim (fun a => .inl (orbit f a))
    (fun b => .inr (orbit g b))) (by
      rintro (a | a) (b | b) h
      · exact congrArg Sum.inl ((orbit_eq_iff f a b).mpr ((sum_sameCycle_inl f g a b).mp h))
      · exact (sum_not_sameCycle f g a b h).elim
      · exact (sum_not_sameCycle f g b a h.symm).elim
      · exact congrArg Sum.inr ((orbit_eq_iff g a b).mpr ((sum_sameCycle_inr f g a b).mp h)))
  invFun := Sum.elim
    (Quotient.lift (fun a => orbit (Equiv.sumCongr f g) (.inl a)) (by
      intro a b h
      exact (orbit_eq_iff _ _ _).mpr ((sum_sameCycle_inl f g a b).mpr h)))
    (Quotient.lift (fun b => orbit (Equiv.sumCongr f g) (.inr b)) (by
      intro a b h
      exact (orbit_eq_iff _ _ _).mpr ((sum_sameCycle_inr f g a b).mpr h)))
  left_inv c := Quotient.inductionOn c (by rintro (a | b) <;> rfl)
  right_inv c := by
    rcases c with c | c
    · exact Quotient.inductionOn c fun _ => rfl
    · exact Quotient.inductionOn c fun _ => rfl

theorem orbit_card_sum (f : Equiv.Perm A) (g : Equiv.Perm B) :
    Nat.card (Orbit (Equiv.sumCongr f g)) = Nat.card (Orbit f) + Nat.card (Orbit g) := by
  rw [Nat.card_congr (sumOrbitEquiv f g), Nat.card_sum]

end ThomGame.Pictures.FiniteReturn

module

public import ThomGame.Pictures.ReturnPaths

/-! # Explicit one/two-step returns and orbit preservation -/

@[expose] public section
namespace ThomGame.Pictures.MarkedReturn

open scoped Classical

variable {A : Type*} [Finite A] (f : Equiv.Perm A) (p : A → Prop)

theorem perm_val_of_step (x : Subtype p) (hx : p (f x.val)) :
    (perm f p x).val = f x.val :=
  (eq_perm_of_hit f p x hx (.direct _)).symm

theorem perm_val_of_two_steps (x : Subtype p) (hx : ¬ p (f x.val))
    (hxx : p (f (f x.val))) : (perm f p x).val = f (f x.val) :=
  (eq_perm_of_hit f p x hxx (.skip _ hx (.direct _))).symm

theorem orbitMap_surjective_of_hits
    (h : ∀ x, ∃ y : Subtype p, f.SameCycle x y.val) : Function.Surjective (orbitMap f p) := by
  intro c
  refine Quotient.inductionOn c fun x => ?_
  obtain ⟨y, hy⟩ := h x
  exact ⟨FiniteReturn.orbit (perm f p) y,
    (FiniteReturn.orbit_eq_iff f y.val x).mpr hy.symm⟩

noncomputable def orbitEquivOfHits
    (h : ∀ x, ∃ y : Subtype p, f.SameCycle x y.val) :
    FiniteReturn.Orbit (perm f p) ≃ FiniteReturn.Orbit f :=
  Equiv.ofBijective (orbitMap f p) ⟨orbitMap_injective f p, orbitMap_surjective_of_hits f p h⟩

theorem pair_return_val (a b : A)
    (ha : f a ≠ a ∧ f a ≠ b) (hb : f b ≠ a ∧ f b ≠ b)
    (x : {x : A // x ≠ a ∧ x ≠ b}) :
    (perm f (fun x => x ≠ a ∧ x ≠ b) x).val =
      if f x.val = a then f a else if f x.val = b then f b else f x.val := by
  classical
  by_cases hxa : f x.val = a
  · rw [ite_eq_left hxa, perm_val_of_two_steps]
    · rw [hxa]
    · rw [hxa]
      exact fun h => h.1 rfl
    · rwa [hxa]
  · by_cases hxb : f x.val = b
    · rw [ite_eq_right hxa, ite_eq_left hxb, perm_val_of_two_steps]
      · rw [hxb]
      · rw [hxb]
        exact fun h => h.2 rfl
      · rwa [hxb]
    · rw [ite_eq_right hxa, ite_eq_right hxb]
      exact perm_val_of_step f _ x ⟨hxa, hxb⟩

omit [Finite A] in
theorem pair_orbits_hit (a b : A)
    (ha : f a ≠ a ∧ f a ≠ b) (hb : f b ≠ a ∧ f b ≠ b) :
    ∀ x, ∃ y : {x : A // x ≠ a ∧ x ≠ b}, f.SameCycle x y.val := by
  intro x
  by_cases hxa : x = a
  · subst x
    exact ⟨⟨f a, ha⟩, Equiv.Perm.SameCycle.rfl.apply_right⟩
  · by_cases hxb : x = b
    · subst x
      exact ⟨⟨f b, hb⟩, Equiv.Perm.SameCycle.rfl.apply_right⟩
    · exact ⟨⟨x, hxa, hxb⟩, Equiv.Perm.SameCycle.rfl⟩

end ThomGame.Pictures.MarkedReturn

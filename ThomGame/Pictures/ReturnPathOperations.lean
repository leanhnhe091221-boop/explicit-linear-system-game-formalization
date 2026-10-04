module

public import ThomGame.Pictures.ReturnPaths

/-! # Concatenation and endpoint changes of genuine return paths -/

@[expose] public section
namespace ThomGame.Pictures.MarkedReturn

variable {A B : Type*}

namespace Hit

variable {f : A → A} {p q : A → Prop} {x y z : A}

theorem weaken (h : Hit f p x y) (hpq : ∀ a, q a → p a) : Hit f q x y := by
  induction h with
  | direct x => exact Hit.direct _
  | skip x hx tail ih => exact Hit.skip _ (fun hq => hx (hpq _ hq)) ih

theorem append (h : Hit f p x y) (hy : ¬ p y) (h' : Hit f p y z) : Hit f p x z := by
  induction h with
  | direct x => exact Hit.skip _ hy h'
  | skip x hx tail ih => exact Hit.skip _ hx (ih hy h')

theorem lift_steps {g : B → B} {q : B → Prop} {x y : B} (e : B → A)
    (hs : ∀ b, Hit f p (e b) (e (g b))) (hm : ∀ b, p (e b) ↔ q b)
    (h : Hit g q x y) : Hit f p (e x) (e y) := by
  induction h with
  | direct x => exact hs x
  | skip x hx tail ih => exact (hs x).append (fun hp => hx ((hm _).mp hp)) ih

/-- Changing targets only at marked points changes the endpoint of a
return path; every unmarked interior step remains the same. -/
theorem twist_targets (s : A → A) (hs : ∀ a, ¬ p a → s a = a)
    (h : Hit f p x y) : Hit (s ∘ f) p x (s y) := by
  induction h with
  | direct x => exact Hit.direct _
  | skip x hx tail ih =>
    have he : (s ∘ f) x = f x := hs _ hx
    apply Hit.skip x
    · rwa [he]
    · rwa [he]

end Hit

theorem perm_preserved_of_paths [Finite A] [Finite B]
    (f : Equiv.Perm A) (p : A → Prop) (g : Equiv.Perm B) (q : B → Prop) (e : B → A)
    (hs : ∀ b, Hit f p (e b) (e (g b))) (hm : ∀ b, p (e b) ↔ q b) (x : Subtype q) :
    e (perm g q x).val = (perm f p ⟨e x.val, (hm x.val).mpr x.property⟩).val :=
  eq_perm_of_hit f p _ ((hm _).mpr (perm g q x).property)
    ((hit_perm g q x).lift_steps e hs hm)

end ThomGame.Pictures.MarkedReturn

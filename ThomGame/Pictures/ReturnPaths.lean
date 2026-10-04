module

public import ThomGame.Pictures.MarkedReturn

/-!
# First-return paths and deletion of unmarked intermediate points

A return path follows every step and may pass only through unmarked
intermediate points. Such paths have a unique marked endpoint. Expanding
one/two-step returns preserves these paths when all marked points survive;
therefore it preserves their exact successor, not merely their orbit.
-/

@[expose] public section
namespace ThomGame.Pictures.MarkedReturn

variable {A B : Type*}

inductive Hit (f : A → A) (p : A → Prop) : A → A → Prop
  | direct (x : A) : Hit f p x (f x)
  | skip (x : A) {y : A} : ¬ p (f x) → Hit f p (f x) y → Hit f p x y

namespace Hit

variable {f : A → A} {p : A → Prop} {x y z : A}

theorem unique (h : Hit f p x y) (h' : Hit f p x z) (hy : p y) (hz : p z) : y = z := by
  induction h generalizing z with
  | direct x =>
    cases h' with
    | direct => rfl
    | skip x hx _ => exact (hx hy).elim
  | skip x hx tail ih =>
    cases h' with
    | direct => exact (hx hz).elim
    | skip x _ tail' => exact ih tail' hy hz

theorem of_pow (f : Equiv.Perm A) (p : A → Prop) : ∀ n : Nat, 0 < n → ∀ x : A,
    (∀ k, 0 < k → k < n → ¬ p ((f ^ k) x)) → Hit f p x ((f ^ n) x) := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ n ih =>
    intro hn x hf
    cases n with
    | zero => simpa using (Hit.direct (f := f) (p := p) x)
    | succ n =>
      rw [pow_succ, Equiv.Perm.mul_apply]
      refine Hit.skip x (by simpa using hf 1 (by omega) (by omega)) ?_
      apply ih (by omega) (f x)
      intro k hk hkn
      rw [← Equiv.Perm.mul_apply, ← pow_succ]
      exact hf (k + 1) (by omega) (by omega)

theorem map {g : B → B} {q : B → Prop} (e : A → B)
    (he : ∀ x, g (e x) = e (f x)) (hm : ∀ x, q (e x) ↔ p x)
    (h : Hit f p x y) : Hit g q (e x) (e y) := by
  induction h with
  | direct x =>
    rw [← he]
    exact Hit.direct _
  | skip x hx tail ih =>
    have hn : ¬ q (g (e x)) := by
      rw [he]
      exact fun hq => hx ((hm _).mp hq)
    rw [← he] at ih
    exact Hit.skip _ hn ih

end Hit

variable [Finite A] (f : Equiv.Perm A) (p : A → Prop)

theorem hit_perm (x : Subtype p) : Hit f p x.val (perm f p x).val :=
  Hit.of_pow f p (time f p x) (time_pos f p x) x.val
    (fun _ hn ht => before_time_not_mem f p x hn ht)

theorem eq_perm_of_hit (x : Subtype p) {y : A} (hy : p y) (h : Hit f p x.val y) :
    y = (perm f p x).val := h.unique (hit_perm f p x) hy (perm f p x).property

theorem perm_preserved_of_commutes [Finite B] (g : Equiv.Perm B) (q : B → Prop) (e : B → A)
    (he : ∀ x, f (e x) = e (g x)) (hm : ∀ x, p (e x) ↔ q x) (x : Subtype q) :
    e (perm g q x).val = (perm f p ⟨e x.val, (hm x.val).mpr x.property⟩).val :=
  eq_perm_of_hit f p _ ((hm _).mpr (perm g q x).property)
    ((hit_perm g q x).map e he hm)

variable [Finite B] (g : Equiv.Perm B) (q : B → Prop) (e : B ↪ A)
variable (ha : FiniteReturn.Advances f g e)
variable (hm : ∀ b, p (e b) ↔ q b) (hs : ∀ a, p a → ∃ b, e b = a)

include ha hm hs

omit [Finite A] [Finite B] in
theorem expand_hit {x y : B} (h : Hit g q x y) : Hit f p (e x) (e y) := by
  have gap : ∀ x : B, (∀ b : B, e b ≠ f (e x)) → ¬ p (f (e x)) := by
    intro x hx hp
    obtain ⟨b, hb⟩ := hs _ hp
    exact hx b hb
  induction h with
  | direct x =>
    rcases ha x with he | ⟨he, hn⟩
    · rw [he]
      exact Hit.direct _
    · rw [he]
      exact Hit.skip _ (gap x hn) (Hit.direct _)
  | skip x hx tail ih =>
    have hn : ¬ p (e (g x)) := fun hp => hx ((hm _).mp hp)
    rcases ha x with he | ⟨he, hgap⟩
    · rw [he] at hn ih
      exact Hit.skip _ hn ih
    · rw [he] at hn ih
      exact Hit.skip _ (gap x hgap) (Hit.skip _ hn ih)

/-- Deleting only unmarked intermediate points preserves the next marked
point, including its position within a circuit. -/
theorem perm_preserved (x : Subtype q) :
    e (perm g q x).val = (perm f p ⟨e x.val, (hm x.val).mpr x.property⟩).val :=
  eq_perm_of_hit f p _ ((hm _).mpr (perm g q x).property)
    (expand_hit f p g q e ha hm hs (hit_perm g q x))

end ThomGame.Pictures.MarkedReturn

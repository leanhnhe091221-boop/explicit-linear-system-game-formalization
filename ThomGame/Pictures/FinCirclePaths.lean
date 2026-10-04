module

public import ThomGame.Pictures.ReturnPathOperations
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Paths in an explicitly numbered finite circle

An increasing injection sends cyclic successors to genuine first returns
through its image. The skipped positions are visited one by one; no
geometric order-preservation assertion is assumed.
-/

@[expose] public section
namespace ThomGame.Pictures.FinCircle

open MarkedReturn

section Numbered

variable {n : Nat} [NeZero n]

theorem rotate_val (a : Fin n) :
    (finRotate n a).val = if a.val + 1 < n then a.val + 1 else 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [coe_finRotate]
  by_cases h : a = Fin.last k
  · subst a
    simp
  · have ha : a.val ≠ k := by
      intro he
      exact h (Fin.ext he)
    have hb := a.isLt
    simp only [ite_eq_right h, ite_eq_left (by omega : a.val + 1 < k + 1)]

theorem rotate_eq_zero_of_last (a : Fin n) (h : ¬ a.val + 1 < n) : finRotate n a = 0 := by
  apply Fin.ext
  rw [rotate_val, ite_eq_right h, Fin.val_zero]

theorem hit_of_lt (p : Fin n → Prop) (a b : Fin n) (hab : a < b)
    (hp : ∀ x, a < x → x < b → ¬ p x) : Hit (finRotate n) p a b := by
  induction hd : b.val - a.val using Nat.strong_induction_on generalizing a b with
  | h d ih =>
    have hstep : a.val + 1 < n := by have hb := b.isLt; exact Nat.lt_of_le_of_lt hab hb
    have hv : (finRotate n a).val = a.val + 1 := by rw [rotate_val, ite_eq_left hstep]
    by_cases he : finRotate n a = b
    · rw [← he]
      exact Hit.direct _
    · have hnext : finRotate n a < b := by
        have hne : (finRotate n a).val ≠ b.val := fun h => he (Fin.ext h)
        change a.val < b.val at hab
        change (finRotate n a).val < b.val
        omega
      refine Hit.skip a (hp _ (by change a.val < (finRotate n a).val; omega) hnext) ?_
      exact ih (b.val - (finRotate n a).val) (by omega) (finRotate n a) b hnext
        (fun x hax hxb => hp x (lt_trans (by change a.val < (finRotate n a).val; omega) hax) hxb) rfl

theorem hit_to_zero (p : Fin n → Prop) (a : Fin n)
    (hp : ∀ x, a < x → ¬ p x) : Hit (finRotate n) p a 0 := by
  induction hd : n - a.val using Nat.strong_induction_on generalizing a with
  | h d ih =>
    by_cases ha : a.val + 1 < n
    · have hv : (finRotate n a).val = a.val + 1 := by rw [rotate_val, ite_eq_left ha]
      have hlt : a < finRotate n a := by change a.val < (finRotate n a).val; omega
      refine Hit.skip a (hp _ hlt) ?_
      exact ih (n - (finRotate n a).val) (by have ha' := a.isLt; omega) (finRotate n a)
        (fun x hx => hp x (lt_trans hlt hx)) rfl
    · rw [← rotate_eq_zero_of_last a ha]
      exact Hit.direct _

theorem hit_wrap (p : Fin n → Prop) (a b : Fin n)
    (hhi : ∀ x, a < x → ¬ p x) (hlo : ∀ x, x < b → ¬ p x) :
    Hit (finRotate n) p a b := by
  have h0 := hit_to_zero p a hhi
  by_cases hb : b = 0
  · simpa only [hb] using h0
  · have hbpos : (0 : Fin n) < b := Fin.pos_iff_ne_zero.mpr hb
    exact h0.append (hlo 0 hbpos) (hit_of_lt p 0 b hbpos (fun x _ hx => hlo x hx))

end Numbered

variable {m n : Nat}

theorem hit_image_next (e : Fin m → Fin n) (he : StrictMono e) (i : Fin m) :
    Hit (finRotate n) (Set.range e) (e i) (e (finRotate m i)) := by
  let : NeZero m := i.neZero
  let : NeZero n := (e i).neZero
  by_cases hi : i.val + 1 < m
  · have hv : (finRotate m i).val = i.val + 1 := by rw [rotate_val, ite_eq_left hi]
    have hii : i < finRotate m i := by change i.val < (finRotate m i).val; omega
    apply hit_of_lt _ _ _ (he hii)
    rintro x hix hxi ⟨j, rfl⟩
    have hj := he.lt_iff_lt.mp hix
    have hj' := he.lt_iff_lt.mp hxi
    change i.val < j.val at hj
    change j.val < (finRotate m i).val at hj'
    omega
  · rw [rotate_eq_zero_of_last i hi]
    apply hit_wrap
    · rintro x hix ⟨j, rfl⟩
      have hj := he.lt_iff_lt.mp hix
      have hj' := j.isLt
      change i.val < j.val at hj
      omega
    · rintro x hx ⟨j, rfl⟩
      exact (not_lt_of_ge (Fin.zero_le j)) (he.lt_iff_lt.mp hx)

end ThomGame.Pictures.FinCircle

module

public import ThomGame.Pictures.CircularPartition
public import ThomGame.Pictures.FinCirclePaths

/-!
# Combining two noncrossing partitions in one numbered circle

The two increasing embeddings preserve cyclic visits by actual return
paths. Noninterlacing additionally requires that the two entire images
do not alternate. Concrete boundary embeddings discharge these explicit
order hypotheses separately.
-/

@[expose] public section
namespace ThomGame.Pictures.CircularPartition

open MarkedReturn

variable {m n k : Nat}

theorem strictMono_sbtw (e : Fin m → Fin k) (he : StrictMono e) (a b c : Fin m) :
    sbtw (e a) (e b) (e c) ↔ sbtw a b c := by
  simp only [Fin.sbtw_iff, he.lt_iff_lt]

theorem sameCycle_image_left (f : Equiv.Perm (Fin m)) (g : Equiv.Perm (Fin n))
    (h : Equiv.Perm (Fin k)) (e : Fin m ⊕ Fin n ≃ Fin k)
    (he : ∀ a, h (e a) = e (Equiv.sumCongr f g a)) (x : Fin m) {y : Fin k}
    (hxy : h.SameCycle (e (.inl x)) y) : ∃ z : Fin m, e (.inl z) = y := by
  obtain ⟨y, rfl⟩ := e.surjective y
  have hs := (FiniteReturn.sameCycle_congr _ _ e he _ _).mpr hxy
  cases y with
  | inl y => exact ⟨y, rfl⟩
  | inr y => exact (FiniteReturn.sum_not_sameCycle f g x y hs).elim

theorem sameCycle_image_right (f : Equiv.Perm (Fin m)) (g : Equiv.Perm (Fin n))
    (h : Equiv.Perm (Fin k)) (e : Fin m ⊕ Fin n ≃ Fin k)
    (he : ∀ a, h (e a) = e (Equiv.sumCongr f g a)) (x : Fin n) {y : Fin k}
    (hxy : h.SameCycle (e (.inr x)) y) : ∃ z : Fin n, e (.inr z) = y := by
  obtain ⟨y, rfl⟩ := e.surjective y
  have hs := (FiniteReturn.sameCycle_congr _ _ e he _ _).mpr hxy
  cases y with
  | inl y => exact (FiniteReturn.sum_not_sameCycle f g y x hs.symm).elim
  | inr y => exact ⟨y, rfl⟩

theorem follows_combine (f : Equiv.Perm (Fin m)) (g : Equiv.Perm (Fin n))
    (h : Equiv.Perm (Fin k)) (e : Fin m ⊕ Fin n ≃ Fin k)
    (he : ∀ a, h (e a) = e (Equiv.sumCongr f g a))
    (hleft : StrictMono (fun a : Fin m => e (.inl a)))
    (hright : StrictMono (fun a : Fin n => e (.inr a)))
    (hf : Follows (finRotate m) f) (hg : Follows (finRotate n) g) : Follows (finRotate k) h := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := e.surjective x
  obtain ⟨y, rfl⟩ := e.surjective y
  have hs := (FiniteReturn.sameCycle_congr _ _ e he _ _).mpr hxy
  rw [he]
  rcases x with x | x <;> rcases y with y | y
  · have hp := hf x y ((FiniteReturn.sum_sameCycle_inl f g x y).mp hs)
    apply hp.lift_steps (fun a => e (.inl a))
    · intro a
      exact (FinCircle.hit_image_next _ hleft a).weaken (fun z hz => sameCycle_image_left f g h e he x hz)
    · intro a
      exact (FiniteReturn.sameCycle_congr _ _ e he _ _).symm.trans (FiniteReturn.sum_sameCycle_inl f g x a)
  · exact (FiniteReturn.sum_not_sameCycle f g x y hs).elim
  · exact (FiniteReturn.sum_not_sameCycle f g y x hs.symm).elim
  · have hp := hg x y ((FiniteReturn.sum_sameCycle_inr f g x y).mp hs)
    apply hp.lift_steps (fun a => e (.inr a))
    · intro a
      exact (FinCircle.hit_image_next _ hright a).weaken (fun z hz => sameCycle_image_right f g h e he x hz)
    · intro a
      exact (FiniteReturn.sameCycle_congr _ _ e he _ _).symm.trans (FiniteReturn.sum_sameCycle_inr f g x a)

theorem noninterlacing_combine_source (f : Equiv.Perm (Fin m)) (g : Equiv.Perm (Fin n))
    (e : Fin m ⊕ Fin n ≃ Fin k)
    (hleft : StrictMono (fun a : Fin m => e (.inl a)))
    (hright : StrictMono (fun a : Fin n => e (.inr a)))
    (hLR : ∀ (a c : Fin m) (b d : Fin n),
      ¬ (sbtw (e (.inl a)) (e (.inr b)) (e (.inl c)) ∧
        sbtw (e (.inl a)) (e (.inl c)) (e (.inr d))))
    (hRL : ∀ (a c : Fin n) (b d : Fin m),
      ¬ (sbtw (e (.inr a)) (e (.inl b)) (e (.inr c)) ∧
        sbtw (e (.inr a)) (e (.inr c)) (e (.inl d))))
    (hf : NonInterlacing (sbtw : Fin m → Fin m → Fin m → Prop) f)
    (hg : NonInterlacing (sbtw : Fin n → Fin n → Fin n → Prop) g) :
    NonInterlacing (fun a b c => sbtw (e a) (e b) (e c)) (Equiv.sumCongr f g) := by
  rintro (a | a) (b | b) (c | c) (d | d) habc hacd hac hbd
  all_goals first
    | exact (FiniteReturn.sum_not_sameCycle f g _ _ hac).elim
    | exact (FiniteReturn.sum_not_sameCycle f g _ _ hac.symm).elim
    | exact (FiniteReturn.sum_not_sameCycle f g _ _ hbd).elim
    | exact (FiniteReturn.sum_not_sameCycle f g _ _ hbd.symm).elim
    | exact (hLR a c b d ⟨habc, hacd⟩).elim
    | exact (hRL a c b d ⟨habc, hacd⟩).elim
    | skip
  · exact (FiniteReturn.sum_sameCycle_inl f g a b).mpr
      (hf a b c d ((strictMono_sbtw _ hleft _ _ _).mp habc)
        ((strictMono_sbtw _ hleft _ _ _).mp hacd)
        ((FiniteReturn.sum_sameCycle_inl f g a c).mp hac)
        ((FiniteReturn.sum_sameCycle_inl f g b d).mp hbd))
  · exact (FiniteReturn.sum_sameCycle_inr f g a b).mpr
      (hg a b c d ((strictMono_sbtw _ hright _ _ _).mp habc)
        ((strictMono_sbtw _ hright _ _ _).mp hacd)
        ((FiniteReturn.sum_sameCycle_inr f g a c).mp hac)
        ((FiniteReturn.sum_sameCycle_inr f g b d).mp hbd))

theorem orderedNoncrossing_combine (f : Equiv.Perm (Fin m)) (g : Equiv.Perm (Fin n))
    (h : Equiv.Perm (Fin k)) (e : Fin m ⊕ Fin n ≃ Fin k)
    (he : ∀ a, h (e a) = e (Equiv.sumCongr f g a))
    (hleft : StrictMono (fun a : Fin m => e (.inl a)))
    (hright : StrictMono (fun a : Fin n => e (.inr a)))
    (hLR : ∀ (a c : Fin m) (b d : Fin n),
      ¬ (sbtw (e (.inl a)) (e (.inr b)) (e (.inl c)) ∧
        sbtw (e (.inl a)) (e (.inl c)) (e (.inr d))))
    (hRL : ∀ (a c : Fin n) (b d : Fin m),
      ¬ (sbtw (e (.inr a)) (e (.inl b)) (e (.inr c)) ∧
        sbtw (e (.inr a)) (e (.inr c)) (e (.inl d))))
    (hf : OrderedNoncrossing (finRotate m) sbtw f)
    (hg : OrderedNoncrossing (finRotate n) sbtw g) : OrderedNoncrossing (finRotate k) sbtw h :=
  ⟨follows_combine f g h e he hleft hright hf.follows hg.follows,
    (noninterlacing_combine_source f g e hleft hright hLR hRL hf.noninterlacing hg.noninterlacing).transport
      e he (fun _ _ _ => Iff.rfl)⟩

/-- Two consecutively numbered circles form a noncrossing union in
their concatenated numbering. -/
theorem orderedNoncrossing_consecutive (f : Equiv.Perm (Fin m)) (g : Equiv.Perm (Fin n))
    (h : Equiv.Perm (Fin (m + n)))
    (he : ∀ a, h (finSumFinEquiv a) = finSumFinEquiv (Equiv.sumCongr f g a))
    (hf : OrderedNoncrossing (finRotate m) sbtw f)
    (hg : OrderedNoncrossing (finRotate n) sbtw g) :
    OrderedNoncrossing (finRotate (m + n)) sbtw h := by
  apply orderedNoncrossing_combine f g h finSumFinEquiv he
  · intro i j hij
    exact hij
  · intro i j hij
    change m + i.val < m + j.val
    exact Nat.add_lt_add_left hij m
  · intro a c b d
    rintro ⟨h1, h2⟩
    simp only [Fin.sbtw_iff, Fin.lt_def] at h1 h2
    have ha := a.isLt
    have hc := c.isLt
    change (a.val < m + b.val ∧ m + b.val < c.val ∨
      m + b.val < c.val ∧ c.val < a.val ∨ c.val < a.val ∧ a.val < m + b.val) at h1
    change (a.val < c.val ∧ c.val < m + d.val ∨
      c.val < m + d.val ∧ m + d.val < a.val ∨ m + d.val < a.val ∧ a.val < c.val) at h2
    omega
  · intro a c b d
    rintro ⟨h1, h2⟩
    simp only [Fin.sbtw_iff, Fin.lt_def] at h1 h2
    have hb := b.isLt
    have hd := d.isLt
    change (m + a.val < b.val ∧ b.val < m + c.val ∨
      b.val < m + c.val ∧ m + c.val < m + a.val ∨
      m + c.val < m + a.val ∧ m + a.val < b.val) at h1
    change (m + a.val < m + c.val ∧ m + c.val < d.val ∨
      m + c.val < d.val ∧ d.val < m + a.val ∨
      d.val < m + a.val ∧ m + a.val < m + c.val) at h2
    omega
  · exact hf
  · exact hg

end ThomGame.Pictures.CircularPartition

module

public import ThomGame.Pictures.ReturnSurgery

/-!
# Surgery supported on marked points

Changing the targets at marked points commutes with first return.
Unmarked orbits are carried unchanged through the surgery. Consequently
the change in the total orbit count equals the change in the return
orbit count, without assuming every original orbit meets the marks.
-/

@[expose] public section
namespace ThomGame.Pictures.MarkedReturn

open Equiv FiniteReturn

variable {A : Type*} [Finite A] (f : Perm A) (p : A → Prop)

omit [Finite A] in
theorem marked_iff_of_fixes_complement (s : Perm A)
    (hs : ∀ a, ¬ p a → s a = a) (a : A) : p (s a) ↔ p a := by
  constructor
  · intro h
    by_contra ha
    exact ha (hs a ha ▸ h)
  · intro ha
    by_contra h
    have he := s.injective (hs (s a) h)
    exact h (he.symm ▸ ha)

/-- A target permutation supported on the retained set descends to the
actual first-return permutation. -/
theorem perm_mul_retained (s : Perm A) (q : Perm (Subtype p))
    (hs : ∀ a, ¬ p a → s a = a) (hq : ∀ x : Subtype p, (q x).val = s x.val) :
    perm (s * f) p = q * perm f p := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  have hp := (hit_perm f p x).twist_targets s hs
  have hm : p (s (perm f p x).val) := (hq _).symm ▸ (q (perm f p x)).property
  exact (eq_perm_of_hit (s * f) p x hm hp).symm.trans (hq _).symm

/-- No point of this orbit is marked. -/
def Avoids (a : A) : Prop := ∀ b, f.SameCycle a b → ¬ p b

omit [Finite A] in
theorem avoids_iff (a : A) : Avoids f p a ↔ ¬ HasMarkedPoint f p (orbit f a) := by
  constructor
  · rintro h ⟨b, hb⟩
    exact h b.val ((orbit_eq_iff _ _ _).mp hb).symm b.property
  · intro h b hb hp
    exact h ⟨⟨b, hp⟩, (orbit_eq_iff _ _ _).mpr hb.symm⟩

omit [Finite A] in
theorem pow_mul_eq_of_avoids (s : Perm A) (hs : ∀ a, ¬ p a → s a = a)
    {a : A} (ha : Avoids f p a) (n : Nat) : ((s * f) ^ n) a = (f ^ n) a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, Perm.mul_apply, ih]
    have hn : ¬ p (f ((f ^ n) a)) := ha _ ⟨(n + 1 : Nat), by
      simp only [zpow_natCast, pow_succ', Perm.mul_apply]⟩
    rw [hs _ hn, pow_succ', Perm.mul_apply]

theorem avoids_mul (s : Perm A) (hs : ∀ a, ¬ p a → s a = a)
    {a : A} (ha : Avoids f p a) : Avoids (s * f) p a := by
  intro b hb
  obtain ⟨n, hn⟩ := hb.exists_nat_pow_eq
  rw [pow_mul_eq_of_avoids f p s hs ha] at hn
  exact ha b ⟨(n : Int), by simpa using hn⟩

omit [Finite A] in
theorem inv_fixes_complement (s : Perm A) (hs : ∀ a, ¬ p a → s a = a) :
    ∀ a, ¬ p a → s⁻¹ a = a := by
  intro a ha
  apply s.injective
  simpa using (hs a ha).symm

theorem avoids_mul_iff (s : Perm A) (hs : ∀ a, ¬ p a → s a = a) (a : A) :
    Avoids (s * f) p a ↔ Avoids f p a := by
  constructor
  · intro h
    simpa only [inv_mul_cancel_left] using
      avoids_mul (s * f) p s⁻¹ (inv_fixes_complement p s hs) h
  · exact avoids_mul f p s hs

theorem sameCycle_mul_iff_of_avoids (s : Perm A) (hs : ∀ a, ¬ p a → s a = a)
    {a : A} (ha : Avoids f p a) (b : A) : (s * f).SameCycle a b ↔ f.SameCycle a b := by
  constructor <;> intro h <;> obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  · rw [pow_mul_eq_of_avoids f p s hs ha] at hn
    exact ⟨(n : Int), by simpa using hn⟩
  · exact ⟨(n : Int), by simpa only [zpow_natCast, pow_mul_eq_of_avoids f p s hs ha] using hn⟩

omit [Finite A] in
theorem out_avoids (c : {c : Orbit f // ¬ HasMarkedPoint f p c}) :
    Avoids f p c.val.out := by
  apply (avoids_iff f p _).mpr
  have he : orbit f c.val.out = c.val := Quotient.out_eq _
  rw [he]
  exact c.property

noncomputable def unmarkedOrbitMap (s : Perm A) (hs : ∀ a, ¬ p a → s a = a) :
    {c : Orbit f // ¬ HasMarkedPoint f p c} →
      {c : Orbit (s * f) // ¬ HasMarkedPoint (s * f) p c} := fun c =>
  ⟨orbit (s * f) c.val.out,
    (avoids_iff (s * f) p _).mp (avoids_mul f p s hs (out_avoids f p c))⟩

theorem unmarkedOrbitMap_orbit (s : Perm A) (hs : ∀ a, ¬ p a → s a = a)
    (a : A) (ha : ¬ HasMarkedPoint f p (orbit f a)) :
    (unmarkedOrbitMap f p s hs ⟨orbit f a, ha⟩).val = orbit (s * f) a := by
  apply (orbit_eq_iff _ _ _).mpr
  apply (sameCycle_mul_iff_of_avoids f p s hs (out_avoids f p ⟨orbit f a, ha⟩) a).mpr
  exact (orbit_eq_iff _ _ _).mp (Quotient.out_eq _)

noncomputable def unmarkedOrbitEquiv (s : Perm A) (hs : ∀ a, ¬ p a → s a = a) :
    {c : Orbit f // ¬ HasMarkedPoint f p c} ≃
      {c : Orbit (s * f) // ¬ HasMarkedPoint (s * f) p c} :=
  Equiv.ofBijective (unmarkedOrbitMap f p s hs) ⟨by
    intro c d he
    apply Subtype.ext
    have hh := (sameCycle_mul_iff_of_avoids f p s hs (out_avoids f p c) d.val.out).mp
      ((orbit_eq_iff _ _ _).mp (congrArg Subtype.val he))
    have he' := (orbit_eq_iff _ _ _).mpr hh
    simpa only [orbit, Quotient.out_eq] using he', by
    intro c
    have ha := (avoids_mul_iff f p s hs c.val.out).mp (out_avoids (s * f) p c)
    refine ⟨⟨orbit f c.val.out, (avoids_iff f p _).mp ha⟩, ?_⟩
    apply Subtype.ext
    rw [unmarkedOrbitMap_orbit]
    exact Quotient.out_eq _⟩

theorem orbit_card_decomposition :
    Nat.card (Orbit f) = Nat.card (Orbit (perm f p)) +
      Nat.card {c : Orbit f // ¬ HasMarkedPoint f p c} := by
  classical
  rw [Nat.card_congr (Equiv.sumCompl (HasMarkedPoint f p)).symm, Nat.card_sum,
    ← Nat.card_congr (markedOrbitEquiv f p)]

/-- The total orbit change is precisely the marked first-return change. -/
theorem orbit_card_mul_balance (s : Perm A) (hs : ∀ a, ¬ p a → s a = a) :
    Nat.card (Orbit (s * f)) + Nat.card (Orbit (perm f p)) =
      Nat.card (Orbit f) + Nat.card (Orbit (perm (s * f) p)) := by
  have h := Nat.card_congr (unmarkedOrbitEquiv f p s hs)
  have hf := orbit_card_decomposition f p
  have hg := orbit_card_decomposition (s * f) p
  omega

end ThomGame.Pictures.MarkedReturn

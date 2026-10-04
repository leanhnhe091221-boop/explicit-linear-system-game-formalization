module

public import ThomGame.Pictures.FiniteReturn
public import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Cutting and joining permutation circuits

Exchanging two targets of a finite permutation joins their circuits when
they were different, and separates them when they were the same. The
proof tracks the actual finite iterates; no planar interpretation or
cycle-count hypothesis is assumed.
-/

@[expose] public section
namespace ThomGame.Pictures.CycleSurgery

open Equiv

variable {A : Type*} [DecidableEq A]

/-- Exchange the two incoming targets `a` and `b`. -/
def splice (f : Perm A) (a b : A) : Perm A := swap a b * f

theorem splice_apply (f : Perm A) (a b x : A) :
    splice f a b x = swap a b (f x) := rfl

theorem splice_splice (f : Perm A) (a b : A) :
    splice (splice f a b) a b = f := by
  simp [splice, ← mul_assoc]

variable [Finite A]

omit [DecidableEq A] in
theorem period_pos (f : Perm A) (a : A) :
    0 < Function.minimalPeriod f a :=
  Function.minimalPeriod_pos_of_mem_periodicPts (f.injective.mem_periodicPts a)

omit [DecidableEq A] [Finite A] in
theorem pow_period (f : Perm A) (a : A) :
    (f ^ Function.minimalPeriod f a) a = a :=
  Function.iterate_minimalPeriod

omit [DecidableEq A] [Finite A] in
theorem pow_injective_before_period (f : Perm A) (a : A) {m n : Nat}
    (hm : m < Function.minimalPeriod f a) (hn : n < Function.minimalPeriod f a)
    (h : (f ^ m) a = (f ^ n) a) : m = n :=
  Function.iterate_injOn_Iio_minimalPeriod hm hn h

omit [DecidableEq A] in
theorem pow_ne_self_before_period (f : Perm A) (a : A) {n : Nat}
    (hn : 0 < n) (hp : n < Function.minimalPeriod f a) : (f ^ n) a ≠ a := by
  intro h
  have he := pow_injective_before_period f a hp (period_pos f a) h
  omega

omit [DecidableEq A] in
theorem exists_pow_before_period (f : Perm A) {a b : A} (h : f.SameCycle a b) :
    ∃ n < Function.minimalPeriod f a, (f ^ n) a = b := by
  obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
  refine ⟨m % Function.minimalPeriod f a, Nat.mod_lt _ (period_pos f a), ?_⟩
  exact Function.iterate_mod_minimalPeriod_eq.trans hm

omit [DecidableEq A] [Finite A] in
theorem apply_pow (f : Perm A) (x : A) (n : Nat) :
    f ((f ^ n) x) = (f ^ (n + 1)) x := by
  rw [pow_succ', Perm.mul_apply]

omit [Finite A] in
theorem splice_pow_of_avoids (f : Perm A) (a b x : A) (n : Nat)
    (h : ∀ i, 0 < i → i ≤ n → (f ^ i) x ≠ a ∧ (f ^ i) x ≠ b) :
    (splice f a b ^ n) x = (f ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn := h (n + 1) (by omega) le_rfl
    rw [pow_succ', Perm.mul_apply, ih (fun i hi hin => h i hi (by omega)),
      splice_apply, apply_pow]
    exact swap_apply_of_ne_of_ne hn.1 hn.2

/-- Two different old circuits become one circuit. -/
theorem joins (f : Perm A) {a b : A} (h : ¬ f.SameCycle a b) :
    (splice f a b).SameCycle a b := by
  let p := Function.minimalPeriod f a
  have hp : 0 < p := period_pos f a
  have hav : ∀ i, 0 < i → i ≤ p - 1 → (f ^ i) a ≠ a ∧ (f ^ i) a ≠ b := by
    intro i hi hip
    refine ⟨pow_ne_self_before_period f a hi (by dsimp [p] at hip ⊢; omega), ?_⟩
    intro he
    exact h ⟨(i : Int), by simpa using he⟩
  refine ⟨(p : Int), ?_⟩
  rw [zpow_natCast, show p = (p - 1) + 1 by omega, pow_succ', Perm.mul_apply,
    splice_pow_of_avoids f a b a (p - 1) hav, splice_apply,
    apply_pow, show p - 1 + 1 = p by omega]
  rw [pow_period, swap_apply_left]

/-- Cutting one old circuit separates the two cut targets. -/
theorem separates (f : Perm A) {a b : A} (hab : a ≠ b) (h : f.SameCycle a b) :
    ¬ (splice f a b).SameCycle a b := by
  obtain ⟨n, hn, he⟩ := exists_pow_before_period f h
  have hn0 : 0 < n := by
    by_contra hz
    have : n = 0 := by omega
    subst n
    exact hab he
  let segment : A → Prop := fun x => ∃ i < n, (f ^ i) a = x
  have ha : segment a := ⟨0, hn0, rfl⟩
  have hb : ¬ segment b := by
    rintro ⟨i, hi, hb⟩
    have := pow_injective_before_period f a (lt_trans hi hn) hn (hb.trans he.symm)
    omega
  have hs : ∀ x, segment x → segment (splice f a b x) := by
    rintro x ⟨i, hi, rfl⟩
    by_cases hil : i + 1 = n
    · refine ⟨0, hn0, ?_⟩
      rw [splice_apply, apply_pow, hil, he, swap_apply_right]
      rfl
    · have hin : i + 1 < n := by omega
      have hia := pow_ne_self_before_period f a (by omega : 0 < i + 1) (lt_trans hin hn)
      have hib : (f ^ (i + 1)) a ≠ b := by
        intro hb'
        have := pow_injective_before_period f a (lt_trans hin hn) hn (hb'.trans he.symm)
        omega
      refine ⟨i + 1, hin, ?_⟩
      rw [splice_apply, apply_pow, swap_apply_of_ne_of_ne hia hib]
  intro hg
  obtain ⟨m, hm⟩ := hg.exists_nat_pow_eq
  apply hb
  rw [← hm]
  clear hm
  induction m with
  | zero => exact ha
  | succ m ih =>
    rw [pow_succ', Perm.mul_apply]
    exact hs _ ih

theorem sameCycle_splice_iff (f : Perm A) {a b : A} (hab : a ≠ b) :
    (splice f a b).SameCycle a b ↔ ¬ f.SameCycle a b := by
  constructor
  · intro hg hf
    exact separates f hab hf hg
  · exact joins f

open FiniteReturn
open scoped Classical

omit [DecidableEq A] in
theorem invariant_sameCycle {B : Type*} (f : Perm A) (q : A → B)
    (hq : ∀ x, q (f x) = q x) {x y : A} (h : f.SameCycle x y) : q x = q y := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, hq]
    exact ih

omit [DecidableEq A] [Finite A] in
theorem orbit_step (f : Perm A) (x : A) : orbit f (f x) = orbit f x :=
  (orbit_eq_iff _ _ _).mpr Equiv.Perm.SameCycle.rfl.apply_left

/-- Identify the old class of `b` with the old class of `a`. -/
noncomputable def mergedClass (f : Perm A) (a b x : A) : Orbit f :=
  if orbit f x = orbit f b then orbit f a else orbit f x

omit [Finite A] in
theorem mergedClass_splice (f : Perm A) (a b x : A) :
    mergedClass f a b (splice f a b x) = mergedClass f a b x := by
  have he := orbit_step f x
  unfold mergedClass
  rw [splice_apply, ← he]
  by_cases hxa : f x = a
  · rw [hxa, swap_apply_left]
    simp
  · by_cases hxb : f x = b
    · rw [hxb, swap_apply_right]
      simp
    · rw [swap_apply_of_ne_of_ne hxa hxb]

/-- Every new circuit has a well-defined old class after the identification. -/
noncomputable def mergeOrbit (f : Perm A) (a b : A) : Orbit (splice f a b) → Orbit f :=
  Quotient.lift (mergedClass f a b) (by
    intro x y h
    exact invariant_sameCycle (splice f a b) _ (mergedClass_splice f a b) h)

theorem mergeOrbit_orbit (f : Perm A) (a b x : A) :
    mergeOrbit f a b (orbit (splice f a b) x) = mergedClass f a b x := rfl

/-- In the joining case, every old circuit remains connected in the new one. -/
theorem oldCycle_in_join (f : Perm A) {a b : A} (h : ¬ f.SameCycle a b)
    {x y : A} (hxy : f.SameCycle x y) : (splice f a b).SameCycle x y := by
  have hab := joins f h
  have hs : ∀ x, (splice f a b).SameCycle x (f x) := by
    intro x
    have hx : (splice f a b).SameCycle x (splice f a b x) := ⟨1, by simp⟩
    by_cases hxa : f x = a
    · rw [splice_apply, hxa, swap_apply_left] at hx
      rw [hxa]
      exact hx.trans hab.symm
    · by_cases hxb : f x = b
      · rw [splice_apply, hxb, swap_apply_right] at hx
        rw [hxb]
        exact hx.trans hab
      · simpa only [splice_apply, swap_apply_of_ne_of_ne hxa hxb] using hx
  obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => exact Perm.SameCycle.rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    exact ih.trans (hs _)

noncomputable def joinedOrbitMap (f : Perm A) {a b : A} (h : ¬ f.SameCycle a b) :
    Orbit f → Orbit (splice f a b) :=
  Quotient.lift (orbit (splice f a b)) (by
    intro x y hxy
    exact (orbit_eq_iff _ _ _).mpr (oldCycle_in_join f h hxy))

theorem joinedOrbitMap_mergeOrbit (f : Perm A) {a b : A} (h : ¬ f.SameCycle a b)
    (c : Orbit (splice f a b)) :
    joinedOrbitMap f h (mergeOrbit f a b c) = c := by
  refine Quotient.inductionOn c fun x => ?_
  change joinedOrbitMap f h (mergedClass f a b x) = orbit (splice f a b) x
  unfold mergedClass
  split_ifs with hx
  · change orbit (splice f a b) a = orbit (splice f a b) x
    apply (orbit_eq_iff _ _ _).mpr
    exact (joins f h).trans (oldCycle_in_join f h ((orbit_eq_iff f x b).mp hx)).symm
  · rfl

theorem mergeOrbit_injective_of_not_sameCycle (f : Perm A) {a b : A}
    (h : ¬ f.SameCycle a b) : Function.Injective (mergeOrbit f a b) := by
  intro c d hcd
  have he := congrArg (joinedOrbitMap f h) hcd
  simpa only [joinedOrbitMap_mergeOrbit] using he

theorem mergeOrbit_ne (f : Perm A) {a b : A} (h : ¬ f.SameCycle a b)
    (c : Orbit (splice f a b)) : mergeOrbit f a b c ≠ orbit f b := by
  have hab : orbit f a ≠ orbit f b := fun he => h ((orbit_eq_iff _ _ _).mp he)
  refine Quotient.inductionOn c fun x => ?_
  change mergedClass f a b x ≠ orbit f b
  unfold mergedClass
  split_ifs with hx
  · exact hab
  · exact hx

/-- Precisely one old circuit class is removed in the joining case. -/
noncomputable def joinedOrbitEquiv (f : Perm A) {a b : A} (h : ¬ f.SameCycle a b) :
    Orbit (splice f a b) ≃ {c : Orbit f // c ≠ orbit f b} :=
  Equiv.ofBijective (fun c => ⟨mergeOrbit f a b c, mergeOrbit_ne f h c⟩) ⟨by
    intro c d hcd
    exact mergeOrbit_injective_of_not_sameCycle f h (congrArg Subtype.val hcd), by
    rintro ⟨c, hc⟩
    refine Quotient.inductionOn c (fun x hx => ?_) hc
    change orbit f x ≠ orbit f b at hx
    refine ⟨orbit (splice f a b) x, Subtype.ext ?_⟩
    change mergedClass f a b x = orbit f x
    simp only [mergedClass, ite_eq_right hx]⟩

theorem orbit_card_join (f : Perm A) {a b : A} (h : ¬ f.SameCycle a b) :
    Nat.card (Orbit (splice f a b)) + 1 = Nat.card (Orbit f) := by
  let : Fintype (Orbit f) := Fintype.ofFinite _
  have he := Nat.card_congr (joinedOrbitEquiv f h)
  have hc := Fintype.card_subtype_compl (fun c : Orbit f => c = orbit f b)
  rw [Fintype.card_subtype_eq] at hc
  have hp : 0 < Fintype.card (Orbit f) := Fintype.card_pos_iff.mpr ⟨orbit f b⟩
  simp only [← Nat.card_eq_fintype_card] at hc hp
  change Nat.card {c : Orbit f // c ≠ orbit f b} = Nat.card (Orbit f) - 1 at hc
  omega

theorem orbit_card_split (f : Perm A) {a b : A} (hab : a ≠ b) (h : f.SameCycle a b) :
    Nat.card (Orbit (splice f a b)) = Nat.card (Orbit f) + 1 := by
  have hc := orbit_card_join (splice f a b) (separates f hab h)
  rw [splice_splice] at hc
  exact hc.symm

/-- Exact circuit count, including singleton circuits. -/
theorem orbit_card_splice (f : Perm A) {a b : A} (hab : a ≠ b) :
    (Nat.card (Orbit (splice f a b)) : Int) =
      Nat.card (Orbit f) + if f.SameCycle a b then 1 else -1 := by
  by_cases h : f.SameCycle a b
  · rw [ite_eq_left h, orbit_card_split f hab h, Nat.cast_add, Nat.cast_one]
  · rw [ite_eq_right h]
    have hc := orbit_card_join f h
    omega

end ThomGame.Pictures.CycleSurgery

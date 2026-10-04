module

public import ThomGame.Pictures.PermutationSurgery
public import ThomGame.Pictures.OrbitTransport

/-!
# The first return to a marked subset of a finite permutation

The return time is the least positive iterate that is marked. In
particular the construction cannot skip another marked point. It gives
a permutation even when some original circuits have no marked points.
-/

@[expose] public section
namespace ThomGame.Pictures.MarkedReturn

open Equiv
open scoped Classical

variable {A : Type*} [Finite A] (f : Perm A) (p : A → Prop)

theorem exists_return (x : Subtype p) : ∃ n : Nat, 0 < n ∧ p ((f ^ n) x.val) :=
  ⟨Function.minimalPeriod f x.val, CycleSurgery.period_pos f x.val,
    by rw [CycleSurgery.pow_period]; exact x.property⟩

noncomputable def time (x : Subtype p) : Nat := Nat.find (exists_return f p x)

theorem time_pos (x : Subtype p) : 0 < time f p x := (Nat.find_spec (exists_return f p x)).1

theorem time_mem (x : Subtype p) : p ((f ^ time f p x) x.val) :=
  (Nat.find_spec (exists_return f p x)).2

theorem time_le (x : Subtype p) {n : Nat} (hn : 0 < n) (hp : p ((f ^ n) x.val)) :
    time f p x ≤ n := Nat.find_le ⟨hn, hp⟩

theorem before_time_not_mem (x : Subtype p) {n : Nat} (hn : 0 < n) (ht : n < time f p x) :
    ¬ p ((f ^ n) x.val) := fun hp => (Nat.not_le_of_gt ht) (time_le f p x hn hp)

theorem time_eq_of_first (x : Subtype p) {n : Nat} (hn : 0 < n)
    (hp : p ((f ^ n) x.val)) (hfirst : ∀ k, 0 < k → k < n → ¬ p ((f ^ k) x.val)) :
    time f p x = n := by
  have ht := time_le f p x hn hp
  by_contra hne
  exact hfirst _ (time_pos f p x) (by omega) (time_mem f p x)

noncomputable def next (x : Subtype p) : Subtype p :=
  ⟨(f ^ time f p x) x.val, time_mem f p x⟩

theorem next_eq_of_time_le (x y : Subtype p) (ht : time f p x ≤ time f p y)
    (h : next f p x = next f p y) : x = y := by
  have he : (f ^ time f p x) x.val = (f ^ time f p y) y.val := congrArg Subtype.val h
  have hback : (f ^ (time f p y - time f p x)) y.val = x.val := by
    apply (f ^ time f p x).injective
    rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_of_le ht]
    exact he.symm
  have htime : time f p x = time f p y := by
    by_contra hne
    have hm : p ((f ^ (time f p y - time f p x)) y.val) := hback.symm ▸ x.property
    have hle := time_le f p y (by omega : 0 < time f p y - time f p x) hm
    have hp := time_pos f p x
    omega
  rw [← htime] at he
  exact Subtype.ext ((f ^ time f p x).injective he)

theorem next_injective : Function.Injective (next f p) := by
  intro x y h
  rcases le_total (time f p x) (time f p y) with ht | ht
  · exact next_eq_of_time_le f p x y ht h
  · exact (next_eq_of_time_le f p y x ht h.symm).symm

/-- The genuine first-return permutation on the marked points. -/
noncomputable def perm : Perm (Subtype p) :=
  Equiv.ofBijective (next f p) ⟨next_injective f p,
    Finite.surjective_of_injective (next_injective f p)⟩

theorem perm_apply (x : Subtype p) : (perm f p x).val = (f ^ time f p x) x.val := rfl

theorem perm_sameCycle (x : Subtype p) : f.SameCycle x.val (perm f p x).val :=
  ⟨(time f p x : Int), by rw [zpow_natCast]; rfl⟩

theorem expand {x y : Subtype p} (h : (perm f p).SameCycle x y) :
    f.SameCycle x.val y.val := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => exact Perm.SameCycle.rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    exact ih.trans (perm_sameCycle f p _)

theorem contract_pow : ∀ n : Nat, ∀ x y : Subtype p,
    (f ^ n) x.val = y.val → (perm f p).SameCycle x y := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y he
    by_cases hn : n = 0
    · subst n
      have hxy : x = y := Subtype.ext he
      exact hxy.sameCycle _
    · have ht := time_le f p x (by omega : 0 < n) (he.symm ▸ y.property)
      have hp := time_pos f p x
      have htail : (f ^ (n - time f p x)) (perm f p x).val = y.val := by
        rw [perm_apply, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel ht]
        exact he
      exact (show (perm f p).SameCycle x (perm f p x) from ⟨1, by simp⟩).trans
        (ih (n - time f p x) (by omega) (perm f p x) y htail)

theorem sameCycle_iff (x y : Subtype p) :
    (perm f p).SameCycle x y ↔ f.SameCycle x.val y.val := by
  constructor
  · exact expand f p
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact contract_pow f p n x y hn

open FiniteReturn

noncomputable def orbitMap : Orbit (perm f p) → Orbit f :=
  Quotient.lift (fun x => orbit f x.val) (by
    intro x y h
    exact (orbit_eq_iff _ _ _).mpr (expand f p h))

theorem orbitMap_orbit (x : Subtype p) : orbitMap f p (orbit (perm f p) x) = orbit f x.val := rfl

theorem orbitMap_injective : Function.Injective (orbitMap f p) := by
  intro c d
  refine Quotient.inductionOn₂ c d fun x y he => ?_
  exact (orbit_eq_iff _ _ _).mpr ((sameCycle_iff f p x y).mpr ((orbit_eq_iff _ _ _).mp he))

def HasMarkedPoint (c : Orbit f) : Prop := ∃ x : Subtype p, orbit f x.val = c

theorem orbitMap_range (c : Orbit f) :
    (∃ d, orbitMap f p d = c) ↔ HasMarkedPoint f p c := by
  constructor
  · rintro ⟨d, hd⟩
    refine Quotient.inductionOn d (fun x hx => ⟨x, hx⟩) hd
  · rintro ⟨x, hx⟩
    exact ⟨orbit (perm f p) x, hx⟩

noncomputable def markedOrbitEquiv :
    Orbit (perm f p) ≃ {c : Orbit f // HasMarkedPoint f p c} :=
  Equiv.ofBijective (fun d => ⟨orbitMap f p d, (orbitMap_range f p _).mp ⟨d, rfl⟩⟩)
    ⟨fun _ _ h => orbitMap_injective f p (congrArg Subtype.val h), by
      rintro ⟨c, hc⟩
      obtain ⟨d, hd⟩ := (orbitMap_range f p c).mpr hc
      exact ⟨d, Subtype.ext hd⟩⟩

end ThomGame.Pictures.MarkedReturn

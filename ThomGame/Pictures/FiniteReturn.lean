module

public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Data.Fintype.Quotient

/-!
# First returns in one or two permutation steps

If a permutation on retained points follows the original permutation for
one step, or for two steps with a genuinely omitted intermediate point,
its cycles are exactly the original cycles meeting the retained points.
The hypothesis is an explicit step equation, not an assumed orbit theorem.
-/

@[expose] public section
namespace ThomGame.Pictures.FiniteReturn

variable {A B : Type*} (f : Equiv.Perm A) (g : Equiv.Perm B) (e : B ↪ A)

def Advances : Prop := ∀ a : B,
  e (g a) = f (e a) ∨
    (e (g a) = f (f (e a)) ∧ ∀ b : B, e b ≠ f (e a))

namespace Advances

variable {f g e} (h : Advances f g e)

include h

theorem step_sameCycle (a : B) : f.SameCycle (e a) (e (g a)) := by
  rcases h a with ha | ⟨ha, _⟩
  · exact ⟨1, by simpa using ha.symm⟩
  · exact ⟨2, by simpa [pow_two, Equiv.Perm.mul_apply] using ha.symm⟩

theorem expand [Finite B] {a b : B} (hab : g.SameCycle a b) : f.SameCycle (e a) (e b) := by
  obtain ⟨n, rfl⟩ := hab.exists_nat_pow_eq
  clear hab
  induction n with
  | zero => exact Equiv.Perm.SameCycle.rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans (h.step_sameCycle ((g ^ n) a))

theorem contract_pow : ∀ n : Nat, ∀ a b : B, (f ^ n) (e a) = e b → g.SameCycle a b := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b hab
    cases n with
    | zero =>
      have he : e a = e b := hab
      exact (e.injective he).sameCycle g
    | succ n =>
      rcases h a with ha | ⟨ha, hn⟩
      · have htail : (f ^ n) (e (g a)) = e b := by
          rw [ha]
          simpa only [pow_succ, Equiv.Perm.mul_apply] using hab
        exact (show g.SameCycle a (g a) from ⟨1, by simp⟩).trans
          (ih n (by omega) (g a) b htail)
      · cases n with
        | zero =>
          have he : f (e a) = e b := by simpa using hab
          exact (hn b he.symm).elim
        | succ n =>
          have htail : (f ^ n) (e (g a)) = e b := by
            rw [ha]
            simpa only [pow_succ, Equiv.Perm.mul_apply] using hab
          exact (show g.SameCycle a (g a) from ⟨1, by simp⟩).trans
            (ih n (by omega) (g a) b htail)

theorem contract [Finite A] {a b : B} (hab : f.SameCycle (e a) (e b)) : g.SameCycle a b := by
  obtain ⟨n, hn⟩ := hab.exists_nat_pow_eq
  exact h.contract_pow n a b hn

theorem sameCycle_iff [Finite A] [Finite B] (a b : B) :
    g.SameCycle a b ↔ f.SameCycle (e a) (e b) := ⟨h.expand, h.contract⟩

end Advances

abbrev Orbit {A : Type*} (f : Equiv.Perm A) := Quotient (Equiv.Perm.SameCycle.setoid f)

def orbit {A : Type*} (f : Equiv.Perm A) (a : A) : Orbit f := Quotient.mk _ a

theorem orbit_eq_iff {A : Type*} (f : Equiv.Perm A) (a b : A) :
    orbit f a = orbit f b ↔ f.SameCycle a b := Quotient.eq

namespace Advances

variable {f g e} [Finite A] [Finite B] (h : Advances f g e)

include h

def orbitMap : Orbit g → Orbit f := Quotient.lift (fun a => orbit f (e a)) (by
  intro a b hab
  exact (orbit_eq_iff _ _ _).mpr (h.expand hab))

omit [Finite A] in
theorem orbitMap_orbit (a : B) : h.orbitMap (orbit g a) = orbit f (e a) := rfl

theorem orbitMap_injective : Function.Injective h.orbitMap := by
  intro x y
  refine Quotient.inductionOn₂ x y fun a b hab => ?_
  apply (orbit_eq_iff g a b).mpr
  apply h.contract
  exact (orbit_eq_iff f (e a) (e b)).mp hab

def orbitEmbedding : Orbit g ↪ Orbit f := ⟨h.orbitMap, h.orbitMap_injective⟩

omit [Finite A] in
theorem orbitMap_surjective_iff : Function.Surjective h.orbitMap ↔
    ∀ a : A, ∃ b : B, f.SameCycle (e b) a := by
  constructor
  · intro hs a
    obtain ⟨q, hq⟩ := hs (orbit f a)
    refine Quotient.inductionOn q (fun b hb => ?_) hq
    exact ⟨b, (orbit_eq_iff f _ _).mp hb⟩
  · intro hs q
    refine Quotient.inductionOn q fun a => ?_
    obtain ⟨b, hb⟩ := hs a
    exact ⟨orbit g b, (orbit_eq_iff f _ _).mpr hb⟩

end Advances
end ThomGame.Pictures.FiniteReturn

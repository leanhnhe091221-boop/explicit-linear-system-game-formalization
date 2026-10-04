module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Finset.Card

/-!
# Distributing a prescribed finite rank across bounded blocks
-/

@[expose] public section
namespace ThomGame.Analysis

variable {μ : Type*}

theorem finset_rank_allocation (a : μ → Nat) (S : Finset μ) (n : Nat)
    (hn : n ≤ ∑ i ∈ S, a i) :
    ∃ b : μ → Nat, (∀ i, b i ≤ a i) ∧ (∑ i ∈ S, b i) = n := by
  classical
  induction S using Finset.induction_on generalizing n with
  | empty =>
    have hn0 : n = 0 := by simpa using hn
    exact ⟨fun _ => 0, fun _ => Nat.zero_le _, by simp [hn0]⟩
  | @insert j S hj ih =>
    have hrest : n - min n (a j) ≤ ∑ i ∈ S, a i := by
      rw [Finset.sum_insert hj] at hn
      omega
    obtain ⟨b, hb, hsum⟩ := ih _ hrest
    refine ⟨Function.update b j (min n (a j)), ?_, ?_⟩
    · intro i
      by_cases hij : i = j
      · subst i; simp
      · simpa [Function.update_of_ne hij] using hb i
    · rw [Finset.sum_insert hj, Function.update_self, Finset.sum_update_of_notMem hj, hsum]
      omega

theorem finite_rank_allocation [Fintype μ] (a : μ → Nat) (n : Nat) (hn : n ≤ ∑ i, a i) :
    ∃ b : μ → Nat, (∀ i, b i ≤ a i) ∧ (∑ i, b i) = n :=
  finset_rank_allocation a Finset.univ n hn

end ThomGame.Analysis

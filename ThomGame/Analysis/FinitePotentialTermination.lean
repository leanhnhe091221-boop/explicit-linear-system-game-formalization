module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Finite termination from a bounded potential

If every nonterminal state admits a genuine next state increasing a
potential by a fixed positive amount, a finite path reaches a terminal
state. The proof constructs the finite path by induction on its budget.
-/

@[expose] public section
namespace ThomGame.Analysis

theorem exists_finite_terminal_path {X : Type*} (potential : X → ℝ)
    (terminal : X → Prop) (step : X → X → Prop) {δ : ℝ} (hδ : 0 < δ)
    (hupper : ∀ x, potential x ≤ 1)
    (hnext : ∀ x, ¬terminal x → ∃ y, step x y ∧ potential x + δ ≤ potential y)
    (N : Nat) (start : X) (hbudget : 1 - (N : ℝ) * δ ≤ potential start) :
    ∃ n ≤ N, ∃ path : Nat → X,
      path 0 = start ∧ terminal (path n) ∧ ∀ i < n, step (path i) (path (i + 1)) := by
  classical
  induction N generalizing start with
  | zero =>
    have ht : terminal start := by
      by_contra hnot
      obtain ⟨y, _, hy⟩ := hnext start hnot
      have hu := hupper y
      norm_num at hbudget
      linarith
    exact ⟨0, le_rfl, fun _ => start, rfl, ht, fun _ hi => False.elim (Nat.not_lt_zero _ hi)⟩
  | succ N ih =>
    by_cases ht : terminal start
    · exact ⟨0, Nat.zero_le _, fun _ => start, rfl, ht, fun _ hi => False.elim (Nat.not_lt_zero _ hi)⟩
    · obtain ⟨y, hstep, hy⟩ := hnext start ht
      have hbudget' : 1 - (N : ℝ) * δ ≤ potential y := by
        rw [Nat.cast_add, Nat.cast_one] at hbudget
        nlinarith only [hbudget, hy]
      obtain ⟨n, hn, path, hp0, hterm, hpath⟩ := ih y hbudget'
      let path' : Nat → X
        | 0 => start
        | i + 1 => path i
      refine ⟨n + 1, Nat.succ_le_succ hn, path', rfl, hterm, ?_⟩
      intro i hi
      cases i with
      | zero => simpa only [path', hp0] using hstep
      | succ i => exact hpath i (Nat.lt_of_succ_lt_succ hi)

end ThomGame.Analysis

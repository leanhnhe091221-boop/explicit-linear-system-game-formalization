module

public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Finite

/-!
# Finite-depth diagonal selection along a filter on the natural numbers

A coordinate can satisfy an increasing finite list of requirements without
satisfying the whole countable list. The selected depth tends to infinity
when each requirement holds eventually and the filter refines `atTop`.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

noncomputable def diagonalDepth (P : Nat → Nat → Prop) (n : Nat) : Nat := by
  classical
  exact Nat.findGreatest (fun k => ∀ j < k, P j n) n

theorem diagonalDepth_spec (P : Nat → Nat → Prop) (n j : Nat)
    (hj : j < diagonalDepth P n) : P j n := by
  classical
  exact Nat.findGreatest_spec (P := fun k => ∀ i < k, P i n)
    (Nat.zero_le n) (by simp) j hj

theorem diagonalDepth_le (P : Nat → Nat → Prop) (n : Nat) :
    diagonalDepth P n ≤ n := by
  classical
  exact Nat.findGreatest_le n

theorem diagonalDepth_tendsto (P : Nat → Nat → Prop) (L : Filter Nat)
    (hL : L ≤ atTop) (hP : ∀ j, ∀ᶠ n in L, P j n) :
    Tendsto (diagonalDepth P) L atTop := by
  classical
  apply tendsto_atTop.2
  intro k
  have hp : ∀ᶠ n in L, ∀ j < k, P j n := by
    simpa only [Finset.mem_range] using
      (eventually_all_finset (Finset.range k)).2 (fun j _ => hP j)
  filter_upwards [hp, (eventually_ge_atTop k).filter_mono hL] with n hn hkn
  exact Nat.le_findGreatest hkn hn

theorem diagonalDepth_pred_eventually (P : Nat → Nat → Prop) (L : Filter Nat)
    (hL : L ≤ atTop) (hP : ∀ j, ∀ᶠ n in L, P j n) (k : Nat) :
    ∀ᶠ n in L, k ≤ diagonalDepth P n - 1 ∧ P (diagonalDepth P n - 1) n := by
  filter_upwards [(diagonalDepth_tendsto P L hL hP).eventually
    (eventually_ge_atTop (k + 1))] with n hn
  exact ⟨by omega, diagonalDepth_spec P n _ (by omega)⟩

end ThomGame.Analysis

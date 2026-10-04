module

public import ThomGame.Analysis.FilterDiagonal

/-!
# Positive diagonal depths with an eventual selected-stage certificate

Each finite stage may impose a different requirement. The selected
positive depth tends to infinity, and its own stage requirement holds
eventually. This is suitable for triangular bounds on varying powers.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

noncomputable def positiveDiagonalDepth (P : Nat → Nat → Prop) (n : Nat) : Nat :=
  max 1 (diagonalDepth P n - 1)

theorem positiveDiagonalDepth_pos (P : Nat → Nat → Prop) (n : Nat) :
    0 < positiveDiagonalDepth P n :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

theorem positiveDiagonalDepth_tendsto (P : Nat → Nat → Prop) (L : Filter Nat)
    (hL : L ≤ atTop) (hP : ∀ m, ∀ᶠ n in L, P m n) :
    Tendsto (positiveDiagonalDepth P) L atTop := by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [diagonalDepth_pred_eventually P L hL hP k] with n hn
  exact hn.1.trans (le_max_right _ _)

theorem positiveDiagonalDepth_spec_eventually (P : Nat → Nat → Prop) (L : Filter Nat)
    (hL : L ≤ atTop) (hP : ∀ m, ∀ᶠ n in L, P m n) :
    ∀ᶠ n in L, P (positiveDiagonalDepth P n) n := by
  filter_upwards [diagonalDepth_pred_eventually P L hL hP 1] with n hn
  simpa only [positiveDiagonalDepth, max_eq_right hn.1] using hn.2

end ThomGame.Analysis

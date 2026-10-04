module

public import ThomGame.Analysis.PositiveFilterDiagonal
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A diverging exponent with vanishing accumulated perturbation

The exponent is selected from actual finite-stage requirements. It grows
to infinity, stays below a prescribed diverging ceiling eventually, and
its product with the nonnegative error tends to zero.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

def slowPowerRequirements (ell : Nat → Nat) (ε : Nat → ℝ) (m n : Nat) : Prop :=
  m ≤ ell n ∧ (m : ℝ) * ε n ≤ (1 / 2 : ℝ) ^ m

noncomputable def slowDivergingPower (ell : Nat → Nat) (ε : Nat → ℝ) : Nat → Nat :=
  positiveDiagonalDepth (slowPowerRequirements ell ε)

theorem slowDivergingPower_pos (ell : Nat → Nat) (ε : Nat → ℝ) (n : Nat) :
    0 < slowDivergingPower ell ε n :=
  positiveDiagonalDepth_pos _ n

variable (ell : Nat → Nat) (ε : Nat → ℝ) (L : Filter Nat) (hL : L ≤ atTop)
  (hell : Tendsto ell L atTop) (hε : Tendsto ε L (𝓝 0))

include hell hε in
theorem slowPowerRequirements_eventually (m : Nat) :
    ∀ᶠ n in L, slowPowerRequirements ell ε m n := by
  have ht : Tendsto (fun n => (m : ℝ) * ε n) L (𝓝 0) := by
    simpa only [mul_zero] using hε.const_mul (m : ℝ)
  filter_upwards [hell.eventually (eventually_ge_atTop m),
    ht.eventually_le_const (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) m)] with n hn he
  exact ⟨hn, he⟩

include hL hell hε

theorem slowDivergingPower_tendsto : Tendsto (slowDivergingPower ell ε) L atTop :=
  positiveDiagonalDepth_tendsto _ L hL (slowPowerRequirements_eventually ell ε L hell hε)

theorem slowDivergingPower_spec_eventually :
    ∀ᶠ n in L, slowPowerRequirements ell ε (slowDivergingPower ell ε n) n :=
  positiveDiagonalDepth_spec_eventually _ L hL (slowPowerRequirements_eventually ell ε L hell hε)

theorem slowDivergingPower_le_eventually :
    ∀ᶠ n in L, slowDivergingPower ell ε n ≤ ell n :=
  (slowDivergingPower_spec_eventually ell ε L hL hell hε).mono (fun _ hn => hn.1)

theorem slowDivergingPower_mul_tendsto_zero (hε₀ : ∀ n, 0 ≤ ε n) :
    Tendsto (fun n => (slowDivergingPower ell ε n : ℝ) * ε n) L (𝓝 0) := by
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).comp (slowDivergingPower_tendsto ell ε L hL hell hε)
  exact squeeze_zero' (Eventually.of_forall (fun n => mul_nonneg (Nat.cast_nonneg _) (hε₀ n)))
    ((slowDivergingPower_spec_eventually ell ε L hL hell hε).mono (fun _ hn => hn.2)) ht

end ThomGame.Analysis

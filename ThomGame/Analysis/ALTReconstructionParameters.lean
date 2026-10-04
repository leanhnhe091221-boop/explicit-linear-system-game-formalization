module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Positive reconstruction thresholds with controlled removal cost

The threshold is the actual fourth root of delta + sigma + 1/(n+1).
The positive summand handles every coordinate, including n = 0.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

noncomputable def altReconstructionThreshold (delta sigma : ℝ) (n : Nat) : ℝ :=
  Real.sqrt (Real.sqrt (delta + sigma + 1 / ((n : ℝ) + 1)))

theorem altReconstructionThreshold_pos (delta sigma : ℝ) (n : Nat)
    (hd : 0 ≤ delta) (hs : 0 ≤ sigma) : 0 < altReconstructionThreshold delta sigma n := by
  unfold altReconstructionThreshold
  positivity

theorem altReconstructionThreshold_fourth (delta sigma : ℝ) (n : Nat)
    (hd : 0 ≤ delta) (hs : 0 ≤ sigma) :
    altReconstructionThreshold delta sigma n ^ 4 = delta + sigma + 1 / ((n : ℝ) + 1) := by
  unfold altReconstructionThreshold
  rw [show (4 : Nat) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]

theorem altReconstructionThreshold_bounds (delta sigma : ℝ) (n : Nat)
    (hd : 0 ≤ delta) (hs : 0 ≤ sigma) :
    delta ≤ altReconstructionThreshold delta sigma n ^ 4 ∧
      sigma ≤ altReconstructionThreshold delta sigma n ^ 4 := by
  rw [altReconstructionThreshold_fourth delta sigma n hd hs]
  constructor <;> linarith [show (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) by positivity]

theorem altReconstructionThreshold_tendsto (delta sigma : Nat → ℝ) (L : Filter Nat) (hL : L ≤ atTop)
    (hd : Tendsto delta L (𝓝 0)) (hs : Tendsto sigma L (𝓝 0)) :
    Tendsto (fun n => altReconstructionThreshold (delta n) (sigma n) n) L (𝓝 0) := by
  have ht := ((hd.add hs).add ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mono_left hL)).sqrt.sqrt
  simpa only [zero_add, Real.sqrt_zero, altReconstructionThreshold] using ht

theorem altReconstructionThreshold_eventually_small (delta sigma : Nat → ℝ) (L : Filter Nat) (hL : L ≤ atTop)
    (hd : Tendsto delta L (𝓝 0)) (hs : Tendsto sigma L (𝓝 0)) :
    ∀ᶠ n in L, altReconstructionThreshold (delta n) (sigma n) n ≤ 1 / 2 := by
  exact (altReconstructionThreshold_tendsto delta sigma L hL hd hs).eventually_le_const (by norm_num)

theorem alt_reconstruction_removal_cost (delta rho : ℝ) (hd : 0 ≤ delta) (hrho : 0 < rho)
    (hbound : delta ≤ rho ^ 4) : 64 * delta ^ 2 / rho ^ 6 ≤ 64 * rho ^ 2 := by
  apply (div_le_iff₀ (pow_pos hrho 6)).mpr
  have hb := pow_le_pow_left₀ hd hbound 2
  nlinarith only [hb]

end ThomGame.Analysis

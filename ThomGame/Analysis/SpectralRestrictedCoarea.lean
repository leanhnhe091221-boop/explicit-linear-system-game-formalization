module

public import ThomGame.Analysis.SpectralStepCoarea

/-!
# Coarea restricted to active spectral pairs

For thresholds at least `a`, pairs whose two eigenvalues are below
`a` do not contribute. Keeping only the other pairs gives the sharper
mass factor used for families of positive matrices.
-/

@[expose] public section
namespace ThomGame.Analysis

open MeasureTheory Set
open scoped BigOperators

noncomputable def spectralActiveWeight (a c x y : ℝ) : ℝ :=
  if a ≤ x ∨ a ≤ y then c else 0

theorem spectralActiveWeight_nonneg (a c x y : ℝ) (hc : 0 ≤ c) :
    0 ≤ spectralActiveWeight a c x y := by
  unfold spectralActiveWeight
  split_ifs <;> positivity

theorem spectralActiveWeight_le (a c x y : ℝ) (hc : 0 ≤ c) :
    spectralActiveWeight a c x y ≤ c := by
  unfold spectralActiveWeight
  split_ifs <;> linarith

theorem spectralActiveWeight_le_steps (a c x y : ℝ) (hc : 0 ≤ c) :
    spectralActiveWeight a c x y ≤ c * (spectralStep a x + spectralStep a y) := by
  by_cases hx : a ≤ x <;> by_cases hy : a ≤ y <;>
    simp [spectralActiveWeight, spectralStep, hx, hy]
  linarith

theorem spectralActiveWeight_energy_eq (a c x y s : ℝ) (has : a ≤ s) :
    c * (spectralStep s y - spectralStep s x) ^ 2 =
      spectralActiveWeight a c x y * (spectralStep s y - spectralStep s x) ^ 2 := by
  by_cases hp : a ≤ x ∨ a ≤ y
  · simp [spectralActiveWeight, hp]
  · have hx : ¬s ≤ x := fun hx => hp (Or.inl (has.trans hx))
    have hy : ¬s ≤ y := fun hy => hp (Or.inr (has.trans hy))
    simp [spectralActiveWeight, hp, spectralStep, hx, hy]

theorem spectralStep_mul_le (a x : ℝ) (hx : 0 ≤ x) :
    a * spectralStep a x ≤ x := by
  unfold spectralStep
  split_ifs with ha
  · simpa using ha
  · simpa using hx

variable {ι : Type*} [Fintype ι]

theorem weighted_spectralStep_coarea_of_mass_le (a b : ℝ) (hab : a ≤ b) (c x y : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (M : ℝ)
    (hM : ∑ i, spectralActiveWeight a (c i) (x i) (y i) ≤ M) :
    (∫ s in a..b, ∑ i, c i * (spectralStep s (y i) - spectralStep s (x i)) ^ 2) ≤
      Real.sqrt (M * ∑ i, c i * (y i - x i) ^ 2) := by
  let w : ι → ℝ := fun i => spectralActiveWeight a (c i) (x i) (y i)
  have hw (i : ι) : 0 ≤ w i := spectralActiveWeight_nonneg a _ _ _ (hc i)
  have he : (∫ s in a..b, ∑ i, c i * (spectralStep s (y i) - spectralStep s (x i)) ^ 2) =
      ∫ s in a..b, ∑ i, w i * (spectralStep s (y i) - spectralStep s (x i)) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hab] at hs
    exact Finset.sum_congr rfl fun i _ => spectralActiveWeight_energy_eq a _ _ _ s hs.1
  rw [he]
  refine (weighted_spectralStep_coarea a b hab w x y hw).trans (Real.sqrt_le_sqrt ?_)
  have hM₀ : 0 ≤ M := (Finset.sum_nonneg fun i _ => hw i).trans hM
  exact mul_le_mul hM (Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (spectralActiveWeight_le a _ _ _ (hc i)) (sq_nonneg _))
    (Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)) hM₀

end ThomGame.Analysis

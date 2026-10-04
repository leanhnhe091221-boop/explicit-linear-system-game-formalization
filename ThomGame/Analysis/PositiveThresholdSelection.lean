module

public import ThomGame.Analysis.SquareSpectralCoarea

/-! A common positive-mass threshold selected using actual integral bounds. -/

@[expose] public section
namespace ThomGame.Analysis

open MeasureTheory Set

theorem exists_positive_mass_threshold (f m : ℝ → ℝ) {K : ℝ} (hK : 0 < K)
    (hf : IntegrableOn f (Ioi (0 : ℝ))) (hm : IntegrableOn m (Ioi (0 : ℝ)))
    (hf0 : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ f s) (hm0 : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ m s)
    (hint : (∫ s in Ioi (0 : ℝ), f s) ≤ K) (hmass : (∫ s in Ioi (0 : ℝ), m s) = 1) :
    ∃ s > 0, 0 < m s ∧ f s ≤ 2 * K * m s := by
  by_contra hn
  have hp (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : 2 * K * m s ≤ f s := by
    by_cases hms : 0 < m s
    · exact le_of_lt (lt_of_not_ge (fun h => hn ⟨s, hs, hms, h⟩))
    · have hz : m s = 0 := le_antisymm (le_of_not_gt hms) (hm0 s hs)
      simpa only [hz, mul_zero] using hf0 s hs
  have hi := setIntegral_mono_on (hm.const_mul (2 * K)) hf measurableSet_Ioi hp
  rw [integral_const_mul, hmass, mul_one] at hi
  linarith

end ThomGame.Analysis

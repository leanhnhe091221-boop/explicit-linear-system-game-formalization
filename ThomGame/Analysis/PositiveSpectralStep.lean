module

public import ThomGame.Analysis.SpectralStepCoarea

/-!
# Integrable positive level sets

For nonnegative x this is the indicator of (0,x]. Its full-line
integral is x, and differences have the usual spectral coarea formula.
-/

@[expose] public section
namespace ThomGame.Analysis

open MeasureTheory Set

noncomputable def positiveSpectralStep (s x : ℝ) : ℝ :=
  (spectralStep s x - spectralStep s 0) ^ 2

theorem positiveSpectralStep_of_pos {s : ℝ} (hs : 0 < s) (x : ℝ) :
    positiveSpectralStep s x = spectralStep s x := by
  simp only [positiveSpectralStep, spectralStep, not_le.mpr hs, ite_false, sub_zero]
  split_ifs <;> norm_num

theorem positiveSpectralStep_of_nonpos {s x : ℝ} (hs : s ≤ 0) (hx : 0 ≤ x) :
    positiveSpectralStep s x = 0 := by
  simp only [positiveSpectralStep, spectralStep, hs.trans hx, hs, ite_true, sub_self, zero_pow (by decide : 2 ≠ 0)]

theorem positiveSpectralStep_nonneg (s x : ℝ) : 0 ≤ positiveSpectralStep s x := sq_nonneg _

theorem positiveSpectralStep_integrable (x : ℝ) : Integrable (fun s => positiveSpectralStep s x) :=
  spectralStep_sq_sub_integrable 0 x

theorem positiveSpectralStep_integral {x : ℝ} (hx : 0 ≤ x) :
    (∫ s, positiveSpectralStep s x) = x := by
  change (∫ s, (spectralStep s x - spectralStep s 0) ^ 2) = x
  rw [spectralStep_sq_sub_integral, sub_zero, abs_of_nonneg hx]

theorem positiveSpectralStep_sub {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (s : ℝ) :
    positiveSpectralStep s y - positiveSpectralStep s x = spectralStep s y - spectralStep s x := by
  by_cases hs : 0 < s
  · rw [positiveSpectralStep_of_pos hs, positiveSpectralStep_of_pos hs]
  · have hs' := le_of_not_gt hs
    rw [positiveSpectralStep_of_nonpos hs' hy, positiveSpectralStep_of_nonpos hs' hx]
    simp only [spectralStep, hs'.trans hx, hs'.trans hy, ite_true, sub_self]

theorem positiveSpectralStep_sub_sq_integrable {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Integrable (fun s => (positiveSpectralStep s y - positiveSpectralStep s x) ^ 2) := by
  simp only [positiveSpectralStep_sub hx hy]
  exact spectralStep_sq_sub_integrable x y

theorem positiveSpectralStep_sub_sq_integral {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (∫ s, (positiveSpectralStep s y - positiveSpectralStep s x) ^ 2) = |y - x| := by
  simp only [positiveSpectralStep_sub hx hy]
  exact spectralStep_sq_sub_integral x y

end ThomGame.Analysis

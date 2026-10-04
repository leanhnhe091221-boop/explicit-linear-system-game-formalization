module

public import ThomGame.Analysis.FiniteWeightedEnergy

/-!
# Cheeger bound from expansion of positive square levels

Integrating the expansion of actual positive level sets gives a
lower bound on square variation. Weighted Cauchy--Schwarz and the
row and column masses then give the sharp constant one.
-/

@[expose] public section
namespace ThomGame.Analysis

open MeasureTheory Set
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem finiteSquareVariation_lower_of_levels (w : ι → ι → ℝ) (a : ι → ℝ) (α ρ : ℝ)
    (hlevels : ∀ s : ℝ, 0 < s → α * ρ * (∑ i, spectralStep s (a i ^ 2)) ≤
      finiteWeightedEnergy w (fun i => spectralStep s (a i ^ 2))) :
    α * (ρ * ∑ i, a i ^ 2) ≤ finiteSquareVariation w a := by
  have hI : Integrable (fun s => α * ρ * (∑ i, positiveSpectralStep s (a i ^ 2))) :=
    (integrable_finsetSum Finset.univ (fun i _ => positiveSpectralStep_integrable (a i ^ 2))).const_mul (α * ρ)
  have hp (s : ℝ) : α * ρ * (∑ i, positiveSpectralStep s (a i ^ 2)) ≤
      finiteWeightedEnergy w (fun i => positiveSpectralStep s (a i ^ 2)) := by
    by_cases hs : 0 < s
    · simpa only [positiveSpectralStep_of_pos hs] using hlevels s hs
    · simp only [positiveSpectralStep_of_nonpos (le_of_not_gt hs) (sq_nonneg _),
        finiteWeightedEnergy, Finset.sum_const_zero, mul_zero, sub_self, zero_pow (by decide : 2 ≠ 0), le_refl]
  have hh := integral_mono hI (finiteWeightedEnergy_positive_levels_integrable w a) hp
  rw [finiteWeightedEnergy_positive_levels_integral, integral_const_mul,
    integral_finsetSum Finset.univ (fun i _ => positiveSpectralStep_integrable (a i ^ 2))] at hh
  simp only [positiveSpectralStep_integral (sq_nonneg _)] at hh
  simpa only [mul_assoc] using hh

theorem finiteWeightedEnergy_cheeger_of_square_levels (w : ι → ι → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) {α ρ : ℝ} (hα : 0 ≤ α) (hρ : 0 ≤ ρ)
    (hrow : ∀ i, ∑ j, w i j = ρ / 4) (hcol : ∀ j, ∑ i, w i j = ρ / 4)
    (a : ι → ℝ)
    (hlevels : ∀ s : ℝ, 0 < s → α * ρ * (∑ i, spectralStep s (a i ^ 2)) ≤
      finiteWeightedEnergy w (fun i => spectralStep s (a i ^ 2))) :
    α ^ 2 * (ρ * ∑ i, a i ^ 2) ≤ finiteWeightedEnergy w a := by
  let M := ρ * ∑ i, a i ^ 2
  have hM : 0 ≤ M := mul_nonneg hρ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hlow := finiteSquareVariation_lower_of_levels w a α ρ hlevels
  have hupp := finiteSquareVariation_sq_le w hw hrow hcol a
  have hsq : (α * M) ^ 2 ≤ finiteWeightedEnergy w a * M :=
    (pow_le_pow_left₀ (mul_nonneg hα hM) hlow 2).trans hupp
  by_cases hMz : M = 0
  · change α ^ 2 * M ≤ _
    rw [hMz, mul_zero]
    exact finiteWeightedEnergy_nonneg w hw a
  · have hMp : 0 < M := lt_of_le_of_ne hM (Ne.symm hMz)
    have he : (α * M) ^ 2 = (α ^ 2 * M) * M := by ring
    rw [he] at hsq
    exact (mul_le_mul_iff_left₀ hMp).mp hsq

end ThomGame.Analysis

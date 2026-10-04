module

public import ThomGame.Analysis.PositiveSpectralStep

/-!
# Finite weighted Dirichlet energy and squared-level coarea

Weights may be directed. Equal row and column masses suffice for
the sharp square-variation estimate; symmetry is not assumed.
-/

@[expose] public section
namespace ThomGame.Analysis

open MeasureTheory Set
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def finiteWeightedEnergy (w : ι → ι → ℝ) (a : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, w i j * (a j - a i) ^ 2

noncomputable def finiteSquareVariation (w : ι → ι → ℝ) (a : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, w i j * |a j ^ 2 - a i ^ 2|

theorem finiteWeightedEnergy_nonneg (w : ι → ι → ℝ) (hw : ∀ i j, 0 ≤ w i j) (a : ι → ℝ) :
    0 ≤ finiteWeightedEnergy w a :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hw i j) (sq_nonneg _)

theorem finiteSquareVariation_nonneg (w : ι → ι → ℝ) (hw : ∀ i j, 0 ≤ w i j) (a : ι → ℝ) :
    0 ≤ finiteSquareVariation w a :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hw i j) (abs_nonneg _)

theorem weighted_product_abs_sum_sq_le (c x y : ι → ℝ) (hc : ∀ i, 0 ≤ c i) :
    (∑ i, c i * |x i * y i|) ^ 2 ≤ (∑ i, c i * x i ^ 2) * ∑ i, c i * y i ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · exact fun i _ => mul_nonneg (hc i) (sq_nonneg _)
  · exact fun i _ => mul_nonneg (hc i) (sq_nonneg _)
  · intro i _
    rw [mul_pow, sq_abs, mul_pow]
    exact le_of_eq (by ring)

theorem finiteWeightedEnergy_sum_sq_le (w : ι → ι → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    {ρ : ℝ} (hrow : ∀ i, ∑ j, w i j = ρ / 4) (hcol : ∀ j, ∑ i, w i j = ρ / 4)
    (a : ι → ℝ) : (∑ i, ∑ j, w i j * (a j + a i) ^ 2) ≤ ρ * ∑ i, a i ^ 2 := by
  have hleft : (∑ i, ∑ j, w i j * a j ^ 2) = ρ / 4 * ∑ i, a i ^ 2 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hcol, ← Finset.mul_sum]
  have hright : (∑ i, ∑ j, w i j * a i ^ 2) = ρ / 4 * ∑ i, a i ^ 2 := by
    simp only [← Finset.sum_mul, hrow, ← Finset.mul_sum]
  calc
    _ ≤ ∑ i, ∑ j, w i j * (2 * a j ^ 2 + 2 * a i ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (by nlinarith only [sq_nonneg (a j - a i)]) (hw i j)
    _ = 2 * (∑ i, ∑ j, w i j * a j ^ 2) + 2 * (∑ i, ∑ j, w i j * a i ^ 2) := by
      simp only [mul_add, show ∀ x y : ℝ, x * (2 * y) = 2 * (x * y) by intros; ring,
        Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by rw [hleft, hright]; ring

theorem finiteSquareVariation_sq_le (w : ι → ι → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    {ρ : ℝ} (hrow : ∀ i, ∑ j, w i j = ρ / 4) (hcol : ∀ j, ∑ i, w i j = ρ / 4)
    (a : ι → ℝ) : finiteSquareVariation w a ^ 2 ≤ finiteWeightedEnergy w a * (ρ * ∑ i, a i ^ 2) := by
  have hh := weighted_product_abs_sum_sq_le
    (fun p : ι × ι => w p.1 p.2) (fun p => a p.2 - a p.1) (fun p => a p.2 + a p.1)
    (fun p => hw p.1 p.2)
  have he (i j : ι) : (a j - a i) * (a j + a i) = a j ^ 2 - a i ^ 2 := by ring
  simp only [Fintype.sum_prod_type, he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (finiteWeightedEnergy_sum_sq_le w hw hrow hcol a)
    (finiteWeightedEnergy_nonneg w hw a))

theorem finiteWeightedEnergy_positive_levels_integrable (w : ι → ι → ℝ) (a : ι → ℝ) :
    Integrable (fun s => finiteWeightedEnergy w (fun i => positiveSpectralStep s (a i ^ 2))) := by
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact (positiveSpectralStep_sub_sq_integrable (sq_nonneg (a i)) (sq_nonneg (a j))).const_mul (w i j)

theorem finiteWeightedEnergy_positive_levels_integral (w : ι → ι → ℝ) (a : ι → ℝ) :
    (∫ s, finiteWeightedEnergy w (fun i => positiveSpectralStep s (a i ^ 2))) = finiteSquareVariation w a := by
  unfold finiteWeightedEnergy finiteSquareVariation
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · simp only [integral_const_mul, positiveSpectralStep_sub_sq_integral (sq_nonneg _) (sq_nonneg _)]
    · intro j _
      exact (positiveSpectralStep_sub_sq_integrable (sq_nonneg (a i)) (sq_nonneg (a j))).const_mul (w i j)
  · intro i _
    apply integrable_finsetSum
    intro j _
    exact (positiveSpectralStep_sub_sq_integrable (sq_nonneg (a i)) (sq_nonneg (a j))).const_mul (w i j)

end ThomGame.Analysis

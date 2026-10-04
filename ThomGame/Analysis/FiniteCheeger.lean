module

public import ThomGame.Analysis.FiniteCheegerCuts
public import ThomGame.Analysis.FiniteVariance

/-!
# Finite weighted Cheeger inequality with the lazy energy constant

Half-size cut expansion alpha implies spectral gap alpha squared
when every row and column of the energy weights sums to rho/4.
The proof constructs a median, treats its positive and negative
parts, then compares with the arithmetic mean.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem finiteWeightedEnergy_cheeger (w : ι → ι → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) {α ρ : ℝ} (hα : 0 ≤ α) (hρ : 0 ≤ ρ)
    (hrow : ∀ i, ∑ j, w i j = ρ / 4) (hcol : ∀ j, ∑ i, w i j = ρ / 4)
    (hcut : ∀ S : Finset ι, 2 * S.card ≤ Fintype.card ι →
      α * ρ * (S.card : ℝ) ≤ finiteWeightedEnergy w (finiteCutVector S))
    (a : ι → ℝ) :
    α ^ 2 * (ρ * ∑ i, (a i - (∑ j, a j) / Fintype.card ι) ^ 2) ≤ finiteWeightedEnergy w a := by
  obtain ⟨m, hmlo, hmhi⟩ := exists_finite_median a
  let p : ι → ℝ := fun i => max (a i - m) 0
  let n : ι → ℝ := fun i => max (-(a i - m)) 0
  have hps : 2 * (Finset.univ.filter (fun i => 0 < p i)).card ≤ Fintype.card ι := by
    simpa only [p, lt_max_iff, lt_self_iff_false, or_false, sub_pos] using hmhi
  have hns : 2 * (Finset.univ.filter (fun i => 0 < n i)).card ≤ Fintype.card ι := by
    simpa only [n, lt_max_iff, lt_self_iff_false, or_false, neg_pos, sub_neg] using hmlo
  have hp := finiteWeightedEnergy_cheeger_half_support w hw hα hρ hrow hcol hcut p
    (fun _ => le_max_right _ _) hps
  have hn := finiteWeightedEnergy_cheeger_half_support w hw hα hρ hrow hcol hcut n
    (fun _ => le_max_right _ _) hns
  have hmass : (∑ i, (a i - m) ^ 2) = (∑ i, p i ^ 2) + ∑ i, n i ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (real_pos_neg_sq (a i - m)).symm
  have hcenter : α ^ 2 * (ρ * ∑ i, (a i - m) ^ 2) ≤ finiteWeightedEnergy w a := by
    calc
      _ = α ^ 2 * (ρ * ∑ i, p i ^ 2) + α ^ 2 * (ρ * ∑ i, n i ^ 2) := by rw [hmass]; ring
      _ ≤ finiteWeightedEnergy w p + finiteWeightedEnergy w n := add_le_add hp hn
      _ ≤ _ := finiteWeightedEnergy_pos_neg_le w hw a m
  exact (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (finite_sum_sq_sub_mean_le a m) hρ) (sq_nonneg α)).trans hcenter

end ThomGame.Analysis

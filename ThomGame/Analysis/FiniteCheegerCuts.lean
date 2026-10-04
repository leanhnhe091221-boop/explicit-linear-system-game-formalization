module

public import ThomGame.Analysis.FiniteCheegerPositive

/-!
# Half-support cut expansion implies a quadratic bound
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def finiteCutVector (S : Finset ι) (i : ι) : ℝ := if i ∈ S then 1 else 0

theorem finiteCutVector_sum (S : Finset ι) : ∑ i, finiteCutVector S i = (S.card : ℝ) := by
  classical
  simp [finiteCutVector]

theorem spectralStep_eq_finiteCutVector (a : ι → ℝ) (s : ℝ) :
    (fun i => spectralStep s (a i)) = finiteCutVector (Finset.univ.filter (fun i => s ≤ a i)) := by
  funext i
  simp only [finiteCutVector, Finset.mem_filter, Finset.mem_univ, true_and, spectralStep]

theorem finiteWeightedEnergy_cheeger_half_support (w : ι → ι → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) {α ρ : ℝ} (hα : 0 ≤ α) (hρ : 0 ≤ ρ)
    (hrow : ∀ i, ∑ j, w i j = ρ / 4) (hcol : ∀ j, ∑ i, w i j = ρ / 4)
    (hcut : ∀ S : Finset ι, 2 * S.card ≤ Fintype.card ι →
      α * ρ * (S.card : ℝ) ≤ finiteWeightedEnergy w (finiteCutVector S))
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hhalf : 2 * (Finset.univ.filter (fun i => 0 < a i)).card ≤ Fintype.card ι) :
    α ^ 2 * (ρ * ∑ i, a i ^ 2) ≤ finiteWeightedEnergy w a := by
  apply finiteWeightedEnergy_cheeger_of_square_levels w hw hα hρ hrow hcol a
  intro s hs
  let S := Finset.univ.filter (fun i => s ≤ a i ^ 2)
  have hsub : S ⊆ Finset.univ.filter (fun i => 0 < a i) := by
    intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hi' := (Finset.mem_filter.mp hi).2
    by_contra hn
    have hz : a i = 0 := le_antisymm (le_of_not_gt hn) (ha i)
    rw [hz, zero_pow (by decide : 2 ≠ 0)] at hi'
    exact (not_le.mpr hs) hi'
  have hS : 2 * S.card ≤ Fintype.card ι :=
    (Nat.mul_le_mul_left 2 (Finset.card_le_card hsub)).trans hhalf
  rw [spectralStep_eq_finiteCutVector, finiteCutVector_sum]
  exact hcut S hS

omit [Fintype ι] [DecidableEq ι] in
theorem real_pos_neg_difference_sq_le (x y : ℝ) :
    (max y 0 - max x 0) ^ 2 + (max (-y) 0 - max (-x) 0) ^ 2 ≤ (y - x) ^ 2 := by
  simp only [max_def]
  split_ifs <;> nlinarith

omit [Fintype ι] [DecidableEq ι] in
theorem real_pos_neg_sq (x : ℝ) : (max x 0) ^ 2 + (max (-x) 0) ^ 2 = x ^ 2 := by
  simp only [max_def]
  split_ifs <;> nlinarith

omit [DecidableEq ι] in
theorem finiteWeightedEnergy_pos_neg_le (w : ι → ι → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (a : ι → ℝ) (m : ℝ) :
    finiteWeightedEnergy w (fun i => max (a i - m) 0) +
      finiteWeightedEnergy w (fun i => max (-(a i - m)) 0) ≤ finiteWeightedEnergy w a := by
  unfold finiteWeightedEnergy
  simp only [← Finset.sum_add_distrib, ← mul_add]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (hw i j)
  simpa only [sub_sub_sub_cancel_right] using real_pos_neg_difference_sq_le (a i - m) (a j - m)

end ThomGame.Analysis

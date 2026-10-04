module

public import ThomGame.Analysis.ScalarBoundedScale

/-!
# The positive conditional median of a finite weighted scale

Nonnegative weights of total mass one admit a unique positive
parameter where the weighted bounded scale is one half.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators

variable {ι : Type*} [Fintype ι] (w a : ι → ℝ)

noncomputable def weightedBoundedScale (s : ℝ) : ℝ := ∑ i, w i * boundedScaleScalar (a i) s

theorem weightedBoundedScale_zero (ha : ∀ i, 0 < a i) (hw : ∑ i, w i = 1) :
    weightedBoundedScale w a 0 = 1 := by
  simp only [weightedBoundedScale, boundedScaleScalar_zero (ha _), mul_one, hw]

theorem weightedBoundedScale_continuousOn (ha : ∀ i, 0 < a i) :
    ContinuousOn (weightedBoundedScale w a) (Set.Ici 0) :=
  continuousOn_finsetSum Finset.univ (fun i _ => continuousOn_const.mul (boundedScaleScalar_continuousOn (ha i)))

theorem weightedBoundedScale_strictAnti (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (ha : ∀ i, 0 < a i) : StrictAntiOn (weightedBoundedScale w a) (Set.Ici 0) := by
  have hpos : ∃ i, 0 < w i := by
    by_contra h
    push Not at h
    have hz : ∑ i, w i = 0 := Finset.sum_eq_zero (fun i _ => le_antisymm (h i) (hw i))
    linarith
  intro s hs t ht hst
  obtain ⟨i, hi⟩ := hpos
  exact Finset.sum_lt_sum
    (fun j _ => mul_le_mul_of_nonneg_left ((boundedScaleScalar_strictAnti (ha j) hs ht hst).le) (hw j))
    ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left (boundedScaleScalar_strictAnti (ha i) hs ht hst) hi⟩

theorem exists_unique_weightedScaleMedian (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (ha : ∀ i, 0 < a i) : ∃! s : ℝ, 0 < s ∧ weightedBoundedScale w a s = 1 / 2 := by
  classical
  let M : ℝ := (∑ i, a i) + 1
  have hM : 0 < M := by
    have hn : 0 ≤ ∑ i, a i := Finset.sum_nonneg (fun i _ => (ha i).le)
    dsimp only [M]
    linarith
  have hupper : weightedBoundedScale w a M ≤ 1 / 2 := by
    calc
      _ ≤ ∑ i, w i * (1 / 2) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (hw i)
        apply boundedScaleScalar_le_half (ha i)
        have hi := Finset.single_le_sum (f := a) (fun j _ => (ha j).le) (Finset.mem_univ i)
        dsimp only [M]
        linarith
      _ = 1 / 2 := by rw [← Finset.sum_mul, hsum, one_mul]
  have hc : ContinuousOn (weightedBoundedScale w a) (Set.Icc 0 M) :=
    (weightedBoundedScale_continuousOn w a ha).mono (fun _ h => h.1)
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc' hM.le hc
    (show 1 / 2 ∈ Set.Icc (weightedBoundedScale w a M) (weightedBoundedScale w a 0) from
      ⟨hupper, by rw [weightedBoundedScale_zero w a ha hsum]; norm_num⟩)
  have hspos : 0 < s := by
    by_contra h
    have hz : s = 0 := le_antisymm (le_of_not_gt h) hs.1
    rw [hz, weightedBoundedScale_zero w a ha hsum] at he
    norm_num at he
  refine ⟨s, ⟨hspos, he⟩, ?_⟩
  intro t ht
  exact (weightedBoundedScale_strictAnti w a hw hsum ha).injOn ht.1.le hspos.le (ht.2.trans he.symm)

noncomputable def weightedScaleMedian (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (ha : ∀ i, 0 < a i) : ℝ := (exists_unique_weightedScaleMedian w a hw hsum ha).exists.choose

theorem weightedScaleMedian_pos (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (ha : ∀ i, 0 < a i) : 0 < weightedScaleMedian w a hw hsum ha :=
  (exists_unique_weightedScaleMedian w a hw hsum ha).exists.choose_spec.1

theorem weightedScaleMedian_mean (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (ha : ∀ i, 0 < a i) : weightedBoundedScale w a (weightedScaleMedian w a hw hsum ha) = 1 / 2 :=
  (exists_unique_weightedScaleMedian w a hw hsum ha).exists.choose_spec.2

end ThomGame.Analysis

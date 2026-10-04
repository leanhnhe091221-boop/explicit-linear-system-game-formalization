module

public import ThomGame.Analysis.MatrixSquareSpectralLayerCake
public import ThomGame.Analysis.PositiveThresholdSelection

/-! One nonzero spectral projection controls all generator and relation errors together. -/

@[expose] public section
namespace ThomGame.Analysis

open MeasureTheory Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {d : Nat} {I L : Type*} [Fintype I] [Fintype L]

noncomputable def matrixCutError (U : I → UnitaryMatrix d) (R : L → CMatrix d) (P : CMatrix d) : ℝ :=
  (∑ i, rectHSNorm 1 (P * (U i).val - (U i).val * P) ^ 2) +
    ∑ j, rectHSNorm 1 (R j * P) ^ 2

theorem matrixCutError_nonneg (U : I → UnitaryMatrix d) (R : L → CMatrix d) (P : CMatrix d) :
    0 ≤ matrixCutError U R P :=
  add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem matrixCutError_generator_le (U : I → UnitaryMatrix d) (R : L → CMatrix d)
    (P : CMatrix d) (i : I) :
    rectHSNorm 1 (P * (U i).val - (U i).val * P) ^ 2 ≤ matrixCutError U R P := by
  have h : rectHSNorm 1 (P * (U i).val - (U i).val * P) ^ 2 ≤
      ∑ k, rectHSNorm 1 (P * (U k).val - (U k).val * P) ^ 2 :=
    Finset.single_le_sum (f := fun k : I => rectHSNorm 1 (P * (U k).val - (U k).val * P) ^ 2)
      (fun k _ => sq_nonneg (rectHSNorm 1 (P * (U k).val - (U k).val * P))) (Finset.mem_univ i)
  have hr : 0 ≤ ∑ j, rectHSNorm 1 (R j * P) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  change _ ≤ _ + _
  linarith only [h, hr]

theorem matrixCutError_relation_le (U : I → UnitaryMatrix d) (R : L → CMatrix d)
    (P : CMatrix d) (j : L) : rectHSNorm 1 (R j * P) ^ 2 ≤ matrixCutError U R P := by
  have h : rectHSNorm 1 (R j * P) ^ 2 ≤ ∑ k, rectHSNorm 1 (R k * P) ^ 2 :=
    Finset.single_le_sum (f := fun k : L => rectHSNorm 1 (R k * P) ^ 2)
      (fun k _ => sq_nonneg (rectHSNorm 1 (R k * P))) (Finset.mem_univ j)
  have hu : 0 ≤ ∑ i, rectHSNorm 1 (P * (U i).val - (U i).val * P) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  change _ ≤ _ + _
  linarith only [h, hu]

theorem matrixSquareSpectralCut_error_integrableOn {A : CMatrix d} (hA : Matrix.IsHermitian A)
    (U : I → UnitaryMatrix d) (R : L → CMatrix d) :
    IntegrableOn (fun s => matrixCutError U R (matrixSquareSpectralCut A s)) (Ioi (0 : ℝ)) := by
  apply Integrable.add
  · apply integrable_finsetSum
    intro i _
    exact (matrixSquareSpectralCut_intertwiner_integrable hA hA (U i).val).integrableOn
  · apply integrable_finsetSum
    intro j _
    exact matrixSquareSpectralCut_weighted_integrableOn hA (R j)

theorem matrixSquareSpectralCut_error_integral_le {A : CMatrix d} (hA : Matrix.IsHermitian A)
    (U : I → UnitaryMatrix d) (R : L → CMatrix d) :
    (∫ s in Ioi (0 : ℝ), matrixCutError U R (matrixSquareSpectralCut A s)) ≤
      2 * rectHSNorm 1 A * (∑ i, rectHSNorm 1 (A * (U i).val - (U i).val * A)) +
        ∑ j, rectHSNorm 1 (R j * A) ^ 2 := by
  have hf := integrable_finsetSum Finset.univ (fun i _ =>
    (matrixSquareSpectralCut_intertwiner_integrable hA hA (U i).val).integrableOn
      (s := Ioi (0 : ℝ)))
  have hg := integrable_finsetSum Finset.univ (fun j _ =>
    matrixSquareSpectralCut_weighted_integrableOn hA (R j))
  change (∫ s in Ioi (0 : ℝ),
    (∑ i, rectHSNorm 1 (matrixSquareSpectralCut A s * (U i).val -
      (U i).val * matrixSquareSpectralCut A s) ^ 2) +
    ∑ j, rectHSNorm 1 (R j * matrixSquareSpectralCut A s) ^ 2) ≤ _
  rw [integral_add hf hg, integral_finsetSum Finset.univ (fun i _ =>
    (matrixSquareSpectralCut_intertwiner_integrable hA hA (U i).val).integrableOn),
    integral_finsetSum Finset.univ (fun j _ => matrixSquareSpectralCut_weighted_integrableOn hA (R j))]
  simp only [matrixSquareSpectralCut_weighted_integral hA]
  refine add_le_add ?_ le_rfl
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact (setIntegral_le_integral (matrixSquareSpectralCut_intertwiner_integrable hA hA (U i).val)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)).trans (matrixSquareSpectralCut_unitary_coarea hA (U i))

theorem exists_common_matrixSpectralCut {A : CMatrix d} (hA : Matrix.IsHermitian A)
    (hAn : rectHSNorm 1 A = 1) (U : I → UnitaryMatrix d) (R : L → CMatrix d)
    {K : ℝ} (hK : 0 < K)
    (herror : 2 * (∑ i, rectHSNorm 1 (A * (U i).val - (U i).val * A)) +
      (∑ j, rectHSNorm 1 (R j * A) ^ 2) ≤ K) :
    ∃ s > 0, matrixSquareSpectralCut A s ≠ 0 ∧
      IsStarProjection (matrixSquareSpectralCut A s) ∧
      (∀ i, rectHSNorm 1 (matrixSquareSpectralCut A s * (U i).val -
        (U i).val * matrixSquareSpectralCut A s) ^ 2 ≤ 2 * K * rectHSNorm 1 (matrixSquareSpectralCut A s) ^ 2) ∧
      (∀ j, rectHSNorm 1 (R j * matrixSquareSpectralCut A s) ^ 2 ≤
        2 * K * rectHSNorm 1 (matrixSquareSpectralCut A s) ^ 2) := by
  have hm : IntegrableOn (fun s => rectHSNorm 1 (matrixSquareSpectralCut A s) ^ 2) (Ioi (0 : ℝ)) := by
    simpa only [Matrix.one_mul] using matrixSquareSpectralCut_weighted_integrableOn hA (1 : CMatrix d)
  have hint := matrixSquareSpectralCut_error_integral_le hA U R
  rw [hAn, mul_one] at hint
  have hmass := matrixSquareSpectralCut_mass_integral hA
  rw [hAn, one_pow] at hmass
  obtain ⟨s, hs, hmpos, he⟩ := exists_positive_mass_threshold
    (fun s => matrixCutError U R (matrixSquareSpectralCut A s))
    (fun s => rectHSNorm 1 (matrixSquareSpectralCut A s) ^ 2) hK
    (matrixSquareSpectralCut_error_integrableOn hA U R) hm
    (fun s _ => matrixCutError_nonneg U R _) (fun s _ => sq_nonneg _) (hint.trans herror) hmass
  refine ⟨s, hs, ?_, matrixSquareSpectralCut_isStarProjection hA s,
    fun i => (matrixCutError_generator_le U R _ i).trans he,
    fun j => (matrixCutError_relation_le U R _ j).trans he⟩
  intro hz
  simp only [hz, rectHSNorm_zero, zero_pow (by decide : 2 ≠ 0), lt_self_iff_false] at hmpos

end ThomGame.Analysis

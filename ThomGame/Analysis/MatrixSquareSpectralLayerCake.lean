module

public import ThomGame.Analysis.MatrixSquareSpectralCoarea

/-! Positive-threshold layer-cake identities for arbitrary matrix relation errors. -/

@[expose] public section
namespace ThomGame.Analysis

open MeasureTheory Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator

theorem spectralStep_positive_indicator (x : ℝ) :
    (Ioi (0 : ℝ)).indicator (fun s => spectralStep s (x ^ 2)) =
      (fun s => (spectralStep s (x ^ 2) - spectralStep s 0) ^ 2) := by
  funext s
  by_cases hs : 0 < s
  · simp only [Set.indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs)]
    rw [show spectralStep s 0 = 0 by simp [spectralStep, not_le.mpr hs], sub_zero, spectralStep_sq]
  · have h0 : s ≤ 0 := le_of_not_gt hs
    have hx : s ≤ x ^ 2 := h0.trans (sq_nonneg x)
    simp [Set.indicator, hs, spectralStep, h0, hx]

theorem spectralStep_square_integrableOn (x : ℝ) :
    IntegrableOn (fun s => spectralStep s (x ^ 2)) (Ioi (0 : ℝ)) := by
  rw [← integrable_indicator_iff measurableSet_Ioi, spectralStep_positive_indicator]
  exact spectralStep_sq_sub_integrable 0 (x ^ 2)

theorem spectralStep_square_integral (x : ℝ) :
    (∫ s in Ioi (0 : ℝ), spectralStep s (x ^ 2)) = x ^ 2 := by
  rw [← integral_indicator measurableSet_Ioi, spectralStep_positive_indicator,
    spectralStep_sq_sub_integral, sub_zero, abs_of_nonneg (sq_nonneg x)]

theorem rectHSNorm_right_cfc_sq {d e : Nat} {A : CMatrix d} (hA : Matrix.IsHermitian A)
    (R : Matrix (Fin e) (Fin d) ℂ) (f : ℝ → ℝ) :
    rectHSNorm 1 (R * cfc f A) ^ 2 =
      ∑ i, ∑ j, ‖(R * hA.eigenvectorUnitary.val) i j‖ ^ 2 * f (hA.eigenvalues j) ^ 2 := by
  rw [hA.cfc_eq]
  change rectHSNorm 1 (R * (hA.eigenvectorUnitary.val *
    Matrix.diagonal (fun j => (f (hA.eigenvalues j) : ℂ)) * hA.eigenvectorUnitary⁻¹.val)) ^ 2 = _
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, rectHSNorm_mul_unitary]
  rw [rectHSNorm_sq, Nat.cast_one, div_one]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.mul_diagonal, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

theorem matrixSquareSpectralCut_weighted_sq {d e : Nat} {A : CMatrix d}
    (hA : Matrix.IsHermitian A) (R : Matrix (Fin e) (Fin d) ℂ) (s : ℝ) :
    rectHSNorm 1 (R * matrixSquareSpectralCut A s) ^ 2 =
      ∑ i, ∑ j, ‖(R * hA.eigenvectorUnitary.val) i j‖ ^ 2 * spectralStep s (hA.eigenvalues j ^ 2) := by
  simp only [matrixSquareSpectralCut, rectHSNorm_right_cfc_sq hA, spectralStep_sq]

theorem matrixSquareSpectralCut_weighted_integrableOn {d e : Nat} {A : CMatrix d}
    (hA : Matrix.IsHermitian A) (R : Matrix (Fin e) (Fin d) ℂ) :
    IntegrableOn (fun s => rectHSNorm 1 (R * matrixSquareSpectralCut A s) ^ 2) (Ioi (0 : ℝ)) := by
  have he : (fun s => rectHSNorm 1 (R * matrixSquareSpectralCut A s) ^ 2) =
      (fun s => ∑ i, ∑ j, ‖(R * hA.eigenvectorUnitary.val) i j‖ ^ 2 *
        spectralStep s (hA.eigenvalues j ^ 2)) := by
    funext s
    exact matrixSquareSpectralCut_weighted_sq hA R s
  rw [he]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact (spectralStep_square_integrableOn (hA.eigenvalues j)).const_mul _

theorem matrixSquareSpectralCut_weighted_integral {d e : Nat} {A : CMatrix d}
    (hA : Matrix.IsHermitian A) (R : Matrix (Fin e) (Fin d) ℂ) :
    (∫ s in Ioi (0 : ℝ), rectHSNorm 1 (R * matrixSquareSpectralCut A s) ^ 2) =
      rectHSNorm 1 (R * A) ^ 2 := by
  have he : (fun s => rectHSNorm 1 (R * matrixSquareSpectralCut A s) ^ 2) =
      (fun s => ∑ i, ∑ j, ‖(R * hA.eigenvectorUnitary.val) i j‖ ^ 2 *
        spectralStep s (hA.eigenvalues j ^ 2)) := by
    funext s
    exact matrixSquareSpectralCut_weighted_sq hA R s
  rw [he, integral_finsetSum]
  · have hid : cfc (fun t : ℝ => t) A = A := cfc_id ℝ A
    have hr := rectHSNorm_right_cfc_sq hA R (fun t : ℝ => t)
    rw [hid] at hr
    rw [hr]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · simp only [integral_const_mul, spectralStep_square_integral]
    · intro j _
      exact (spectralStep_square_integrableOn (hA.eigenvalues j)).const_mul _
  · intro i _
    exact integrable_finsetSum _ (fun j _ =>
      (spectralStep_square_integrableOn (hA.eigenvalues j)).const_mul _)

theorem matrixSquareSpectralCut_mass_integral {d : Nat} {A : CMatrix d} (hA : Matrix.IsHermitian A) :
    (∫ s in Ioi (0 : ℝ), rectHSNorm 1 (matrixSquareSpectralCut A s) ^ 2) = rectHSNorm 1 A ^ 2 := by
  simpa only [Matrix.one_mul] using matrixSquareSpectralCut_weighted_integral hA (1 : CMatrix d)

end ThomGame.Analysis

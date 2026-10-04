module

public import ThomGame.Analysis.MatrixCoverageBounds

/-!
# Actual resolvents of positive matrices

The spectral definition is proved equal to the matrix inverse of
lambda times one plus S. Inverse identities, positivity and norm
bounds have constants independent of the matrix dimension.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d : Nat} {S T : CMatrix d} {lam : ℝ}

noncomputable def matrixPositiveResolvent (lam : ℝ) (S : CMatrix d) : CMatrix d :=
  cfc (fun t : ℝ => (lam + t)⁻¹) S

theorem matrix_positive_shift_eq_cfc (lam : ℝ) (hS : IsSelfAdjoint S) :
    lam • (1 : CMatrix d) + S = cfc (fun t : ℝ => lam + t) S := by
  rw [cfc_add S (fun _ : ℝ => lam) (fun t : ℝ => t) continuous_const.continuousOn
    continuous_id.continuousOn, cfc_const lam S hS, cfc_id' ℝ S hS,
    Algebra.algebraMap_eq_smul_one]

theorem matrixPositiveResolvent_isSelfAdjoint (lam : ℝ) (S : CMatrix d) :
    IsSelfAdjoint (matrixPositiveResolvent lam S) := IsSelfAdjoint.cfc

theorem matrixPositiveResolvent_nonneg (hlam : 0 < lam) (hS : 0 ≤ S) :
    0 ≤ matrixPositiveResolvent lam S := by
  apply cfc_nonneg
  intro t ht
  exact inv_nonneg.mpr (add_nonneg hlam.le (spectrum_nonneg_of_nonneg hS ht))

theorem matrixPositiveResolvent_mul_shift (hlam : 0 < lam) (hS : 0 ≤ S) :
    matrixPositiveResolvent lam S * (lam • (1 : CMatrix d) + S) = 1 := by
  rw [matrix_positive_shift_eq_cfc lam hS.isSelfAdjoint, matrixPositiveResolvent,
    ← cfc_mul _ _ S (S.finite_real_spectrum.continuousOn _) (by fun_prop)]
  calc
    _ = cfc (fun _ : ℝ => 1) S := cfc_congr fun t ht =>
      inv_mul_cancel₀ (ne_of_gt (add_pos_of_pos_of_nonneg hlam (spectrum_nonneg_of_nonneg hS ht)))
    _ = 1 := cfc_const_one ℝ S hS.isSelfAdjoint

theorem matrixPositiveResolvent_eq_inverse (hlam : 0 < lam) (hS : 0 ≤ S) :
    matrixPositiveResolvent lam S = (lam • (1 : CMatrix d) + S)⁻¹ :=
  (Matrix.inv_eq_left_inv (matrixPositiveResolvent_mul_shift hlam hS)).symm

theorem matrixPositiveResolvent_shift_mul (hlam : 0 < lam) (hS : 0 ≤ S) :
    (lam • (1 : CMatrix d) + S) * matrixPositiveResolvent lam S = 1 :=
  mul_eq_one_comm.mp (matrixPositiveResolvent_mul_shift hlam hS)

theorem matrixPositiveResolvent_norm_le (hlam : 0 < lam) (hS : 0 ≤ S) :
    matrixOpNorm (matrixPositiveResolvent lam S) ≤ lam⁻¹ := by
  apply norm_cfc_le (inv_nonneg.mpr hlam.le)
  intro t ht
  have ht0 := spectrum_nonneg_of_nonneg hS ht
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (add_nonneg hlam.le ht0))]
  simpa only [one_div] using one_div_le_one_div_of_le hlam (le_add_of_nonneg_right ht0)

theorem matrixPositiveResolvent_le_scalar (hlam : 0 < lam) (hS : 0 ≤ S) :
    matrixPositiveResolvent lam S ≤ lam⁻¹ • (1 : CMatrix d) := by
  rw [← Algebra.algebraMap_eq_smul_one]
  apply cfc_le_algebraMap _ _ S _ (S.finite_real_spectrum.continuousOn _) hS.isSelfAdjoint
  intro t ht
  simpa only [one_div] using one_div_le_one_div_of_le hlam
    (le_add_of_nonneg_right (spectrum_nonneg_of_nonneg hS ht))

theorem matrixPositiveResolvent_difference (hlam : 0 < lam) (hS : 0 ≤ S) (hT : 0 ≤ T) :
    matrixPositiveResolvent lam S - matrixPositiveResolvent lam T =
      matrixPositiveResolvent lam S * (T - S) * matrixPositiveResolvent lam T := by
  have he : T - S = (lam • (1 : CMatrix d) + T) - (lam • (1 : CMatrix d) + S) := by abel
  rw [he, mul_sub, sub_mul, mul_assoc, matrixPositiveResolvent_shift_mul hlam hT,
    mul_one, matrixPositiveResolvent_mul_shift hlam hS, one_mul]

theorem matrixPositiveResolvent_hsNorm_sub_le (hlam : 0 < lam) (hS : 0 ≤ S) (hT : 0 ≤ T) :
    hsNorm (matrixPositiveResolvent lam S - matrixPositiveResolvent lam T) ≤
      lam⁻¹ ^ 2 * hsNorm (S - T) := by
  rw [matrixPositiveResolvent_difference hlam hS hT]
  calc
    _ ≤ matrixOpNorm (matrixPositiveResolvent lam S) * hsNorm (T - S) *
        matrixOpNorm (matrixPositiveResolvent lam T) :=
      (hsNorm_mul_le_right _ _).trans
        (mul_le_mul_of_nonneg_right (hsNorm_mul_le_left _ _) (matrixOpNorm_nonneg _))
    _ ≤ lam⁻¹ * hsNorm (T - S) * lam⁻¹ := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (matrixPositiveResolvent_norm_le hlam hS) (hsNorm_nonneg _))
        (matrixPositiveResolvent_norm_le hlam hT) (matrixOpNorm_nonneg _)
        (mul_nonneg (inv_nonneg.mpr hlam.le) (hsNorm_nonneg _))
    _ = _ := by rw [hsNorm_sub_comm T S]; ring

theorem matrixPositiveResolvent_mul_self (hlam : 0 < lam) (hS : 0 ≤ S) :
    matrixPositiveResolvent lam S * S = 1 - lam • matrixPositiveResolvent lam S := by
  have he := matrixPositiveResolvent_mul_shift hlam hS
  rw [mul_add, mul_smul_comm, mul_one] at he
  exact eq_sub_of_add_eq' he

theorem matrixPositiveResolvent_self_mul (hlam : 0 < lam) (hS : 0 ≤ S) :
    S * matrixPositiveResolvent lam S = 1 - lam • matrixPositiveResolvent lam S := by
  have he := matrixPositiveResolvent_shift_mul hlam hS
  rw [add_mul, smul_mul_assoc, one_mul] at he
  exact eq_sub_of_add_eq' he

theorem matrixPositiveResolvent_self_mul_nonneg (hlam : 0 < lam) (hS : 0 ≤ S) :
    0 ≤ S * matrixPositiveResolvent lam S := by
  have hi : cfc (fun t : ℝ => t) S = S := cfc_id' ℝ S hS.isSelfAdjoint
  unfold matrixPositiveResolvent
  nth_rw 1 [← hi]
  rw [← cfc_mul (fun t : ℝ => t) (fun t : ℝ => (lam + t)⁻¹) S
    continuous_id.continuousOn (S.finite_real_spectrum.continuousOn _)]
  apply cfc_nonneg
  intro t ht
  have ht0 := spectrum_nonneg_of_nonneg hS ht
  exact mul_nonneg ht0 (inv_nonneg.mpr (add_nonneg hlam.le ht0))

theorem matrixPositiveResolvent_self_mul_le_one (hlam : 0 < lam) (hS : 0 ≤ S) :
    S * matrixPositiveResolvent lam S ≤ 1 := by
  rw [matrixPositiveResolvent_self_mul hlam hS]
  exact sub_le_self _ (smul_nonneg hlam.le (matrixPositiveResolvent_nonneg hlam hS))

end ThomGame.Analysis

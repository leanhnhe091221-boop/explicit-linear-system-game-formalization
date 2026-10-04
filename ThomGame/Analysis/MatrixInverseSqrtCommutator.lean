module

public import ThomGame.Analysis.MatrixResolventUnitaryBound
public import ThomGame.Analysis.MatrixFunctionalCalculusEnergy

/-!
# Hilbert--Schmidt control of the actual inverse square root

On the positive half-line, t |-> (1+t)^(-1/2) is 1/2-Lipschitz.
The two spectral bases estimate gives the corresponding commutator
bound for the actual square root of the positive resolvent.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

theorem real_inverse_sqrt_lipschitz {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    |(Real.sqrt a)⁻¹ - (Real.sqrt b)⁻¹| ≤ (1 / 2 : ℝ) * |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · simpa only [abs_sub_comm] using this hb ha (le_of_not_ge hab)
  have hra : 1 ≤ Real.sqrt a := by simpa using Real.sqrt_le_sqrt ha
  have hrb : 1 ≤ Real.sqrt b := by simpa using Real.sqrt_le_sqrt hb
  have hrab := Real.sqrt_le_sqrt hab
  have hpa : 0 < Real.sqrt a := by linarith
  have hpb : 0 < Real.sqrt b := by linarith
  have hi : (Real.sqrt b)⁻¹ ≤ (Real.sqrt a)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hpa hrab
  rw [abs_of_nonneg (sub_nonneg.mpr hi), abs_of_nonpos (sub_nonpos.mpr hab)]
  have hid : (Real.sqrt a)⁻¹ - (Real.sqrt b)⁻¹ =
      (Real.sqrt b - Real.sqrt a) / (Real.sqrt a * Real.sqrt b) := by field_simp
  have hprod : 1 ≤ Real.sqrt a * Real.sqrt b := by nlinarith
  have hsub : 0 ≤ Real.sqrt b - Real.sqrt a := sub_nonneg.mpr hrab
  have hdiv : (Real.sqrt b - Real.sqrt a) / (Real.sqrt a * Real.sqrt b) ≤
      Real.sqrt b - Real.sqrt a := (div_le_self hsub hprod)
  have hgap : 2 * (Real.sqrt b - Real.sqrt a) ≤ b - a := by
    have hp := mul_nonneg hsub (show 0 ≤ Real.sqrt a + Real.sqrt b - 2 by linarith)
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ a), Real.sq_sqrt (by linarith : 0 ≤ b)]
  rw [hid]
  linarith

variable {d : Nat}

theorem matrixResolventSqrt_eq_cfc {A : CMatrix d} (hA : 0 ≤ A) :
    CFC.sqrt (matrixPositiveResolvent 1 A) = cfc (fun t : ℝ => (Real.sqrt (1 + t))⁻¹) A := by
  rw [matrix_sqrt_eq_cfc_real (matrixPositiveResolvent_nonneg zero_lt_one hA), matrixPositiveResolvent]
  calc
    _ = cfc (fun t : ℝ => Real.sqrt ((1 + t)⁻¹)) A :=
      (cfc_comp' Real.sqrt (fun t : ℝ => (1 + t)⁻¹) A
        Real.continuous_sqrt.continuousOn (A.finite_real_spectrum.continuousOn _) hA.isSelfAdjoint).symm
    _ = _ := by simp only [Real.sqrt_inv]

theorem matrixResolventSqrt_norm_le {A : CMatrix d} (hA : 0 ≤ A) :
    matrixOpNorm (CFC.sqrt (matrixPositiveResolvent 1 A)) ≤ 1 := by
  rw [matrixResolventSqrt_eq_cfc hA]
  apply norm_cfc_le zero_le_one
  intro t ht
  have ht0 := spectrum_nonneg_of_nonneg hA ht
  have hs : 1 ≤ Real.sqrt (1 + t) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show 1 ≤ 1 + t by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact inv_le_one_of_one_le₀ hs

theorem hsNorm_resolventSqrt_commutator_le {A : CMatrix d} (hA : 0 ≤ A) (X : CMatrix d) :
    hsNorm (X * CFC.sqrt (matrixPositiveResolvent 1 A) - CFC.sqrt (matrixPositiveResolvent 1 A) * X) ≤
      (1 / 2 : ℝ) * hsNorm (X * A - A * X) := by
  rw [matrixResolventSqrt_eq_cfc hA, hsNorm_sub_comm (X * _), hsNorm_sub_comm (X * A)]
  have hH : Matrix.IsHermitian A := hA.isSelfAdjoint
  apply rectHSNorm_cfc_intertwiner_le_of_spectral_bound d hH hH
    (fun t : ℝ => (Real.sqrt (1 + t))⁻¹) (fun t : ℝ => (Real.sqrt (1 + t))⁻¹)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) _ X
  intro i j
  have hi := spectrum_nonneg_of_nonneg hA (hH.eigenvalues_mem_spectrum_real i)
  have hj := spectrum_nonneg_of_nonneg hA (hH.eigenvalues_mem_spectrum_real j)
  simpa only [add_sub_add_left_eq_sub] using
    real_inverse_sqrt_lipschitz (by linarith : 1 ≤ 1 + hH.eigenvalues i)
      (by linarith : 1 ≤ 1 + hH.eigenvalues j)

end ThomGame.Analysis

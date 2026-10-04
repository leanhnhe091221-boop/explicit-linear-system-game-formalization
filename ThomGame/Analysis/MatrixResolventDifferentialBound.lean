module

public import ThomGame.Analysis.MatrixOffDiagonalPairing

/-!
# Differential inequality for the resolvent potential

The exact identity and off-diagonal pairing bound give a dimension-free
estimate. We use the absolute pairing constant two, so the coefficient
of the input energy is two rather than one in the displayed source proof.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d : Nat}

theorem hsNorm_sqrt_left_sq_lower {B : CMatrix d} {lam : ℝ}
    (hB : 0 ≤ B) (hlower : lam • (1 : CMatrix d) ≤ B) (X : CMatrix d) :
    lam * hsNorm X ^ 2 ≤ hsNorm (CFC.sqrt B * X) ^ 2 := by
  have he := normalizedTrace_re_mono (star_right_conjugate_le_conjugate hlower (star X))
  simp only [star_star, mul_smul_comm, smul_mul_assoc, mul_one] at he
  have hsmul : (normalizedTrace (lam • (star X * X))).re =
      lam * (normalizedTrace (star X * X)).re := normalizedTraceRealCLM.map_smul lam (star X * X)
  rw [hsmul, normalizedTrace_gram, Complex.ofReal_re, ← matrix_sqrt_left_gram hB,
    normalizedTrace_gram, Complex.ofReal_re] at he
  exact he

theorem hsNorm_selfAdjoint_involution_mul {U : CMatrix d}
    (hU : IsSelfAdjoint U) (hUU : U * U = 1) (X : CMatrix d) : hsNorm (U * X) = hsNorm X := by
  let V : UnitaryMatrix d := ⟨U, by
    constructor <;> simpa only [← Matrix.star_eq_conjTranspose, hU.star_eq] using hUU⟩
  exact hsNorm_unitary_mul V X

theorem matrixResolvent_dissipation_lower {A D U F : CMatrix d} {lam : ℝ}
    (hA : 0 ≤ A) (hlower : lam • (1 : CMatrix d) ≤ A)
    (hU : IsSelfAdjoint U) (hUU : U * U = 1) :
    lam * hsNorm ((U * D - D * U) * F) ^ 2 ≤
      hsNorm (CFC.sqrt (U * A * U) * (D - U * D * U) * F) ^ 2 := by
  have hB : 0 ≤ U * A * U := by
    simpa only [hU.star_eq] using star_right_conjugate_nonneg hA U
  have hBlower : lam • (1 : CMatrix d) ≤ U * A * U := by
    simpa only [hU.star_eq, mul_smul_comm, smul_mul_assoc, mul_one, hUU] using
      star_right_conjugate_le_conjugate hlower U
  have he := hsNorm_sqrt_left_sq_lower hB hBlower ((D - U * D * U) * F)
  have hc : (D - U * D * U) * F = U * ((U * D - D * U) * F) := by
    have h : U * (U * D - D * U) = D - U * D * U := by
      rw [mul_sub, ← mul_assoc U U D, hUU, one_mul, ← mul_assoc]
    rw [← mul_assoc, h]
  rw [hc, hsNorm_selfAdjoint_involution_mul hU hUU] at he
  simpa only [← hc, mul_assoc] using he

theorem resolvent_young_bound {lam : ℝ} (hlam : 0 < lam) (e z : ℝ) :
    2 * e * z - lam * z ^ 2 ≤ (2 / lam) * e ^ 2 - (lam / 2) * z ^ 2 := by
  apply (mul_le_mul_iff_right₀ hlam).mp
  have he : lam * ((2 / lam) * e ^ 2 - (lam / 2) * z ^ 2) =
      2 * e ^ 2 - (lam ^ 2 / 2) * z ^ 2 := by field_simp
  rw [he]
  nlinarith [sq_nonneg (2 * e - lam * z)]

theorem matrixResolvent_dissipation_bound [NeZero d] {A D U F : CMatrix d} {lam : ℝ}
    (hlam : 0 < lam) (hA : 0 ≤ A) (hlower : lam • (1 : CMatrix d) ≤ A)
    (hD : IsSelfAdjoint D) (hU : IsSelfAdjoint U) (hUU : U * U = 1) (hF : IsStarProjection F) :
    -(normalizedTrace (star (U * F - F * U) * (U * D - D * U))).re -
        hsNorm (CFC.sqrt (U * A * U) * (D - U * D * U) * F) ^ 2 ≤
      (2 / lam) * hsNorm (U * F - F * U) ^ 2 -
        (lam / 2) * hsNorm ((U * D - D * U) * F) ^ 2 := by
  have hp := abs_normalizedTrace_commutator_pairing_le hU hF hD
  have hl := matrixResolvent_dissipation_lower hA hlower hU hUU (D := D) (F := F)
  have hn := neg_le_abs ((normalizedTrace (star (U * F - F * U) * (U * D - D * U))).re)
  exact (sub_le_sub (hn.trans hp) hl).trans
    (resolvent_young_bound hlam (hsNorm (U * F - F * U)) (hsNorm ((U * D - D * U) * F)))

theorem matrixResolventPotential_derivative_bound [NeZero d] {lam t : ℝ} {S F U : CMatrix d}
    (hlam : 0 < lam) (hS : 0 ≤ S) (hF : IsStarProjection F) (ht : 0 ≤ t)
    (hU : IsSelfAdjoint U) (hUU : U * U = 1) :
    deriv (fun s : ℝ => matrixResolventPotential (lam • 1 + S + s • F) U) t ≤
      (2 / lam) * hsNorm (U * F - F * U) ^ 2 - (lam / 2) *
        hsNorm ((U * matrixAffineResolvent lam S F t - matrixAffineResolvent lam S F t * U) * F) ^ 2 := by
  rw [(matrixResolventPotential_hasDerivAt_dissipation hlam hS hF ht hU hUU).deriv]
  have hD : IsSelfAdjoint (matrixAffineResolvent lam S F t) := by
    rw [matrixAffineResolvent_eq_positive hlam hS hF.nonneg ht]
    exact matrixPositiveResolvent_isSelfAdjoint _ _
  have hA : 0 ≤ lam • (1 : CMatrix d) + S + t • F :=
    add_nonneg (add_nonneg (smul_nonneg hlam.le zero_le_one) hS) (smul_nonneg ht hF.nonneg)
  have hlower : lam • (1 : CMatrix d) ≤ lam • (1 : CMatrix d) + S + t • F := by
    rw [add_assoc]
    exact le_add_of_nonneg_right (add_nonneg hS (smul_nonneg ht hF.nonneg))
  exact matrixResolvent_dissipation_bound hlam hA hlower hD hU hUU hF

end ThomGame.Analysis

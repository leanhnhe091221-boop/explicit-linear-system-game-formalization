module

public import ThomGame.Analysis.MatrixResolventPotentialPositive

/-!
# Exact dissipation identity for the resolvent potential

For a self-adjoint involution and a projection increment, the derivative
splits into a commutator pairing and a negative squared norm. Every
square root below is the actual positive matrix square root.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d : Nat}

theorem matrix_inverse_conjugation_difference {A D U : CMatrix d}
    (hAD : A * D = 1) (hDA : D * A = 1) (hUU : U * U = 1) :
    (D - U * D * U) * (U * A * U) * (D - U * D * U) =
      D * U * A * U * D - (D + D) + U * D * U := by
  have hr : (D - U * D * U) * U = D * U - U * D := by
    rw [sub_mul, mul_assoc (U * D) U U, hUU, mul_one]
  have hl : U * (D - U * D * U) = U * D - D * U := by
    rw [mul_sub, ← mul_assoc U (U * D) U, ← mul_assoc U U D, hUU, one_mul]
  calc
    _ = ((D - U * D * U) * U) * A * (U * (D - U * D * U)) := by noncomm_ring
    _ = (D * U - U * D) * A * (U * D - D * U) := by rw [hr, hl]
    _ = D * U * A * U * D - D * U * (A * D) * U -
        U * (D * A) * U * D + U * (D * A) * D * U := by noncomm_ring
    _ = _ := by simp only [hAD, hDA, mul_one, mul_assoc D U U, hUU, one_mul]; abel

theorem normalizedTrace_projection_sandwich {F : CMatrix d} (hF : F * F = F) (X : CMatrix d) :
    normalizedTrace (F * X * F) = normalizedTrace (F * X) := by
  rw [normalizedTrace_mul_comm (F * X) F, ← mul_assoc, hF]

theorem normalizedTrace_involution_commutators {F D U : CMatrix d}
    (hF : IsSelfAdjoint F) (hU : IsSelfAdjoint U) (hUU : U * U = 1) :
    normalizedTrace (star (U * F - F * U) * (U * D - D * U)) =
      2 * normalizedTrace (F * D) - 2 * normalizedTrace (F * U * D * U) := by
  have he : star (U * F - F * U) * (U * D - D * U) =
      F * D - F * U * D * U - U * F * U * D + U * F * D * U := by
    simp only [star_sub, star_mul, hF.star_eq, hU.star_eq]
    calc
      _ = F * (U * U) * D - F * U * D * U - U * F * U * D + U * F * D * U := by noncomm_ring
      _ = _ := by rw [hUU, mul_one]
  have hc : normalizedTrace (U * F * U * D) = normalizedTrace (F * U * D * U) := by
    rw [mul_assoc U F U, mul_assoc U (F * U) D, normalizedTrace_mul_comm U]
  have hd : normalizedTrace (U * F * D * U) = normalizedTrace (F * D) := by
    rw [normalizedTrace_mul_comm (U * F * D) U, ← mul_assoc U (U * F) D,
      ← mul_assoc U U F, hUU, one_mul]
  rw [he, normalizedTrace_add, normalizedTrace_sub, normalizedTrace_sub, hc, hd]
  ring

theorem matrix_sqrt_left_gram {B : CMatrix d} (hB : 0 ≤ B) (X : CMatrix d) :
    star (CFC.sqrt B * X) * (CFC.sqrt B * X) = star X * B * X := by
  simp only [star_mul, (CFC.sqrt_nonneg B).isSelfAdjoint.star_eq, mul_assoc]
  rw [← mul_assoc (CFC.sqrt B) (CFC.sqrt B), CFC.sqrt_mul_sqrt_self B hB]

theorem normalizedTrace_resolvent_dissipation {A D U F : CMatrix d}
    (hA : 0 ≤ A) (hD : IsSelfAdjoint D) (hU : IsSelfAdjoint U) (hUU : U * U = 1)
    (hF : IsStarProjection F) (hAD : A * D = 1) (hDA : D * A = 1) :
    (normalizedTrace (F * U * D * U - A * U * D * F * D * U)).re =
      -(normalizedTrace (star (U * F - F * U) * (U * D - D * U))).re -
        hsNorm (CFC.sqrt (U * A * U) * (D - U * D * U) * F) ^ 2 := by
  have hB : 0 ≤ U * A * U := by
    simpa only [hU.star_eq] using star_right_conjugate_nonneg hA U
  have hC : IsSelfAdjoint (D - U * D * U) := by
    show star (D - U * D * U) = D - U * D * U
    simp only [star_sub, star_mul, hD.star_eq, hU.star_eq, mul_assoc]
  have hg : normalizedTrace (star (CFC.sqrt (U * A * U) * (D - U * D * U) * F) *
      (CFC.sqrt (U * A * U) * (D - U * D * U) * F)) =
      normalizedTrace (F * (D * U * A * U * D - (D + D) + U * D * U)) := by
    rw [mul_assoc (CFC.sqrt _) _ F, matrix_sqrt_left_gram hB]
    simp only [star_mul, hF.isSelfAdjoint.star_eq, hC.star_eq]
    calc
      _ = normalizedTrace (F * ((D - U * D * U) * (U * A * U) * (D - U * D * U)) * F) := by
        congr 1; noncomm_ring
      _ = _ := by rw [matrix_inverse_conjugation_difference hAD hDA hUU,
        normalizedTrace_projection_sandwich hF.isIdempotentElem.eq]
  rw [normalizedTrace_gram] at hg
  have hc : normalizedTrace (F * (D * U * A * U * D)) =
      normalizedTrace (A * U * D * F * D * U) := by
    calc
      _ = normalizedTrace ((F * D * U) * (A * U * D)) := by congr 1; noncomm_ring
      _ = normalizedTrace ((A * U * D) * (F * D * U)) := normalizedTrace_mul_comm _ _
      _ = _ := by simp only [mul_assoc]
  simp only [mul_add, mul_sub, normalizedTrace_add, normalizedTrace_sub] at hg
  rw [hc] at hg
  have hr := congrArg Complex.re hg
  simp only [Complex.ofReal_re, Complex.add_re, Complex.sub_re] at hr
  rw [normalizedTrace_involution_commutators hF.isSelfAdjoint hU hUU]
  simp only [normalizedTrace_sub, Complex.sub_re, Complex.mul_re]
  norm_num
  rw [← mul_sub] at hr
  simp only [mul_assoc] at hr ⊢
  linarith

theorem matrixResolventPotential_hasDerivAt_dissipation {lam t : ℝ} {S F U : CMatrix d}
    (hlam : 0 < lam) (hS : 0 ≤ S) (hF : IsStarProjection F) (ht : 0 ≤ t)
    (hU : IsSelfAdjoint U) (hUU : U * U = 1) :
    HasDerivAt (fun s : ℝ => matrixResolventPotential (lam • 1 + S + s • F) U)
      (-(normalizedTrace (star (U * F - F * U) *
        (U * matrixAffineResolvent lam S F t - matrixAffineResolvent lam S F t * U))).re -
          hsNorm (CFC.sqrt (U * (lam • 1 + S + t • F) * U) *
            (matrixAffineResolvent lam S F t - U * matrixAffineResolvent lam S F t * U) * F) ^ 2) t := by
  have hpos := add_nonneg hS (smul_nonneg ht hF.nonneg)
  have hA : 0 ≤ lam • (1 : CMatrix d) + S + t • F :=
    add_nonneg (add_nonneg (smul_nonneg hlam.le zero_le_one) hS) (smul_nonneg ht hF.nonneg)
  have hD : IsSelfAdjoint (matrixAffineResolvent lam S F t) := by
    rw [matrixAffineResolvent_eq_positive hlam hS hF.nonneg ht]
    exact matrixPositiveResolvent_isSelfAdjoint _ _
  have hAD : (lam • (1 : CMatrix d) + S + t • F) * matrixAffineResolvent lam S F t = 1 := by
    rw [matrixAffineResolvent_eq_positive hlam hS hF.nonneg ht, add_assoc]
    exact matrixPositiveResolvent_shift_mul hlam hpos
  have hd := matrixResolventPotential_hasDerivAt hlam hS hF.nonneg ht U
  rwa [normalizedTrace_resolvent_dissipation hA hD hU hUU hF hAD (mul_eq_one_comm.mp hAD)] at hd

end ThomGame.Analysis

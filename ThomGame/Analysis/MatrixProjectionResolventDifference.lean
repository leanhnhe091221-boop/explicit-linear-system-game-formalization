module

public import ThomGame.Analysis.MatrixPositiveResolvent

/-!
# Resolvent differences for an added projection

An explicit inverse update yields the positive factorization in ALT
(3.5). The difference is a positive contraction and has rank at most
the added projection. All inverses and square roots are actual matrix
functional-calculus constructions.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d : Nat} {S F : CMatrix d} {lam : ℝ}

theorem projection_inverse_update_mul {A R Z F : CMatrix d}
    (hAR : A * R = 1) (hF : F * F = F) (hZ : (1 + F * R * F) * Z = 1) :
    (A + F) * (R - R * F * Z * F * R) = 1 := by
  have he : (A + F) * (R * F) = F * (1 + F * R * F) := by
    calc
      _ = (A * R) * F + F * R * F := by noncomm_ring
      _ = F + F * R * F := by rw [hAR, one_mul]
      _ = _ := by rw [mul_add, mul_one, ← mul_assoc, ← mul_assoc, hF]
  calc
    _ = (A * R + F * R) - ((A + F) * (R * F)) * Z * F * R := by noncomm_ring
    _ = (1 + F * R) - (F * (1 + F * R * F)) * Z * F * R := by rw [hAR, he]
    _ = 1 := by rw [mul_assoc F (1 + F * R * F) Z, hZ, mul_one, hF]; abel

noncomputable def matrixProjectionResolventCore (lam : ℝ) (S F : CMatrix d) : CMatrix d :=
  F * matrixPositiveResolvent lam S * F

noncomputable def matrixProjectionResolventDifference (lam : ℝ) (S F : CMatrix d) : CMatrix d :=
  lam • (matrixPositiveResolvent lam S - matrixPositiveResolvent lam (S + F))

theorem matrixProjectionResolventCore_nonneg (hlam : 0 < lam) (hS : 0 ≤ S)
    (hF : IsStarProjection F) : 0 ≤ matrixProjectionResolventCore lam S F := by
  unfold matrixProjectionResolventCore
  simpa only [hF.isSelfAdjoint.star_eq] using
    star_right_conjugate_nonneg (matrixPositiveResolvent_nonneg hlam hS) F

theorem matrixPositiveResolvent_projection_update (hlam : 0 < lam) (hS : 0 ≤ S)
    (hF : IsStarProjection F) :
    matrixPositiveResolvent lam (S + F) = matrixPositiveResolvent lam S -
      matrixPositiveResolvent lam S * F *
        matrixPositiveResolvent 1 (matrixProjectionResolventCore lam S F) * F *
          matrixPositiveResolvent lam S := by
  have hcore := matrixProjectionResolventCore_nonneg hlam hS hF
  have hZ := matrixPositiveResolvent_shift_mul zero_lt_one hcore
  simp only [one_smul, matrixProjectionResolventCore] at hZ
  have he := projection_inverse_update_mul (matrixPositiveResolvent_shift_mul hlam hS)
    hF.isIdempotentElem.eq hZ
  rw [add_assoc] at he
  rw [matrixPositiveResolvent_eq_inverse hlam (add_nonneg hS hF.nonneg)]
  exact Matrix.inv_eq_right_inv he

theorem matrixProjectionResolventDifference_factor (hlam : 0 < lam) (hS : 0 ≤ S)
    (hF : IsStarProjection F) :
    matrixProjectionResolventDifference lam S F = lam •
      (matrixPositiveResolvent lam S * F *
        matrixPositiveResolvent 1 (matrixProjectionResolventCore lam S F) * F *
          matrixPositiveResolvent lam S) := by
  rw [matrixProjectionResolventDifference, matrixPositiveResolvent_projection_update hlam hS hF,
    sub_sub_cancel]

theorem matrixProjectionResolventDifference_nonneg (hlam : 0 < lam) (hS : 0 ≤ S)
    (hF : IsStarProjection F) : 0 ≤ matrixProjectionResolventDifference lam S F := by
  rw [matrixProjectionResolventDifference_factor hlam hS hF]
  apply smul_nonneg hlam.le
  have hp := star_right_conjugate_nonneg
    (matrixPositiveResolvent_nonneg zero_lt_one (matrixProjectionResolventCore_nonneg hlam hS hF))
    (matrixPositiveResolvent lam S * F)
  simpa only [star_mul, hF.isSelfAdjoint.star_eq,
    (matrixPositiveResolvent_isSelfAdjoint lam S).star_eq, mul_assoc] using hp

theorem matrixProjectionResolventDifference_le_resolvent (hlam : 0 < lam) (hS : 0 ≤ S)
    (hF : IsStarProjection F) :
    matrixProjectionResolventDifference lam S F ≤ lam • matrixPositiveResolvent lam S := by
  apply smul_le_smul_of_nonneg_left _ hlam.le
  exact sub_le_self _ (matrixPositiveResolvent_nonneg hlam (add_nonneg hS hF.nonneg))

theorem matrixProjectionResolventDifference_le_one (hlam : 0 < lam) (hS : 0 ≤ S)
    (hF : IsStarProjection F) : matrixProjectionResolventDifference lam S F ≤ 1 := by
  apply (matrixProjectionResolventDifference_le_resolvent hlam hS hF).trans
  have he := smul_le_smul_of_nonneg_left (matrixPositiveResolvent_le_scalar hlam hS) hlam.le
  simpa only [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul] using he

theorem matrixProjectionResolventDifference_rank_le (hlam : 0 < lam) (hS : 0 ≤ S)
    (hF : IsStarProjection F) : (matrixProjectionResolventDifference lam S F).rank ≤ F.rank := by
  rw [matrixProjectionResolventDifference_factor hlam hS hF]
  have he : lam • (matrixPositiveResolvent lam S * F *
      matrixPositiveResolvent 1 (matrixProjectionResolventCore lam S F) * F *
        matrixPositiveResolvent lam S) =
      ((lam • matrixPositiveResolvent lam S) * F) *
        (matrixPositiveResolvent 1 (matrixProjectionResolventCore lam S F) * F *
          matrixPositiveResolvent lam S) := by simp only [smul_mul_assoc, mul_assoc]
  rw [he]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

end ThomGame.Analysis

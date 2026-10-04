module

public import ThomGame.Analysis.MatrixProjectionResolventDifference

/-!
# Factor and weighted-trace bounds for resolvent differences

The inverse update yields the actual factor X with D = XX*. A second
order comparison gives D <= lambda R F R and hence
trace(S squared D) <= lambda trace(F), the local estimate in ALT (3.7).
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d : Nat} {S F A B X : CMatrix d} {lam : ℝ}

noncomputable def matrixProjectionResolventFactor (lam : ℝ) (S F : CMatrix d) : CMatrix d :=
  Real.sqrt lam • (matrixPositiveResolvent lam S * F *
    CFC.sqrt (matrixPositiveResolvent 1 (matrixProjectionResolventCore lam S F)))

theorem matrixProjectionResolventDifference_eq_factor (hlam : 0 < lam) (hS : 0 ≤ S)
    (hF : IsStarProjection F) : matrixProjectionResolventDifference lam S F =
      matrixProjectionResolventFactor lam S F * star (matrixProjectionResolventFactor lam S F) := by
  have hZ := matrixPositiveResolvent_nonneg zero_lt_one
    (matrixProjectionResolventCore_nonneg hlam hS hF)
  have hsq := (CFC.sqrt_nonneg (matrixPositiveResolvent 1
    (matrixProjectionResolventCore lam S F))).isSelfAdjoint
  rw [matrixProjectionResolventDifference_factor hlam hS hF, matrixProjectionResolventFactor]
  simp only [star_smul, star_trivial, star_mul, hsq.star_eq, hF.isSelfAdjoint.star_eq,
    (matrixPositiveResolvent_isSelfAdjoint lam S).star_eq, smul_mul_assoc, mul_smul_comm,
    smul_smul, Real.mul_self_sqrt hlam.le]
  congr 1
  simp only [mul_assoc]
  rw [← mul_assoc (CFC.sqrt _) (CFC.sqrt _), CFC.sqrt_mul_sqrt_self _ hZ]

theorem matrixProjectionResolventDifference_le_gram (hlam : 0 < lam) (hS : 0 ≤ S)
    (hF : IsStarProjection F) : matrixProjectionResolventDifference lam S F ≤
      lam • (matrixPositiveResolvent lam S * F * matrixPositiveResolvent lam S) := by
  have hcore := matrixProjectionResolventCore_nonneg hlam hS hF
  have hZ : matrixPositiveResolvent 1 (matrixProjectionResolventCore lam S F) ≤ 1 := by
    simpa only [inv_one, one_smul] using matrixPositiveResolvent_le_scalar zero_lt_one hcore
  have hc := star_right_conjugate_le_conjugate hZ (matrixPositiveResolvent lam S * F)
  simp only [mul_one, star_mul, hF.isSelfAdjoint.star_eq,
    (matrixPositiveResolvent_isSelfAdjoint lam S).star_eq] at hc
  have he : (matrixPositiveResolvent lam S * F) * (F * matrixPositiveResolvent lam S) =
      matrixPositiveResolvent lam S * F * matrixPositiveResolvent lam S := by
    rw [← mul_assoc, mul_assoc (matrixPositiveResolvent lam S) F F, hF.isIdempotentElem.eq]
  rw [he] at hc
  rw [matrixProjectionResolventDifference_factor hlam hS hF]
  apply smul_le_smul_of_nonneg_left _ hlam.le
  simpa only [mul_assoc] using hc

theorem normalizedTrace_mul_re_mono (hX : 0 ≤ X) (hAB : A ≤ B) :
    (normalizedTrace (X * A)).re ≤ (normalizedTrace (X * B)).re := by
  have hp := (Complex.nonneg_iff.mp
    (normalizedTrace_mul_nonneg X (B - A) hX (sub_nonneg.mpr hAB))).1
  simpa only [mul_sub, normalizedTrace_sub, Complex.sub_re, sub_nonneg] using hp

theorem matrix_positive_contraction_mul_self_le_one (hX : 0 ≤ X) (hX1 : X ≤ 1) : X * X ≤ 1 := by
  have hn : ‖X‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg X hX).mpr hX1
  have hp : 0 ≤ X * X := by simpa only [hX.isSelfAdjoint.star_eq] using star_mul_self_nonneg X
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg (X * X) hp).mp
  exact (norm_mul_le X X).trans (by nlinarith [norm_nonneg X])

theorem matrixPositiveResolvent_self_mul_commute (hlam : 0 < lam) (hS : 0 ≤ S) :
    Commute S (matrixPositiveResolvent lam S) := by
  show S * matrixPositiveResolvent lam S = matrixPositiveResolvent lam S * S
  rw [matrixPositiveResolvent_self_mul hlam hS, matrixPositiveResolvent_mul_self hlam hS]

theorem matrixPositiveResolvent_weighted_trace (hlam : 0 < lam) (hS : 0 ≤ S) (F : CMatrix d) :
    normalizedTrace (S ^ 2 * (matrixPositiveResolvent lam S * F * matrixPositiveResolvent lam S)) =
      normalizedTrace ((S * matrixPositiveResolvent lam S) * (S * matrixPositiveResolvent lam S) * F) := by
  let R := matrixPositiveResolvent lam S
  have hc : R * S = S * R := (matrixPositiveResolvent_self_mul_commute hlam hS).eq.symm
  change normalizedTrace (S ^ 2 * (R * F * R)) = normalizedTrace ((S * R) * (S * R) * F)
  calc
    _ = normalizedTrace ((S * S * R * F) * R) := congrArg normalizedTrace (by noncomm_ring)
    _ = normalizedTrace (R * (S * S * R * F)) := normalizedTrace_mul_comm _ _
    _ = _ := by
      congr 1
      calc
        _ = (R * S) * (S * R) * F := by noncomm_ring
        _ = _ := by rw [hc]

theorem matrixProjectionResolventDifference_weighted_trace_le (hlam : 0 < lam) (hS : 0 ≤ S)
    (hF : IsStarProjection F) :
    (normalizedTrace (S ^ 2 * matrixProjectionResolventDifference lam S F)).re ≤
      lam * (normalizedTrace F).re := by
  have hSsq : 0 ≤ S ^ 2 := by
    simpa only [hS.isSelfAdjoint.star_eq, sq] using star_mul_self_nonneg S
  have hmul := matrixPositiveResolvent_self_mul_nonneg hlam hS
  have hmul1 := matrixPositiveResolvent_self_mul_le_one hlam hS
  have hsquare := matrix_positive_contraction_mul_self_le_one hmul hmul1
  have ht := normalizedTrace_mul_re_mono hF.nonneg hsquare
  rw [mul_one, normalizedTrace_mul_comm F] at ht
  calc
    _ ≤ (normalizedTrace (S ^ 2 *
        (lam • (matrixPositiveResolvent lam S * F * matrixPositiveResolvent lam S)))).re :=
      normalizedTrace_mul_re_mono hSsq (matrixProjectionResolventDifference_le_gram hlam hS hF)
    _ = lam * (normalizedTrace ((S * matrixPositiveResolvent lam S) *
        (S * matrixPositiveResolvent lam S) * F)).re := by
      rw [mul_smul_comm]
      change (normalizedTrace ((lam : ℂ) • (S ^ 2 *
        (matrixPositiveResolvent lam S * F * matrixPositiveResolvent lam S)))).re = _
      rw [normalizedTrace_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, matrixPositiveResolvent_weighted_trace hlam hS]
    _ ≤ _ := mul_le_mul_of_nonneg_left ht hlam.le

end ThomGame.Analysis

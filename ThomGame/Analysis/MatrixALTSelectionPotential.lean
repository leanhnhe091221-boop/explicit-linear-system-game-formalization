module

public import ThomGame.Analysis.MatrixALTLowSpectralTransport
public import ThomGame.Analysis.MatrixResolventDifferenceBounds

/-!
# The bounded selection potential in ALT Theorem 4.3

This is the actual trace of 1-(1+4S) inverse. The existing inverse-update
formula gives a lower bound on each projection increment. The low
spectral cut supplies the required uniform lower bound on the squared
resolvent.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat}

theorem matrixPositiveResolvent_ge_scalar {S : CMatrix d} {lam M : ℝ}
    (hlam : 0 < lam) (hS : 0 ≤ S) (hSM : S ≤ M • (1 : CMatrix d)) :
    (lam + M)⁻¹ • (1 : CMatrix d) ≤ matrixPositiveResolvent lam S := by
  have hspec : ∀ t ∈ spectrum ℝ S, t ≤ M := by
    apply (le_algebraMap_iff_spectrum_le (R := ℝ) hS.isSelfAdjoint).mp
    simpa only [Algebra.algebraMap_eq_smul_one] using hSM
  rw [matrixPositiveResolvent, ← Algebra.algebraMap_eq_smul_one]
  apply algebraMap_le_cfc _ _ S _ (S.finite_real_spectrum.continuousOn _) hS.isSelfAdjoint
  intro t ht
  simpa only [one_div] using one_div_le_one_div_of_le
    (add_pos_of_pos_of_nonneg hlam (spectrum_nonneg_of_nonneg hS ht))
    (add_le_add_right (hspec t ht) lam)

theorem matrixALTSelection_inverse {S : CMatrix d} (hS : 0 ≤ S) :
    (1 + (4 : ℝ) • S)⁻¹ = (1 / 4 : ℝ) • matrixPositiveResolvent (1 / 4) S := by
  have hshift : (1 : CMatrix d) + (4 : ℝ) • S =
      (4 : ℝ) • ((1 / 4 : ℝ) • (1 : CMatrix d) + S) := by module
  apply Matrix.inv_eq_left_inv
  rw [hshift, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    matrixPositiveResolvent_mul_shift (by norm_num : (0 : ℝ) < 1 / 4) hS]
  norm_num

noncomputable def matrixALTSelectionPotential (S : CMatrix d) : ℝ :=
  matrixTraceReal d (1 - (1 + (4 : ℝ) • S)⁻¹)

theorem matrixALTSelectionPotential_eq_resolvent {S : CMatrix d} (hS : 0 ≤ S) :
    matrixALTSelectionPotential S =
      matrixTraceReal d (1 - (1 / 4 : ℝ) • matrixPositiveResolvent (1 / 4) S) := by
  rw [matrixALTSelectionPotential, matrixALTSelection_inverse hS]

theorem matrixALTSelectionPotential_nonneg {S : CMatrix d} (hS : 0 ≤ S) :
    0 ≤ matrixALTSelectionPotential S := by
  rw [matrixALTSelectionPotential_eq_resolvent hS]
  apply matrixTraceReal_nonneg
  apply sub_nonneg.mpr
  have he := smul_le_smul_of_nonneg_left
    (matrixPositiveResolvent_le_scalar (by norm_num : (0 : ℝ) < 1 / 4) hS)
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  simpa only [smul_smul, mul_inv_cancel₀ (by norm_num : (1 / 4 : ℝ) ≠ 0), one_smul] using he

theorem matrixALTSelectionPotential_le_one [NeZero d] {S : CMatrix d} (hS : 0 ≤ S) :
    matrixALTSelectionPotential S ≤ 1 := by
  rw [matrixALTSelectionPotential_eq_resolvent hS]
  have hp := smul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (matrixPositiveResolvent_nonneg (by norm_num : (0 : ℝ) < 1 / 4) hS)
  have he := matrixTraceReal_mono d (sub_le_self (1 : CMatrix d) hp)
  have htrace : matrixTraceReal d (1 : CMatrix d) = 1 := by
    rw [matrixTraceReal, Matrix.trace_one, Fintype.card_fin, Complex.natCast_re]
    exact div_self (Nat.cast_ne_zero.mpr (NeZero.ne d))
  exact htrace ▸ he

theorem matrixALTSelectionPotential_increment {S F : CMatrix d} (hS : 0 ≤ S)
    (hF : IsStarProjection F) :
    matrixALTSelectionPotential (S + F) - matrixALTSelectionPotential S =
      matrixTraceReal d (matrixProjectionResolventDifference (1 / 4) S F) := by
  rw [matrixALTSelectionPotential_eq_resolvent (add_nonneg hS hF.nonneg),
    matrixALTSelectionPotential_eq_resolvent hS, matrixProjectionResolventDifference]
  simp only [matrixTraceReal_sub, matrixTraceReal_real_smul]
  ring

theorem matrixProjectionResolventDifference_quarter_ge_gram {S F : CMatrix d}
    (hS : 0 ≤ S) (hF : IsStarProjection F) :
    (1 / 20 : ℝ) • (matrixPositiveResolvent (1 / 4) S * F * matrixPositiveResolvent (1 / 4) S) ≤
      matrixProjectionResolventDifference (1 / 4) S F := by
  have hlam : (0 : ℝ) < 1 / 4 := by norm_num
  have hR := matrixPositiveResolvent_isSelfAdjoint (1 / 4) S
  have hcore := matrixProjectionResolventCore_nonneg hlam hS hF
  have hcore4 : matrixProjectionResolventCore (1 / 4) S F ≤ (4 : ℝ) • (1 : CMatrix d) := by
    have hc := star_right_conjugate_le_conjugate (matrixPositiveResolvent_le_scalar hlam hS) F
    have hF1 : F ≤ (1 : CMatrix d) := hF.le_one
    have hf := smul_le_smul_of_nonneg_left hF1 (by norm_num : (0 : ℝ) ≤ 4)
    have hh : matrixProjectionResolventCore (1 / 4) S F ≤ (4 : ℝ) • F := by
      simpa only [matrixProjectionResolventCore, hF.isSelfAdjoint.star_eq, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_one, hF.isIdempotentElem.eq,
        show (1 / 4 : ℝ)⁻¹ = 4 by norm_num] using hc
    exact hh.trans hf
  have hZ : (1 / 5 : ℝ) • (1 : CMatrix d) ≤
      matrixPositiveResolvent 1 (matrixProjectionResolventCore (1 / 4) S F) := by
    simpa only [show ((1 : ℝ) + 4)⁻¹ = 1 / 5 by norm_num] using
      matrixPositiveResolvent_ge_scalar zero_lt_one hcore hcore4
  have hc := star_right_conjugate_le_conjugate hZ (matrixPositiveResolvent (1 / 4) S * F)
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, star_mul,
    hF.isSelfAdjoint.star_eq, hR.star_eq] at hc
  have he : (matrixPositiveResolvent (1 / 4) S * F) * (F * matrixPositiveResolvent (1 / 4) S) =
      matrixPositiveResolvent (1 / 4) S * F * matrixPositiveResolvent (1 / 4) S := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc (matrixPositiveResolvent (1 / 4) S) F F,
      hF.isIdempotentElem.eq]
  rw [he] at hc
  have hh := smul_le_smul_of_nonneg_left hc hlam.le
  rw [matrixProjectionResolventDifference_factor hlam hS hF]
  simpa only [smul_smul, show (1 / 4 : ℝ) * (1 / 5) = 1 / 20 by norm_num,
    Matrix.mul_assoc] using hh

theorem matrixPositiveResolvent_square_ge_lowCut {S : CMatrix d} (hS : 0 ≤ S)
    {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    ((lam + s)⁻¹) ^ 2 • matrixClosedLowSpectralCut S s ≤
      matrixPositiveResolvent lam S * matrixPositiveResolvent lam S := by
  rw [matrixClosedLowSpectralCut, matrixPositiveResolvent,
    ← cfc_const_mul _ _ S (S.finite_real_spectrum.continuousOn _),
    ← cfc_mul _ _ S (S.finite_real_spectrum.continuousOn _) (S.finite_real_spectrum.continuousOn _)]
  apply cfc_mono _ (S.finite_real_spectrum.continuousOn _) (S.finite_real_spectrum.continuousOn _)
  intro t ht
  have ht0 := spectrum_nonneg_of_nonneg hS ht
  by_cases hts : t ≤ s
  · simp only [ht0, hts, and_self, ite_true, mul_one]
    have he : (lam + s)⁻¹ ≤ (lam + t)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le
        (add_pos_of_pos_of_nonneg hlam ht0) (add_le_add_right hts lam)
    have hs0 : 0 ≤ (lam + s)⁻¹ := inv_nonneg.mpr (by linarith)
    simpa only [pow_two] using mul_self_le_mul_self hs0 he
  · simp only [hts, and_false, ite_false, mul_zero]
    exact mul_self_nonneg _

end ThomGame.Analysis

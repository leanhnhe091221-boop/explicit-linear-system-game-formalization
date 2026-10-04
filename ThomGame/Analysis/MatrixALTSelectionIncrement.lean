module

public import ThomGame.Analysis.MatrixALTSelectionPotential

/-!
# Quantitative growth of the ALT selection potential

The actual inverse update and the low spectral cutoff imply the source
coefficient 4/(5(1+kappa/128)^2). A projection with at least half of its
trace in the low spectral space increases the potential by at least
three eighths of its trace.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem matrixTraceReal_projection_mul_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Nat) {F A B : Matrix ι ι ℂ} (hF : IsStarProjection F) (hAB : A ≤ B) :
    matrixTraceReal r (F * A) ≤ matrixTraceReal r (F * B) := by
  have he := star_right_conjugate_le_conjugate hAB F
  simp only [hF.isSelfAdjoint.star_eq] at he
  simpa only [matrixTraceReal_projection_sandwich r hF] using matrixTraceReal_mono r he

variable {d : Nat}

theorem matrixALTSelectionPotential_increment_ge_lowCut {S F : CMatrix d}
    (hS : 0 ≤ S) (hF : IsStarProjection F) (s : ℝ) :
    (1 / 20 : ℝ) * ((1 / 4 + s)⁻¹) ^ 2 * matrixTraceReal d (matrixClosedLowSpectralCut S s * F) ≤
      matrixALTSelectionPotential (S + F) - matrixALTSelectionPotential S := by
  have he := matrixTraceReal_mono d (matrixProjectionResolventDifference_quarter_ge_gram hS hF)
  rw [matrixTraceReal_real_smul, Matrix.mul_assoc,
    matrixTraceReal_mul_comm d (matrixPositiveResolvent (1 / 4) S)
      (F * matrixPositiveResolvent (1 / 4) S), Matrix.mul_assoc,
    ← matrixALTSelectionPotential_increment hS hF] at he
  have hl := matrixTraceReal_projection_mul_mono d hF
    (matrixPositiveResolvent_square_ge_lowCut hS (by norm_num : (0 : ℝ) < 1 / 4) s)
  rw [Matrix.mul_smul, matrixTraceReal_real_smul,
    matrixTraceReal_mul_comm d F (matrixClosedLowSpectralCut S s)] at hl
  have hh := mul_le_mul_of_nonneg_left hl (by norm_num : (0 : ℝ) ≤ 1 / 20)
  rw [← mul_assoc] at hh
  exact hh.trans he

theorem alt_selection_coefficient {κ : ℝ} (hκ : 0 ≤ κ) :
    (1 / 20 : ℝ) * ((1 / 4 + κ / 512)⁻¹) ^ 2 = 4 / (5 * (1 + κ / 128) ^ 2) := by
  have hden : (1 / 4 + κ / 512 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hden' : (1 + κ / 128 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

theorem alt_selection_coefficient_ge {κ : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    (3 / 4 : ℝ) ≤ 4 / (5 * (1 + κ / 128) ^ 2) := by
  have hden : 0 < 5 * (1 + κ / 128) ^ 2 := by positivity
  apply (le_div_iff₀ hden).mpr
  have hs := mul_self_le_mul_self
    (by positivity : 0 ≤ (1 + κ / 128 : ℝ))
    (show (1 + κ / 128 : ℝ) ≤ 129 / 128 by linarith)
  nlinarith only [hs]

theorem matrixALTSelectionPotential_increment_ge_source {S F : CMatrix d}
    (hS : 0 ≤ S) (hF : IsStarProjection F) {κ : ℝ} (hκ : 0 ≤ κ) :
    4 / (5 * (1 + κ / 128) ^ 2) * matrixTraceReal d (matrixClosedLowSpectralCut S (κ / 512) * F) ≤
      matrixALTSelectionPotential (S + F) - matrixALTSelectionPotential S := by
  have he := matrixALTSelectionPotential_increment_ge_lowCut hS hF (κ / 512)
  rwa [alt_selection_coefficient hκ] at he

theorem matrixALTSelectionPotential_increment_ge_trace {S F : CMatrix d}
    (hS : 0 ≤ S) (hF : IsStarProjection F) {κ : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hcover : matrixTraceReal d F / 2 ≤ matrixTraceReal d (matrixClosedLowSpectralCut S (κ / 512) * F)) :
    (3 / 8 : ℝ) * matrixTraceReal d F ≤
      matrixALTSelectionPotential (S + F) - matrixALTSelectionPotential S := by
  have ht := matrixTraceReal_projection_product_nonneg d
    (matrixClosedLowSpectralCut_isStarProjection S (κ / 512)) hF
  calc
    _ ≤ (3 / 4 : ℝ) * matrixTraceReal d (matrixClosedLowSpectralCut S (κ / 512) * F) := by
      linarith only [hcover]
    _ ≤ 4 / (5 * (1 + κ / 128) ^ 2) *
        matrixTraceReal d (matrixClosedLowSpectralCut S (κ / 512) * F) :=
      mul_le_mul_of_nonneg_right (alt_selection_coefficient_ge hκ hκ1) ht
    _ ≤ _ := matrixALTSelectionPotential_increment_ge_source hS hF hκ

end ThomGame.Analysis

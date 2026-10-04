module

public import ThomGame.Analysis.MatrixALTSelectionIncrement

/-!
# Coverage of the corrected projection in ALT Step 1

The selected projection is pulled back through the actual polar factor.
The sharp transport estimate and the 9/16 improvement bound give a
169/256 distance bound to this pullback. The projection-distance identity
then places at least half the corrected trace in the low spectral space.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixPartialIsometry_transport_inverse {W p : Matrix ι ι ℂ}
    (hW : IsStarProjection (W * Wᴴ)) (hp : IsStarProjection p) (hpW : p ≤ W * Wᴴ) :
    W * (Wᴴ * p * W) * Wᴴ = p := by
  calc
    _ = (W * Wᴴ) * p * (W * Wᴴ) := by simp only [Matrix.mul_assoc]
    _ = p := by rw [(hp.le_iff_mul_eq_right hW).mp hpW, (hp.le_iff_mul_eq_left hW).mp hpW]

omit [DecidableEq ι] in
theorem rectHSNorm_ALT_three_point_sq_le (r : Nat) (X Y Z : Matrix ι ι ℂ) (t : ℝ)
    (hXY : rectHSNorm r (X - Y) ^ 2 ≤ (9 / 16 : ℝ) * t)
    (hYZ : rectHSNorm r (Y - Z) ^ 2 ≤ (1 / 256 : ℝ) * t) :
    rectHSNorm r (X - Z) ^ 2 ≤ (169 / 256 : ℝ) * t := by
  have he : X - Z = (X - Y) + (Y - Z) := by abel
  have hh := rectHSNorm_add_le r (X - Y) (Y - Z)
  rw [← he] at hh
  have hs := mul_self_le_mul_self (rectHSNorm_nonneg r (X - Z)) hh
  nlinarith [sq_nonneg (rectHSNorm r (X - Y) - 12 * rectHSNorm r (Y - Z))]

theorem matrixTraceReal_low_overlap_of_distance (r : Nat) {b p F : Matrix ι ι ℂ}
    (hp : IsStarProjection p) (hF : IsStarProjection F) (hpb : p ≤ b)
    (hdist : rectHSNorm r (F - p) ^ 2 ≤ matrixTraceReal r p) :
    matrixTraceReal r F / 2 ≤ matrixTraceReal r (b * F) := by
  have he := rectHSNorm_sub_sq_hermitian r hF.isSelfAdjoint.isHermitian hp.isSelfAdjoint.isHermitian
  rw [hF.isIdempotentElem.eq, hp.isIdempotentElem.eq] at he
  have hm := matrixTraceReal_projection_mul_mono r hF hpb
  rw [matrixTraceReal_mul_comm r F b] at hm
  linarith only [he, hdist, hm]

theorem matrixALTSelection_correction_overlap {d : Nat} {S R p F : CMatrix d}
    (hS : 0 ≤ S) (hR : IsStarProjection R) (hSR : 1 - R ≤ S)
    {κ : ℝ} (hκ : κ ≤ 1) (hp : IsStarProjection p) (hF : IsStarProjection F)
    (hpw : p ≤ matrixRectPolar (R * matrixClosedLowSpectralCut S (κ / 512)) *
      (matrixRectPolar (R * matrixClosedLowSpectralCut S (κ / 512)))ᴴ)
    (hclose : hsNorm (F - p) ^ 2 ≤ (9 / 16 : ℝ) * matrixTraceReal d p) :
    matrixTraceReal d F / 2 ≤ matrixTraceReal d (matrixClosedLowSpectralCut S (κ / 512) * F) := by
  let b := matrixClosedLowSpectralCut S (κ / 512)
  let w := matrixRectPolar (R * b)
  let q := wᴴ * p * w
  have hb : IsStarProjection b := matrixClosedLowSpectralCut_isStarProjection _ _
  have hf : IsStarProjection (w * wᴴ) := matrixRectPolar_final_projection _
  have heps : κ / 512 < 1 := by linarith
  have hleak := matrixClosedLowSpectralCut_leakage hS.isSelfAdjoint hSR (κ / 512)
  have hinit : wᴴ * w = b := matrixProjectionPolar_initial hb hR heps hleak
  have hwstar : (wᴴ)ᴴ * wᴴ = w * wᴴ := by rw [Matrix.conjTranspose_conjTranspose]
  have hq : IsStarProjection q := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      matrixPartialIsometry_transport_projection hf hp hwstar hpw
  have hqb : q ≤ b := by
    have he := matrixProjection_conjugate_le_gram hp wᴴ
    simpa only [Matrix.conjTranspose_conjTranspose, hinit] using he
  have ht : matrixTraceReal d q = matrixTraceReal d p := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      matrixTraceReal_partialIsometry_transport d hf hp hwstar hpw
  have hback : w * q * wᴴ = p := matrixPartialIsometry_transport_inverse hf hp hpw
  have hdist : rectHSNorm d (p - q) ^ 2 ≤ (1 / 256 : ℝ) * matrixTraceReal d p := by
    have he := rectHSNorm_projectionPolar_transport_sq_le d hb hR hq hqb heps hleak
    change rectHSNorm d (w * q * wᴴ - q) ^ 2 ≤ _ at he
    rw [hback, ht] at he
    have hn := mul_le_mul_of_nonneg_right hκ (matrixTraceReal_nonneg d hp.nonneg)
    linarith
  have he := rectHSNorm_ALT_three_point_sq_le d F p q (matrixTraceReal d p) hclose hdist
  apply matrixTraceReal_low_overlap_of_distance d hq hF hqb
  rw [ht]
  exact he.trans (by nlinarith [matrixTraceReal_nonneg d hp.nonneg])

theorem matrixALTSelection_corrected_increment {d : Nat} {S R p F : CMatrix d}
    (hS : 0 ≤ S) (hR : IsStarProjection R) (hSR : 1 - R ≤ S)
    {κ : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (hp : IsStarProjection p) (hF : IsStarProjection F)
    (hpw : p ≤ matrixRectPolar (R * matrixClosedLowSpectralCut S (κ / 512)) *
      (matrixRectPolar (R * matrixClosedLowSpectralCut S (κ / 512)))ᴴ)
    (hclose : hsNorm (F - p) ^ 2 ≤ (9 / 16 : ℝ) * matrixTraceReal d p) :
    (3 / 8 : ℝ) * matrixTraceReal d F ≤
      matrixALTSelectionPotential (S + F) - matrixALTSelectionPotential S :=
  matrixALTSelectionPotential_increment_ge_trace hS hF hκ hκ1
    (matrixALTSelection_correction_overlap hS hR hSR hκ1 hp hF hpw hclose)

end ThomGame.Analysis

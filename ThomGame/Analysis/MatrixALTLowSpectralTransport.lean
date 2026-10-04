module

public import ThomGame.Analysis.MatrixProjectionTransportDistance
public import ThomGame.Analysis.MatrixClosedLowSpectralCut

/-!
# ALT (4.6) for the actual low spectral projection

The spectral projection is constructed from S. Its leakage into 1-R
is controlled by S >= 1-R, and the actual polar factor of Rb has both
distance and boundary-energy bounds with the constants in the source.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat}

theorem matrixClosedLowSpectralCut_compression_le {S : CMatrix d} (hS : IsSelfAdjoint S) (s : ℝ) :
    matrixClosedLowSpectralCut S s * S * matrixClosedLowSpectralCut S s ≤
      s • matrixClosedLowSpectralCut S s := by
  have hid : cfc (fun t : ℝ => t) S = S := cfc_id' ℝ S hS
  have he : matrixClosedLowSpectralCut S s * S * matrixClosedLowSpectralCut S s =
      cfc (fun t : ℝ => (if 0 ≤ t ∧ t ≤ s then 1 else 0) * t *
        (if 0 ≤ t ∧ t ≤ s then 1 else 0)) S := by
    calc
      _ = matrixClosedLowSpectralCut S s * cfc (fun t : ℝ => t) S *
          matrixClosedLowSpectralCut S s := by rw [hid]
      _ = _ := by
        rw [matrixClosedLowSpectralCut,
          ← cfc_mul _ _ S (S.finite_real_spectrum.continuousOn _) (S.finite_real_spectrum.continuousOn _),
          ← cfc_mul _ _ S (S.finite_real_spectrum.continuousOn _) (S.finite_real_spectrum.continuousOn _)]
  rw [he, matrixClosedLowSpectralCut,
    ← cfc_const_mul s _ S (S.finite_real_spectrum.continuousOn _)]
  apply cfc_mono _ (S.finite_real_spectrum.continuousOn _) (S.finite_real_spectrum.continuousOn _)
  intro t _
  split_ifs with ht
  · simpa only [one_mul, mul_one] using ht.2
  · simp

theorem matrixClosedLowSpectralCut_leakage {S R : CMatrix d} (hS : IsSelfAdjoint S)
    (hSR : 1 - R ≤ S) (s : ℝ) :
    matrixClosedLowSpectralCut S s * (1 - R) * matrixClosedLowSpectralCut S s ≤
      s • matrixClosedLowSpectralCut S s := by
  have hp := matrixClosedLowSpectralCut_isStarProjection S s
  have he := star_right_conjugate_le_conjugate hSR (matrixClosedLowSpectralCut S s)
  simp only [hp.isSelfAdjoint.star_eq] at he
  exact he.trans (matrixClosedLowSpectralCut_compression_le hS s)

theorem matrixALT_lowSpectral_polar_transport [NeZero h] (U : Fin h → UnitaryMatrix d)
    {S R : CMatrix d} (hS : 0 ≤ S) (hR : IsStarProjection R) (hSR : 1 - R ≤ S)
    {κ : ℝ} (hκ : κ ≤ 1) :
    let b := matrixClosedLowSpectralCut S (κ / 512)
    let w := matrixRectPolar (R * b)
    wᴴ * w = b ∧ w * wᴴ ≤ R ∧ b * w * b = matrixRectAbs (R * b) ∧
      ∀ p : CMatrix d, IsStarProjection p → p ≤ b →
        IsStarProjection (w * p * wᴴ) ∧ w * p * wᴴ ≤ R ∧
        matrixTraceReal d (w * p * wᴴ) = matrixTraceReal d p ∧
        (w * p * wᴴ).rank = p.rank ∧
        hsNorm (w * p * wᴴ - p) ^ 2 ≤ κ / 256 * matrixTraceReal d p ∧
        matrixCoordinateEnergy U (w * p * wᴴ) ≤
          2 * matrixCoordinateEnergy U p + κ / 128 * matrixTraceReal d p := by
  dsimp only
  let b := matrixClosedLowSpectralCut S (κ / 512)
  let w := matrixRectPolar (R * b)
  have hb : IsStarProjection b := matrixClosedLowSpectralCut_isStarProjection _ _
  have heps : κ / 512 < 1 := by linarith
  have hleak := matrixClosedLowSpectralCut_leakage hS.isSelfAdjoint hSR (κ / 512)
  have hinit : wᴴ * w = b := matrixProjectionPolar_initial hb hR heps hleak
  have hfinal : w * wᴴ ≤ R := matrixProjectionPolar_final_le hR
  refine ⟨hinit, hfinal, matrixProjectionPolar_compression hb hR, ?_⟩
  intro p hp hpb
  refine ⟨matrixPartialIsometry_transport_projection hb hp hinit hpb,
    (matrixProjection_conjugate_le_gram hp w).trans hfinal,
    matrixTraceReal_partialIsometry_transport d hb hp hinit hpb,
    matrixPartialIsometry_transport_rank hb hp hinit hpb, ?_, ?_⟩
  · have he := rectHSNorm_projectionPolar_transport_sq_le d hb hR hp hpb heps hleak
    simpa only [rectHSNorm_eq_hsNorm, show 2 * (κ / 512) = κ / 256 by ring] using he
  · have he := matrixCoordinateEnergy_projectionPolar_transport_le U hb hR hp hpb heps hleak
    simpa only [show 4 * (κ / 512) = κ / 128 by ring] using he

end ThomGame.Analysis

module

public import ThomGame.Analysis.MatrixCompressionRounding
public import ThomGame.Analysis.MatrixALTOrthogonalSelection

/-!
# ALT expansion after compression and rounding

Minimum rank is applied to the actual closed half cut. A half-rank
subprojection of a corrected initial support transports to a projection
of strictly smaller rank than the original selected candidate.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat} [NeZero h]

theorem matrixALTSelection_compression_expansion (U : Fin h → UnitaryMatrix d)
    {S R P : CMatrix d} (hS : 0 ≤ S) (hR : IsStarProjection R) (hSR : 1 - R ≤ S)
    {κ : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hmin : ∀ q, MatrixALTSelectionCandidate U κ R S q → P.rank ≤ q.rank)
    {y : CMatrix d} (hy : IsStarProjection y) (hrank : y.rank < P.rank) :
    κ / 512 * matrixTraceReal d y -
        3 * matrixTraceReal d ((1 - matrixClosedLowSpectralCut S (κ / 512)) * y) ≤
      matrixCoordinateEnergy U y := by
  let b := matrixClosedLowSpectralCut S (κ / 512)
  let z := matrixHalfProjection (b * y * b)
  have hb : IsStarProjection b := matrixClosedLowSpectralCut_isStarProjection S (κ / 512)
  have hz : IsStarProjection z := matrixHalfProjection_isStarProjection _
  have hzb : z ≤ b := matrixHalfProjection_compression_le hb hy
  have hzr : z.rank < P.rank := (matrixHalfProjection_compression_rank_le hb hy).trans_lt hrank
  have he := matrixALTSelection_minimal_rank_expansion U hS hR hSR hκ1 hmin hz hzb hzr
  have hd := matrixHalfProjection_compression_distance_le d hb hy
  have ht := matrixHalfProjection_compression_trace_ge d hb hy
  have hp := matrixIntertwiningEnergy_perturb_le d U U z y
  simp only [matrixIntertwiningEnergy_eq_coordinate, rectHSNorm_sub_comm d z y] at hp
  have hm := mul_le_mul_of_nonneg_left ht (div_nonneg hκ (by norm_num : (0 : ℝ) ≤ 256))
  have hl := matrixTraceReal_projection_product_nonneg d hb.one_sub hy
  have hκl := mul_le_mul_of_nonneg_right hκ1 hl
  change rectHSNorm d (y - z) ^ 2 ≤ _ at hd
  change κ / 256 * (matrixTraceReal d y - 2 * matrixTraceReal d ((1 - b) * y)) ≤
    κ / 256 * matrixTraceReal d z at hm
  change κ / 512 * matrixTraceReal d y - 3 * matrixTraceReal d ((1 - b) * y) ≤ _
  nlinarith only [he, hd, hp, hm, hl, hκl]

omit [NeZero h] in
theorem MatrixALTOrthogonalSelection.half_rank_lt_selected (U : Fin h → UnitaryMatrix d)
    {κ α η : ℝ} {R : CMatrix d} (sel : MatrixALTOrthogonalSelection U κ α η R)
    (i : Fin sel.n) {q : CMatrix d} (hqrank : 2 * q.rank ≤ ((sel.V i)ᴴ * sel.V i).rank) :
    q.rank < (sel.P i).rank := by
  have hle := sel.rank_le i
  have hgap := sel.rank_gap i
  omega

theorem MatrixALTOrthogonalSelection.transported_half_expansion (U : Fin h → UnitaryMatrix d)
    {κ α η : ℝ} {R : CMatrix d} (sel : MatrixALTOrthogonalSelection U κ α η R)
    (hR : IsStarProjection R) (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (i : Fin sel.n) {q : CMatrix d} (hq : IsStarProjection q)
    (hqP : q ≤ (sel.V i)ᴴ * sel.V i) (hqrank : 2 * q.rank ≤ ((sel.V i)ᴴ * sel.V i).rank) :
    κ / 512 * matrixTraceReal d q -
        3 * matrixTraceReal d ((1 - matrixClosedLowSpectralCut (sel.S i) (κ / 512)) *
          (sel.V i * (sel.V i)ᴴ)) ≤
      matrixCoordinateEnergy U (sel.V i * q * (sel.V i)ᴴ) := by
  let y := sel.V i * q * (sel.V i)ᴴ
  have hy : IsStarProjection y := matrixPartialIsometry_transport_projection (sel.initial_projection i) hq rfl hqP
  have hr : y.rank = q.rank := matrixPartialIsometry_transport_rank (sel.initial_projection i) hq rfl hqP
  have hlt : y.rank < (sel.P i).rank := by
    rw [hr]
    exact sel.half_rank_lt_selected U i hqrank
  have hS : 0 ≤ sel.S i := hR.one_sub.nonneg.trans (sel.state_ge i)
  have he := matrixALTSelection_compression_expansion U hS hR (sel.state_ge i) hκ hκ1
    (sel.selection i).2.1 hy hlt
  have htrace : matrixTraceReal d y = matrixTraceReal d q :=
    matrixTraceReal_partialIsometry_transport d (sel.initial_projection i) hq rfl hqP
  have hl := matrixTraceReal_projection_mul_mono d
    (matrixClosedLowSpectralCut_isStarProjection (sel.S i) (κ / 512)).one_sub
      (matrixProjection_conjugate_le_gram hq (sel.V i))
  rw [htrace] at he
  change κ / 512 * matrixTraceReal d q - 3 * _ ≤ matrixCoordinateEnergy U y
  linarith only [he, hl]

end ThomGame.Analysis

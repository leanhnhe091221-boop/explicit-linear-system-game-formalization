module

public import ThomGame.Analysis.FiniteNoDriftAnchor
public import ThomGame.Analysis.MatrixThomScalarTransport

/-! Finite scalar concentration and reverse inclusion in the original dimension. -/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}
    (S : MatrixThomSpectralData A B D ε)

theorem MatrixThomSpectralData.finite_inverse_cut_dimension_sqrt_bound
    (hε : 0 ≤ ε) (hsmall : ε < 1 / 2) :
    Real.sqrt ((d : ℝ) / S.cut.rank) ≤ 2 := by
  have hdim := (neg_le_abs ((S.cut.rank : ℝ) / d - 1)).trans S.dimension_error
  have hr : (1 / 2 : ℝ) ≤ (S.cut.rank : ℝ) / d := by nlinarith
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hm : (0 : ℝ) < S.cut.rank := Nat.cast_pos.mpr (S.cut_rank_pos hε hsmall)
  have hc := (le_div_iff₀ hd).mp hr
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by norm_num, (div_le_iff₀ hm).mpr ?_⟩
  nlinarith

theorem MatrixThomSpectralData.finite_frame_support_distance (hε : 0 ≤ ε) :
    rectHSNorm d (S.stableSourceFrame * S.stableSourceFrameᴴ -
      S.stableTargetFrame * S.stableTargetFrameᴴ) ≤ 4 * ε := by
  have ha := rectHSNorm_projection_sq d
    (matrixFrame_final_projection S.stableSourceFrame S.stableSourceFrame_initial).one_sub
  have hb := rectHSNorm_projection_sq d
    (matrixFrame_final_projection S.stableTargetFrame S.stableTargetFrame_initial).one_sub
  have hsa : rectHSNorm d (1 - S.stableSourceFrame * S.stableSourceFrameᴴ) ≤ 2 * ε := by
    nlinarith [S.stableSourceFrame_complement_trace,
      rectHSNorm_nonneg d (1 - S.stableSourceFrame * S.stableSourceFrameᴴ)]
  have hsb : rectHSNorm d (1 - S.stableTargetFrame * S.stableTargetFrameᴴ) ≤ 2 * ε := by
    nlinarith [S.stableTargetFrame_complement_trace,
      rectHSNorm_nonneg d (1 - S.stableTargetFrame * S.stableTargetFrameᴴ), sq_nonneg ε]
  have ht := rectHSNorm_sub_triangle d (S.stableSourceFrame * S.stableSourceFrameᴴ)
    1 (S.stableTargetFrame * S.stableTargetFrameᴴ)
  rw [rectHSNorm_sub_comm d (S.stableSourceFrame * S.stableSourceFrameᴴ) 1] at ht
  linarith

theorem MatrixThomSpectralData.finite_scalar_concentration_transfer
    (hε : 0 ≤ ε) (hsmall : ε < 1 / 2)
    (X : CMatrix d) (Y : CMatrix S.cut.rank) {a t : ℝ}
    (hX : hsNorm (X - (1 / 2 : ℂ) • 1) ≤ a)
    (hXY : rectHSNorm d (matrixFrameLift S.stableSourceFrame X -
      matrixFrameLift S.stableTargetFrame Y) ≤ t) :
    hsNorm (Y - (1 / 2 : ℂ) • 1) ≤ 2 * (t + a + 2 * ε) := by
  have hiden : matrixFrameLift S.stableTargetFrame (Y - (1 / 2 : ℂ) • 1) =
      (matrixFrameLift S.stableTargetFrame Y - matrixFrameLift S.stableSourceFrame X) +
      matrixFrameLift S.stableSourceFrame (X - (1 / 2 : ℂ) • 1) +
      (1 / 2 : ℂ) • (S.stableSourceFrame * S.stableSourceFrameᴴ -
        S.stableTargetFrame * S.stableTargetFrameᴴ) := by
    simp only [matrixFrameLift_sub, matrixFrameLift_smul, matrixFrameLift_one, smul_sub]
    abel
  have ha := rectHSNorm_add_le d
    (matrixFrameLift S.stableTargetFrame Y - matrixFrameLift S.stableSourceFrame X +
      matrixFrameLift S.stableSourceFrame (X - (1 / 2 : ℂ) • 1))
    ((1 / 2 : ℂ) • (S.stableSourceFrame * S.stableSourceFrameᴴ -
      S.stableTargetFrame * S.stableTargetFrameᴴ))
  have hb := rectHSNorm_add_le d
    (matrixFrameLift S.stableTargetFrame Y - matrixFrameLift S.stableSourceFrame X)
    (matrixFrameLift S.stableSourceFrame (X - (1 / 2 : ℂ) • 1))
  have hnormhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [← hiden, matrixFrameLift_hsNorm d S.stableTargetFrame_initial,
    rectHSNorm_smul, hnormhalf] at ha
  rw [rectHSNorm_sub_comm d (matrixFrameLift S.stableTargetFrame Y),
    matrixFrameLift_hsNorm d S.stableSourceFrame_initial, rectHSNorm_eq_hsNorm] at hb
  have ht : rectHSNorm d (Y - (1 / 2 : ℂ) • 1) ≤ t + a + 2 * ε := by
    linarith [S.finite_frame_support_distance hε]
  have ht0 : 0 ≤ t + a + 2 * ε := (rectHSNorm_nonneg _ _).trans ht
  rw [← rectHSNorm_eq_hsNorm, rectHSNorm_rescale (S.cut_rank_pos hε hsmall) (NeZero.pos d)]
  exact (mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg _)).trans
    (mul_le_mul_of_nonneg_right (S.finite_inverse_cut_dimension_sqrt_bound hε hsmall) ht0)

end ThomGame.Analysis

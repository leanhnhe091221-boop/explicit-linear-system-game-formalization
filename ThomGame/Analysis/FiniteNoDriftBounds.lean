module

public import ThomGame.Analysis.MatrixThomBoundedScaleStableBounds
public import ThomGame.Analysis.MatrixThomOrderedTransport
public import ThomGame.Analysis.MatrixThomScaleConcentration
public import ThomGame.Analysis.MatrixThomReverseTransfer

/-! Finite bounds for the existing Thom correction, without changing its construction. -/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}
    (S : MatrixThomSpectralData A B D ε)

theorem finiteNoDrift_sqrt_two_le_two : Real.sqrt 2 ≤ 2 := by
  apply (Real.sqrt_le_iff).mpr
  norm_num

theorem finiteNoDrift_norm_le_of_sq {a c t : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (ht : 0 ≤ t) (hsq : a ^ 2 ≤ c ^ 2 * t ^ 2) : a ≤ c * t := by
  nlinarith [mul_nonneg hc ht]

theorem MatrixThomSpectralData.finite_sourceBoundedScale_bound
    (P : MatrixSubalgebraStarBlocks B)
    (hDB : D ≤ B) (F : MatrixSubalgebraStarBlocks D)
    (s : Fin F.count → ℝ) (hs : ∀ i, 0 < s i)
    (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    rectHSNorm d (matrixFrameLift S.stableSourceFrame
        (matrixBoundedScale (matrixSubalgebraScale B P) (matrixStarBlockScalar D F s)) -
      matrixFrameLift S.stableTargetFrame
        (matrixBoundedScale (S.retainedSourceScale P) (S.commonPositiveScalar hDB F s))) ≤ 17 * ε := by
  have hb := S.sourceBoundedScale_stable_bound P hDB F s hs hε hBA
  have he := matrixThom_retainedSourceScale_error S P hDB F s hs hε hBA
  have hn := rectHSNorm_nonneg d
    (matrixBoundedScale (S.retainedSourceScale P) (S.commonPositiveScalar hDB F s) -
      matrixBoundedScale (S.rawSourceScale P) (S.commonPositiveScalar hDB F s))
  have ht : rectHSNorm d
      (matrixBoundedScale (S.retainedSourceScale P) (S.commonPositiveScalar hDB F s) -
        matrixBoundedScale (S.rawSourceScale P) (S.commonPositiveScalar hDB F s)) ≤ 5 * ε := by
    nlinarith [sq_nonneg ε]
  have hroot := mul_le_mul_of_nonneg_right finiteNoDrift_sqrt_two_le_two hε
  nlinarith

theorem MatrixThomSpectralData.finite_targetBoundedScale_bound
    (R : MatrixSubalgebraStarBlocks (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))))
    (hDB : D ≤ B) (F : MatrixSubalgebraStarBlocks D)
    (s : Fin F.count → ℝ) (hs : ∀ i, 0 < s i)
    (hDA : D ≤ A) (hε : 0 ≤ ε) :
    rectHSNorm d (matrixFrameLift S.stableSourceFrame
        (matrixBoundedScale (matrixSubalgebraComplementaryScale A R) (matrixStarBlockScalar D F s)) -
      matrixFrameLift S.stableTargetFrame
        (matrixBoundedScale (S.retainedTargetScale R) (S.commonPositiveScalar hDB F s))) ≤ 9 * ε := by
  have hb := S.targetBoundedScale_stable_bound R hDB F s hs hDA hε
  have he := matrixThom_retainedTargetScale_error S R hDB F s hs
  have hn := rectHSNorm_nonneg d
    (matrixBoundedScale (S.rawTargetScale R) (S.commonPositiveScalar hDB F s) -
      matrixBoundedScale (S.retainedTargetScale R) (S.commonPositiveScalar hDB F s))
  have ht : rectHSNorm d
      (matrixBoundedScale (S.rawTargetScale R) (S.commonPositiveScalar hDB F s) -
        matrixBoundedScale (S.retainedTargetScale R) (S.commonPositiveScalar hDB F s)) ≤ 3 * ε := by
    nlinarith [sq_nonneg ε]
  have hroot := mul_le_mul_of_nonneg_right finiteNoDrift_sqrt_two_le_two hε
  nlinarith

theorem MatrixThomSpectralData.finite_stable_dimension_sqrt_bound
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 2) :
    Real.sqrt ((S.stableDim : ℝ) / d) ≤ 2 := by
  have hr := (le_abs_self ((S.stableDim : ℝ) / d - 1)).trans S.stableDim_ratio_bound
  apply (Real.sqrt_le_iff).mpr
  constructor
  · norm_num
  · nlinarith

theorem MatrixThomSpectralData.finite_cut_dimension_sqrt_bound
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 2) :
    Real.sqrt ((S.cut.rank : ℝ) / d) ≤ 2 := by
  have hr := (le_abs_self ((S.cut.rank : ℝ) / d - 1)).trans S.dimension_error
  apply (Real.sqrt_le_iff).mpr
  constructor
  · norm_num
  · nlinarith

theorem MatrixThomSpectralData.finite_ordered_transport
    (a b : CMatrix d) (x y : CMatrix S.cut.rank)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1)
    (htrace : a.trace = b.trace) (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 2)
    {e : ℝ} (he : rectHSNorm d (matrixFrameLift S.stableSourceFrame a -
        matrixFrameLift S.stableTargetFrame x) +
      rectHSNorm d (matrixFrameLift S.stableSourceFrame b -
        matrixFrameLift S.stableTargetFrame y) ≤ e) :
    hsNorm (a - b) ≤ 2 * (e + Real.sqrt e) := by
  have hlarge := (NeZero.pos d).trans_le S.le_stableDim
  have hdim := S.finite_stable_dimension_sqrt_bound hε hsmall
  have h₁ := rectHSNorm_antitone_denominator (NeZero.pos d) S.le_stableDim
    (matrixFrameLift S.stableSourceFrame a - matrixFrameLift S.stableTargetFrame x)
  have h₂ := rectHSNorm_antitone_denominator (NeZero.pos d) S.le_stableDim
    (matrixFrameLift S.stableSourceFrame b - matrixFrameLift S.stableTargetFrame y)
  have hb := matrixFrame_ordered_equalTrace_distance S.stableSourceFrame S.stableTargetFrame
    S.stableSourceFrame_initial S.stableTargetFrame_initial a b x y hx hxy hy htrace
  have he' := (add_le_add h₁ h₂).trans he
  have hs := Real.sqrt_le_sqrt he'
  have hb' : rectHSNorm S.stableDim (a - b) ≤ e + Real.sqrt e := by linarith
  have he0 : 0 ≤ e := le_trans (add_nonneg (rectHSNorm_nonneg _ _) (rectHSNorm_nonneg _ _)) he
  rw [← rectHSNorm_eq_hsNorm, rectHSNorm_rescale (NeZero.pos d) hlarge]
  exact (mul_le_mul_of_nonneg_left hb' (Real.sqrt_nonneg _)).trans
    (mul_le_mul_of_nonneg_right hdim (add_nonneg he0 (Real.sqrt_nonneg _)))

theorem MatrixThomSpectralData.finite_reverse_transfer
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 2) (hBA : MatrixNearInclusion B A ε)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hrev : MatrixNearInclusion S.correctedTargetAlgebra S.correctedSourceAlgebra δ) :
    MatrixNearInclusion A B (14 * ε + 2 * δ) := by
  have hb := S.reverse_nearInclusion_transfer hε hBA hrev
  have hroot := mul_le_mul_of_nonneg_right finiteNoDrift_sqrt_two_le_two hε
  have hdim := mul_le_mul_of_nonneg_right (S.finite_cut_dimension_sqrt_bound hε hsmall) hδ
  intro X hXA hX
  obtain ⟨Y, hY, hXY⟩ := hb X hXA hX
  exact ⟨Y, hY, hXY.trans (by nlinarith)⟩

end ThomGame.Analysis

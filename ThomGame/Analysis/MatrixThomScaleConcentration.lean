module

public import ThomGame.Analysis.MatrixThomBoundedScaleOrder
public import ThomGame.Analysis.MatrixInclusionScaleConcentrationLimits

/-!
# Concentration estimates for the same actual Thom correction

The ratio uses the actual retained scales, and concentration is measured
with the corrected dimension. The final limit theorems state explicitly
the concentration input still needed from the ultraproduct anchor.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

section Finite

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}
    (S : MatrixThomSpectralData A B D ε)
    (P : MatrixSubalgebraStarBlocks B)
    (R : MatrixSubalgebraStarBlocks (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))))

noncomputable def MatrixThomSpectralData.retainedScaleRatio : CMatrix S.cut.rank :=
  S.retainedTargetScale R * (S.retainedSourceScale P)⁻¹

theorem MatrixThomSpectralData.retainedScaleRatio_one_le : 1 ≤ S.retainedScaleRatio P R :=
  matrixInclusionScaleRatio_one_le _ _ _ _ (S.retainedRange_le P R)

theorem MatrixThomSpectralData.retainedScaleRatio_inverse :
    (S.retainedScaleRatio P R)⁻¹ = (S.retainedTargetScale R)⁻¹ * S.retainedSourceScale P :=
  matrixInclusionScaleRatio_inverse _ _ _ _ (S.retainedRange_le P R)

theorem MatrixThomSpectralData.retainedScaleRatio_trace_defect_nonneg (r : Nat) :
    0 ≤ matrixTraceReal r (1 - (S.retainedScaleRatio P R)⁻¹) :=
  matrixInclusionScaleRatio_trace_defect_nonneg _ _ _ _ (S.retainedRange_le P R) r

variable (hDB : D ≤ B) (F : MatrixSubalgebraStarBlocks D)
    (s : Fin F.count → ℝ) (hs : ∀ i, 0 < s i)

noncomputable def MatrixThomSpectralData.retainedScaleConcentration : ℝ :=
  rectHSNorm S.cut.rank
    (matrixBoundedScale (S.retainedSourceScale P) (S.commonPositiveScalar hDB F s) - (1 / 2 : ℂ) • 1) +
  rectHSNorm S.cut.rank
    (matrixBoundedScale (S.retainedTargetScale R) (S.commonPositiveScalar hDB F s) - (1 / 2 : ℂ) • 1)

theorem MatrixThomSpectralData.retainedScaleConcentration_nonneg :
    0 ≤ S.retainedScaleConcentration P R hDB F s :=
  add_nonneg (rectHSNorm_nonneg _ _) (rectHSNorm_nonneg _ _)

include hs in
theorem matrixThom_retainedScaleRatio_defect_norm (r : Nat) :
    rectHSNorm r (1 - (S.retainedScaleRatio P R)⁻¹) ≤
      8 * (rectHSNorm r
        (matrixBoundedScale (S.retainedSourceScale P) (S.commonPositiveScalar hDB F s) - (1 / 2 : ℂ) • 1) +
      rectHSNorm r
        (matrixBoundedScale (S.retainedTargetScale R) (S.commonPositiveScalar hDB F s) - (1 / 2 : ℂ) • 1)) :=
  matrixInclusionScaleRatio_defect_norm _ _ _ _ (S.retainedRange_le P R) r _
    (S.commonPositiveScalar_posDef hDB F s hs) (S.commonPositiveScalar_mem_retainedSource P hDB F s)

include hs in
theorem matrixThom_retainedScaleRatio_defect_trace :
    matrixTraceReal S.cut.rank (1 - (S.retainedScaleRatio P R)⁻¹) ≤
      8 * S.retainedScaleConcentration P R hDB F s :=
  matrixInclusionScaleRatio_defect_trace _ _ _ _ (S.retainedRange_le P R) _
    (S.commonPositiveScalar_posDef hDB F s hs) (S.commonPositiveScalar_mem_retainedSource P hDB F s)

include hs in
theorem matrixThom_reverseInclusion_center_error [NeZero S.cut.rank] :
    matrixNearInclusionError S.correctedTargetAlgebra S.correctedSourceAlgebra ≤
      4 * Real.sqrt (S.retainedScaleConcentration P R hDB F s) := by
  obtain ⟨_, hsource, _, htarget⟩ := matrixThom_star_block_algebras S P R
  rw [hsource, htarget]
  exact matrixReverseInclusion_center_error _ _ _ _ (S.retainedRange_le P R) _
    (S.commonPositiveScalar_posDef hDB F s hs) (S.commonPositiveScalar_mem_retainedSource P hDB F s)

include hs in
theorem matrixThom_reverseInclusion_center_near [NeZero S.cut.rank] :
    MatrixNearInclusion S.correctedTargetAlgebra S.correctedSourceAlgebra
      (4 * Real.sqrt (S.retainedScaleConcentration P R hDB F s)) :=
  (matrixNearInclusion_iff_error_le _ _ _).mpr
    (matrixThom_reverseInclusion_center_error S P R hDB F s hs)

end Finite

section Limits

variable {ι : Type*} (dims : ι → Nat) [∀ n, NeZero (dims n)]
    {A B D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n))} {ε : ι → ℝ}
    (S : (n : ι) → MatrixThomSpectralData (A n) (B n) (D n) (ε n))
    (P : (n : ι) → MatrixSubalgebraStarBlocks (B n))
    (R : (n : ι) → MatrixSubalgebraStarBlocks
      (StarSubalgebra.centralizer ℂ (A n : Set (CMatrix (dims n)))))
    (hDB : ∀ n, D n ≤ B n) (F : (n : ι) → MatrixSubalgebraStarBlocks (D n))
    (s : (n : ι) → Fin (F n).count → ℝ) (hs : ∀ n i, 0 < s n i)

include hs in
theorem matrixThom_retainedScaleRatio_defect_trace_tendsto (L : Filter ι)
    (hc : Tendsto (fun n => (S n).retainedScaleConcentration (P n) (R n) (hDB n) (F n) (s n)) L (𝓝 0)) :
    Tendsto (fun n => matrixTraceReal (S n).cut.rank (1 - ((S n).retainedScaleRatio (P n) (R n))⁻¹))
      L (𝓝 0) := by
  have hb := (tendsto_const_nhds (x := (8 : ℝ))).mul hc
  exact squeeze_zero (fun n => (S n).retainedScaleRatio_trace_defect_nonneg (P n) (R n) _)
    (fun n => matrixThom_retainedScaleRatio_defect_trace (S n) (P n) (R n) (hDB n) (F n) (s n) (hs n))
    (by simpa only [mul_zero] using hb)

include hs in
theorem matrixThom_reverseInclusion_center_tendsto [∀ n, NeZero (S n).cut.rank] (L : Filter ι)
    (hc : Tendsto (fun n => (S n).retainedScaleConcentration (P n) (R n) (hDB n) (F n) (s n)) L (𝓝 0)) :
    Tendsto (fun n => matrixNearInclusionError (S n).correctedTargetAlgebra (S n).correctedSourceAlgebra)
      L (𝓝 0) := by
  have hb := (tendsto_const_nhds (x := (4 : ℝ))).mul hc.sqrt
  exact squeeze_zero (fun n => matrixNearInclusionError_nonneg _ _)
    (fun n => matrixThom_reverseInclusion_center_error (S n) (P n) (R n) (hDB n) (F n) (s n) (hs n))
    (by simpa only [Real.sqrt_zero, mul_zero] using hb)

end Limits

end ThomGame.Analysis

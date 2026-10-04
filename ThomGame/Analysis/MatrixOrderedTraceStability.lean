module

public import ThomGame.Analysis.MatrixInclusionScaleDefectBound
public import ThomGame.Analysis.MatrixFrameStabilizationBounds
public import ThomGame.Analysis.MatrixProjectionNearUnitary

/-!
# Stability of ordered contractions with equal-trace approximants

If two equal-trace matrices are close to an ordered pair of positive
contractions, their distance is at most e + sqrt(e). This finite estimate
implements the faithful-trace no-drift step without changing dimensions.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem matrixPositiveContraction_hsNorm_sq_le_trace {d : Nat} (r : Nat) (X : CMatrix d)
    (hX0 : 0 ≤ X) (hX1 : X ≤ 1) : rectHSNorm r X ^ 2 ≤ matrixTraceReal r X := by
  have hp := Commute.mul_nonneg hX0 (sub_nonneg.mpr hX1)
    ((Commute.one_right X).sub_right (Commute.refl X))
  have hsq : X * X ≤ X := by
    rw [mul_sub, mul_one] at hp
    exact sub_nonneg.mp hp
  have he := matrixTraceReal_mono r hsq
  rw [← matrixTraceReal_gram, hX0.isSelfAdjoint.isHermitian.eq]
  exact he

theorem matrixFrameLift_nonneg {d m : Nat} (F : Matrix (Fin m) (Fin d) ℂ)
    {X : CMatrix d} (hX : 0 ≤ X) : 0 ≤ matrixFrameLift F X :=
  ((Matrix.nonneg_iff_posSemidef.mp hX).mul_mul_conjTranspose_same F).nonneg

theorem matrixFrameLift_mono {d m : Nat} (F : Matrix (Fin m) (Fin d) ℂ)
    {X Y : CMatrix d} (hXY : X ≤ Y) : matrixFrameLift F X ≤ matrixFrameLift F Y := by
  have h := matrixFrameLift_nonneg F (sub_nonneg.mpr hXY)
  rw [matrixFrameLift_sub] at h
  exact sub_nonneg.mp h

theorem matrixFrameLift_le_one {d m : Nat} (F : Matrix (Fin m) (Fin d) ℂ)
    (hF : Fᴴ * F = 1) {X : CMatrix d} (hX : X ≤ 1) : matrixFrameLift F X ≤ 1 := by
  have h := matrixFrameLift_mono F hX
  rw [matrixFrameLift_one] at h
  exact h.trans (matrixFrame_final_projection F hF).le_one

theorem matrixOrdered_equalTrace_distance {d : Nat} (a b x y : CMatrix d)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1)
    (htrace : matrixTraceReal d a = matrixTraceReal d b) :
    rectHSNorm d (a - b) ≤
      (rectHSNorm d (a - x) + rectHSNorm d (b - y)) +
        Real.sqrt (rectHSNorm d (a - x) + rectHSNorm d (b - y)) := by
  have hD0 : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hD1 : y - x ≤ 1 := (sub_le_self _ hx).trans hy
  have hsq := matrixPositiveContraction_hsNorm_sq_le_trace d (y - x) hD0 hD1
  have htr : matrixTraceReal d (y - x) = matrixTraceReal d (y - b) + matrixTraceReal d (a - x) := by
    simp only [matrixTraceReal_sub, htrace]
    ring
  have ht : matrixTraceReal d (y - x) ≤ rectHSNorm d (a - x) + rectHSNorm d (b - y) := by
    rw [htr]
    have h1 := matrixTraceReal_self_le_rectHSNorm (y - b)
    rw [rectHSNorm_sub_comm d y b] at h1
    linarith [matrixTraceReal_self_le_rectHSNorm (a - x)]
  have hn : rectHSNorm d (x - y) ≤ Real.sqrt (rectHSNorm d (a - x) + rectHSNorm d (b - y)) := by
    rw [rectHSNorm_sub_comm d x y]
    exact (Real.le_sqrt (rectHSNorm_nonneg _ _)
      (add_nonneg (rectHSNorm_nonneg _ _) (rectHSNorm_nonneg _ _))).mpr (hsq.trans ht)
  have he := rectHSNorm_sub_triangle_three d a x y b
  rw [rectHSNorm_sub_comm d y b] at he
  linarith

theorem matrixFrame_ordered_equalTrace_distance {d k m : Nat}
    (F : Matrix (Fin m) (Fin d) ℂ) (G : Matrix (Fin m) (Fin k) ℂ)
    (hF : Fᴴ * F = 1) (hG : Gᴴ * G = 1) (a b : CMatrix d) (x y : CMatrix k)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) (htrace : a.trace = b.trace) :
    rectHSNorm m (a - b) ≤
      (rectHSNorm m (matrixFrameLift F a - matrixFrameLift G x) +
        rectHSNorm m (matrixFrameLift F b - matrixFrameLift G y)) +
      Real.sqrt (rectHSNorm m (matrixFrameLift F a - matrixFrameLift G x) +
        rectHSNorm m (matrixFrameLift F b - matrixFrameLift G y)) := by
  have he := matrixOrdered_equalTrace_distance (matrixFrameLift F a) (matrixFrameLift F b)
    (matrixFrameLift G x) (matrixFrameLift G y)
    (matrixFrameLift_nonneg G hx) (matrixFrameLift_mono G hxy) (matrixFrameLift_le_one G hG hy)
    (by rw [matrixFrameLift_trace m hF, matrixFrameLift_trace m hF, matrixTraceReal, matrixTraceReal, htrace])
  rw [← matrixFrameLift_sub, matrixFrameLift_hsNorm m hF] at he
  exact he

end ThomGame.Analysis

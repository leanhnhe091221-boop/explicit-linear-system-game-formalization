module

public import ThomGame.Analysis.MatrixIsometryCutPolar
public import ThomGame.Analysis.RectangularOperatorBounds

/-!
# Thom's uniform intertwining estimate for the actual polar correction

The same polar factor which preserves the common algebras has error
at most (4 + sqrt 2) epsilon on the whole contraction ball of B.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d m : Nat}

theorem matrixRectangular_intertwining_perturbation (r : Nat)
    (R : CMatrix m) (X : CMatrix d) (V W : Matrix (Fin m) (Fin d) ℂ)
    (hR : ‖R‖ ≤ 1) (hX : ‖X‖ ≤ 1) :
    rectHSNorm r (R * W - W * X) ≤
      2 * rectHSNorm r (W - V) + rectHSNorm r (R * V - V * X) := by
  have he : R * W - W * X =
      (R * (W - V) + (R * V - V * X)) + (V - W) * X := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    abel
  have hl : rectHSNorm r (R * (W - V)) ≤ rectHSNorm r (W - V) :=
    (rectHSNorm_mul_le_left r R (W - V)).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hR (rectHSNorm_nonneg r (W - V)))
  have hr : rectHSNorm r ((V - W) * X) ≤ rectHSNorm r (W - V) := by
    apply (rectHSNorm_mul_le_right r (V - W) X).trans
    rw [rectHSNorm_sub_comm r V W]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hX (rectHSNorm_nonneg r (W - V))
  rw [he]
  have ht := rectHSNorm_add_le r (R * (W - V) + (R * V - V * X)) ((V - W) * X)
  have hs := rectHSNorm_add_le r (R * (W - V)) (R * V - V * X)
  linarith

variable [NeZero d]

theorem MatrixThomSpectralData.polar_intertwining_bound {A B D : StarSubalgebra ℂ (CMatrix d)}
    {ε : ℝ} (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε)
    (X : CMatrix d) (hXB : X ∈ B) (hX : matrixOpNorm X ≤ 1) :
    rectHSNorm d (S.sourceRep X * matrixRectPolar (S.cut * S.isometry) -
      matrixRectPolar (S.cut * S.isometry) * X) ≤ (4 + Real.sqrt 2) * ε := by
  have hd := matrixCutIsometry_polar_distance_le d S.isometry S.isometry_gram S.cut_projection
  have hc : rectHSNorm d (matrixRectPolar (S.cut * S.isometry) - S.isometry) ≤ 2 * ε := by
    apply (sq_le_sq₀ (rectHSNorm_nonneg d _) (mul_nonneg (by norm_num) hε)).mp
    nlinarith [S.deleted_mass_le]
  have hρ : ‖S.sourceRep X‖ ≤ 1 :=
    (completelyPositiveMap_norm_le (S.sourceRep : CMatrix d →CP CMatrix (d * (d * d)))
      (map_one S.sourceRep) X).trans hX
  have he := matrixStinespring_expectation_nearInclusion_bound A B hε hBA
    S.sourceRep S.isometry S.isometry_gram S.expectation X hXB hX
  have hp := matrixRectangular_intertwining_perturbation d (S.sourceRep X) X S.isometry
    (matrixRectPolar (S.cut * S.isometry)) hρ hX
  nlinarith

theorem MatrixThomSpectralData.polar_rank_lower {A B D : StarSubalgebra ℂ (CMatrix d)}
    {ε : ℝ} (S : MatrixThomSpectralData A B D ε) :
    (d : ℝ) - 2 * ε ^ 2 * d ≤ (matrixRectPolar (S.cut * S.isometry)).rank := by
  have hr := matrixCutIsometry_polar_rank_bound d S.isometry S.isometry_gram S.cut_projection
  have ht : matrixTraceReal d (1 : CMatrix d) = 1 := by simp [matrixTraceReal, NeZero.ne d]
  rw [ht] at hr
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have he := (le_div_iff₀ hd).mp (show 1 - 2 * ε ^ 2 ≤
    ((matrixRectPolar (S.cut * S.isometry)).rank : ℝ) / d by linarith [S.deleted_mass_le])
  nlinarith

end ThomGame.Analysis

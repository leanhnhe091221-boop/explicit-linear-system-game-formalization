module

public import ThomGame.Analysis.MatrixStableAmbientFrames
public import ThomGame.Analysis.MatrixPartialIsometryCornerNorms

/-!
# The common support inside the actual enlarged matrix algebra

The two embedded support corners coincide in a single Fin-indexed matrix
space. Traces and HS distances continue to use the supplied denominator.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d m n : Nat}

theorem matrixFrame_final_projection (F : Matrix (Fin n) (Fin d) ℂ) (hF : Fᴴ * F = 1) :
    IsStarProjection (F * Fᴴ) := by
  apply matrixPartialIsometry_final_projection
  rw [hF]
  exact IsStarProjection.one _

theorem matrixFrameLift_projection (F : Matrix (Fin n) (Fin d) ℂ) (hF : Fᴴ * F = 1)
    (P : CMatrix d) (hP : IsStarProjection P) : IsStarProjection (matrixFrameLift F P) := by
  constructor
  · show matrixFrameLift F P * matrixFrameLift F P = matrixFrameLift F P
    rw [matrixFrameLift_mul hF, hP.isIdempotentElem.eq]
  · change (matrixFrameLift F P)ᴴ = matrixFrameLift F P
    rw [matrixFrameLift_star, hP.isSelfAdjoint.isHermitian.eq]

theorem matrixStableFrames_source_corner (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) (X : CMatrix d) :
    matrixFrameLift (matrixStableSourceFrame W hW) ((Wᴴ * W) * X * (Wᴴ * W)) =
      matrixFrameLift (matrixStableTargetFrame W) (W * X * Wᴴ) := by
  let E := matrixStableSourceFrame W hW
  let F := matrixStableTargetFrame W
  calc
    _ = (E * (Wᴴ * W)) * X * (E * (Wᴴ * W))ᴴ := by
      simp only [matrixFrameLift, E, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = (F * W) * X * (F * W)ᴴ := by rw [matrixStableFrames_support_match]
    _ = _ := by simp only [matrixFrameLift, F, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem matrixStableFrames_target_corner (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) (Y : CMatrix m) :
    matrixFrameLift (matrixStableTargetFrame W) ((W * Wᴴ) * Y * (W * Wᴴ)) =
      matrixFrameLift (matrixStableSourceFrame W hW) (Wᴴ * Y * W) := by
  let E := matrixStableSourceFrame W hW
  let F := matrixStableTargetFrame W
  calc
    _ = (F * (W * Wᴴ)) * Y * (F * (W * Wᴴ))ᴴ := by
      simp only [matrixFrameLift, F, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = (E * Wᴴ) * Y * (E * Wᴴ)ᴴ := by rw [matrixStableFrames_adjoint_support_match]
    _ = _ := by simp only [matrixFrameLift, E, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem matrixStableFrames_common_support (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) :
    matrixFrameLift (matrixStableSourceFrame W hW) (Wᴴ * W) =
      matrixFrameLift (matrixStableTargetFrame W) (W * Wᴴ) := by
  have he := matrixStableFrames_source_corner W hW (1 : CMatrix d)
  simpa only [Matrix.mul_one, hW.isIdempotentElem.eq] using he

theorem matrixFrameLift_opNorm (F : Matrix (Fin n) (Fin d) ℂ) (hF : Fᴴ * F = 1)
    (X : CMatrix d) : matrixOpNorm (matrixFrameLift F X) = matrixOpNorm X := by
  apply matrixPartialIsometry_sandwich_norm_eq
  · rw [hF]; exact IsStarProjection.one _
  · rw [hF, Matrix.one_mul]
  · rw [hF, Matrix.mul_one]

theorem matrixFrameCompression_opNorm_le (F : Matrix (Fin n) (Fin d) ℂ) (hF : Fᴴ * F = 1)
    (Y : CMatrix n) : matrixOpNorm (Fᴴ * Y * F) ≤ matrixOpNorm Y := by
  change ‖Fᴴ * Y * F‖ ≤ ‖Y‖
  have hP : IsStarProjection (Fᴴᴴ * Fᴴ) := by
    simpa only [Matrix.conjTranspose_conjTranspose] using matrixFrame_final_projection F hF
  simpa only [Matrix.conjTranspose_conjTranspose] using matrixPartialIsometry_sandwich_norm_le Fᴴ hP Y

theorem matrixStableCommonSupport_complement_trace (r : Nat) (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) :
    matrixTraceReal r (1 - matrixFrameLift (matrixStableSourceFrame W hW) (Wᴴ * W)) =
      matrixTraceReal r (1 - Wᴴ * W) + matrixTraceReal r (1 - W * Wᴴ) := by
  have hm := matrixProjection_rank_one_sub_add (matrixPartialIsometry_final_projection hW)
  rw [Matrix.rank_self_mul_conjTranspose, Fintype.card_fin] at hm
  have hmR : (m : ℝ) = ((1 - W * Wᴴ).rank : ℝ) + (W.rank : ℝ) := by exact_mod_cast hm.symm
  rw [matrixTraceReal_sub, matrixFrameLift_trace r (matrixStableSourceFrame_initial W hW),
    matrixTraceReal_projection_rank r hW, matrixTraceReal_projection_rank r hW.one_sub,
    matrixTraceReal_projection_rank r (matrixPartialIsometry_final_projection hW).one_sub,
    Matrix.rank_conjTranspose_mul_self]
  have hone : matrixTraceReal r (1 : CMatrix (m + (1 - Wᴴ * W).rank)) =
      ((m : ℝ) + ((1 - Wᴴ * W).rank : ℝ)) / r := by simp [matrixTraceReal]
  rw [hone, hmR]
  ring

end ThomGame.Analysis

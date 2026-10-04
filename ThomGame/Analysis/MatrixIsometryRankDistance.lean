module

public import ThomGame.Analysis.MatrixPartialIsometryCompression
public import ThomGame.Analysis.MatrixPolarSupport

/-!
# Distance from an isometry bounds the rank defect

On the actual kernel support of T, the difference V-T equals V.
This gives the dimension bound without a singular-value gap or a norm bound on T.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d m : Nat}

theorem matrixIsometry_rank_defect_le_distance (r : Nat) (V T : Matrix (Fin m) (Fin d) ℂ)
    (hV : Vᴴ * V = 1) :
    matrixTraceReal r (1 : CMatrix d) - (T.rank : ℝ) / r ≤ rectHSNorm r (T - V) ^ 2 := by
  let P := matrixRealSupport (matrixRectAbs T)
  let Q := 1 - P
  have hP : IsStarProjection P := matrixRealSupport_isStarProjection _
  have hQ : IsStarProjection Q := hP.one_sub
  have hTQ : T * Q = 0 := by
    dsimp only [Q, P]
    rw [Matrix.mul_sub, Matrix.mul_one, matrix_mul_absSupport, sub_self]
  have he : (V - T) * Q = V * Q := by rw [Matrix.sub_mul, hTQ, sub_zero]
  have hQi : IsStarProjection (Qᴴ * Q) := by
    rw [hQ.isSelfAdjoint.isHermitian.eq, hQ.isIdempotentElem.eq]
    exact hQ
  have hb := rectHSNorm_mul_sq_le_of_partialIsometry r (V - T) hQi
  rw [he, rectHSNorm_sub_comm r V T] at hb
  have hnorm : rectHSNorm r (V * Q) ^ 2 = matrixTraceReal r Q := by
    rw [rectHSNorm_frame_mul r hV, ← matrixTraceReal_gram,
      hQ.isSelfAdjoint.isHermitian.eq, hQ.isIdempotentElem.eq]
  have ht : matrixTraceReal r Q = matrixTraceReal r (1 : CMatrix d) - (T.rank : ℝ) / r := by
    dsimp only [Q]
    rw [matrixTraceReal_sub, matrixTraceReal_projection_rank r hP]
    dsimp only [P]
    rw [matrixRectPolar_initial_rank]
  rwa [hnorm, ht] at hb

theorem matrixIsometry_rank_lower_of_distance [NeZero d] (V T : Matrix (Fin m) (Fin d) ℂ)
    (hV : Vᴴ * V = 1) {c : ℝ} (hc : rectHSNorm d (T - V) ^ 2 ≤ c) :
    (d : ℝ) - c * d ≤ T.rank := by
  have he := (matrixIsometry_rank_defect_le_distance d V T hV).trans hc
  have ht : matrixTraceReal d (1 : CMatrix d) = 1 := by simp [matrixTraceReal, NeZero.ne d]
  rw [ht] at he
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hm := (le_div_iff₀ hd).mp (show 1 - c ≤ (T.rank : ℝ) / d by linarith)
  nlinarith

end ThomGame.Analysis

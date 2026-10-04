module

public import ThomGame.Analysis.MatrixBimoduleRectangles

/-!
# Trace pairing depends only on the matching rectangular compression
-/

@[expose] public section
namespace ThomGame.Analysis

variable {d : Nat}

theorem matrixRectangle_pairing_compress_left (P Q X Y : CMatrix d)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hXl : P * X = X) (hXr : X * Q = X) :
    normalizedTrace (star (P * Y * Q) * X) = normalizedTrace (star Y * X) := by
  calc
    normalizedTrace (star (P * Y * Q) * X) = normalizedTrace (Q * (star Y * (P * X))) := by
      simp only [star_mul, hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq, mul_assoc]
    _ = normalizedTrace (Q * (star Y * X)) := by rw [hXl]
    _ = normalizedTrace ((star Y * X) * Q) := normalizedTrace_mul_comm _ _
    _ = normalizedTrace (star Y * X) := by rw [mul_assoc, hXr]

theorem matrixRectangle_pairing_compress_right (P Q X Y : CMatrix d)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hYl : P * Y = Y) (hYr : Y * Q = Y) :
    normalizedTrace (star Y * (P * X * Q)) = normalizedTrace (star Y * X) := by
  have h := congrArg star (matrixRectangle_pairing_compress_left P Q Y X hP hQ hYl hYr)
  simpa only [← normalizedTrace_star, star_mul, star_star] using h

end ThomGame.Analysis

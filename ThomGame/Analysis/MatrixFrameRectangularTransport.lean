module

public import ThomGame.Analysis.MatrixReducingCompression

/-!
# Restriction of supported rectangular matrices to an orthonormal frame

Rank, Gram matrices and HS norms retain their actual values. Reducing
intertwining defects retain the original normalization, for any denominator.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d m k : Nat}

theorem matrixFrame_supported_lift (F : Matrix (Fin m) (Fin k) ℂ)
    (W : Matrix (Fin m) (Fin d) ℂ) (hW : (F * Fᴴ) * W = W) :
    F * (Fᴴ * W) = W := by rw [← Matrix.mul_assoc, hW]

theorem matrixFrame_supported_gram (F : Matrix (Fin m) (Fin k) ℂ)
    (W : Matrix (Fin m) (Fin d) ℂ) (hW : (F * Fᴴ) * W = W) :
    (Fᴴ * W)ᴴ * (Fᴴ * W) = Wᴴ * W := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    _ = Wᴴ * ((F * Fᴴ) * W) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hW]

theorem matrixFrame_supported_rank (F : Matrix (Fin m) (Fin k) ℂ)
    (W : Matrix (Fin m) (Fin d) ℂ) (hW : (F * Fᴴ) * W = W) :
    (Fᴴ * W).rank = W.rank := by
  rw [← Matrix.rank_conjTranspose_mul_self (Fᴴ * W), matrixFrame_supported_gram F W hW,
    Matrix.rank_conjTranspose_mul_self]

theorem matrixFrame_supported_hsNorm (r : Nat) {F : Matrix (Fin m) (Fin k) ℂ}
    (hF : Fᴴ * F = 1) (W : Matrix (Fin m) (Fin d) ℂ) (hW : (F * Fᴴ) * W = W) :
    rectHSNorm r (Fᴴ * W) = rectHSNorm r W := by
  rw [← rectHSNorm_frame_mul r hF, matrixFrame_supported_lift F W hW]

theorem matrixFrame_supported_partialIsometry (F : Matrix (Fin m) (Fin k) ℂ)
    (W : Matrix (Fin m) (Fin d) ℂ) (hW : (F * Fᴴ) * W = W) (hWi : IsStarProjection (Wᴴ * W)) :
    IsStarProjection ((Fᴴ * W)ᴴ * (Fᴴ * W)) ∧ IsStarProjection ((Fᴴ * W) * (Fᴴ * W)ᴴ) := by
  have hi : IsStarProjection ((Fᴴ * W)ᴴ * (Fᴴ * W)) := by
    rwa [matrixFrame_supported_gram F W hW]
  exact ⟨hi, matrixPartialIsometry_final_projection hi⟩

theorem matrixFrame_supported_intertwining_lift {F : Matrix (Fin m) (Fin k) ℂ}
    (hF : Fᴴ * F = 1) (W : Matrix (Fin m) (Fin d) ℂ) (hW : (F * Fᴴ) * W = W)
    (R : CMatrix m) (X : CMatrix d) (hR : (F * Fᴴ) * R = R * (F * Fᴴ)) :
    F * ((Fᴴ * R * F) * (Fᴴ * W) - (Fᴴ * W) * X) = R * W - W * X := by
  rw [Matrix.mul_sub, ← Matrix.mul_assoc F (Fᴴ * R * F) (Fᴴ * W),
    ← matrixFrame_reducing_intertwines hF R hR, Matrix.mul_assoc R F (Fᴴ * W),
    matrixFrame_supported_lift F W hW, ← Matrix.mul_assoc F (Fᴴ * W) X,
    matrixFrame_supported_lift F W hW]

theorem matrixFrame_supported_intertwining_norm (r : Nat) {F : Matrix (Fin m) (Fin k) ℂ}
    (hF : Fᴴ * F = 1) (W : Matrix (Fin m) (Fin d) ℂ) (hW : (F * Fᴴ) * W = W)
    (R : CMatrix m) (X : CMatrix d) (hR : (F * Fᴴ) * R = R * (F * Fᴴ)) :
    rectHSNorm r ((Fᴴ * R * F) * (Fᴴ * W) - (Fᴴ * W) * X) =
      rectHSNorm r (R * W - W * X) := by
  rw [← rectHSNorm_frame_mul r hF, matrixFrame_supported_intertwining_lift hF W hW R X hR]

theorem matrixFrame_supported_exact_intertwining (F : Matrix (Fin m) (Fin k) ℂ)
    (W : Matrix (Fin m) (Fin d) ℂ) (hW : (F * Fᴴ) * W = W)
    (R : CMatrix m) (X : CMatrix d) (h : R * W = W * X) :
    (Fᴴ * R * F) * (Fᴴ * W) = (Fᴴ * W) * X := by
  calc
    _ = Fᴴ * R * ((F * Fᴴ) * W) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hW, Matrix.mul_assoc Fᴴ R W, h, Matrix.mul_assoc]

end ThomGame.Analysis

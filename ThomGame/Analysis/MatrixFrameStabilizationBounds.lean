module

public import ThomGame.Analysis.MatrixThomStableCompression
public import ThomGame.Analysis.MatrixThomStableNearInclusion

/-!
# Exact normalization and deletion bounds for matrix frame embeddings

The source and target normalized HS norms differ by the square root of
their dimension ratio. Removing the complementary corner is small for
every operator-bounded matrix, not only for contractions.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

open scoped Matrix.Norms.Frobenius in
theorem rectHSNorm_rescale {ι κ : Type*} [Fintype ι] [Fintype κ]
    {r s : Nat} (hr : 0 < r) (hs : 0 < s) (X : Matrix ι κ ℂ) :
    rectHSNorm r X = Real.sqrt ((s : ℝ) / r) * rectHSNorm s X := by
  have hr' : Real.sqrt (r : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hr))
  have hs' : Real.sqrt (s : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hs))
  rw [rectHSNorm, rectHSNorm, Real.sqrt_div (Nat.cast_nonneg s)]
  field_simp

theorem matrixFrameLift_hsNorm_rescale {d n : Nat} (hd : 0 < d) (hn : 0 < n)
    (F : Matrix (Fin n) (Fin d) ℂ) (hF : Fᴴ * F = 1) (X : CMatrix d) :
    hsNorm (matrixFrameLift F X) = Real.sqrt ((d : ℝ) / n) * hsNorm X := by
  rw [← rectHSNorm_eq_hsNorm, rectHSNorm_rescale hn hd, matrixFrameLift_hsNorm d hF,
    rectHSNorm_eq_hsNorm]

theorem matrixFrameLift_hsNorm_recover {d n : Nat} (hd : 0 < d) (hn : 0 < n)
    (F : Matrix (Fin n) (Fin d) ℂ) (hF : Fᴴ * F = 1) (X : CMatrix d) :
    hsNorm X = Real.sqrt ((n : ℝ) / d) * hsNorm (matrixFrameLift F X) := by
  rw [← rectHSNorm_eq_hsNorm X, ← matrixFrameLift_hsNorm d hF X,
    rectHSNorm_rescale hd hn, rectHSNorm_eq_hsNorm]

theorem matrixProjection_compression_loss_opNorm (r : Nat) {n : Nat}
    (P X : CMatrix n) (hP : IsStarProjection P) :
    rectHSNorm r (X - P * X * P) ≤ 2 * rectHSNorm r (1 - P) * matrixOpNorm X := by
  have he : X - P * X * P = (1 - P) * X + P * (X * (1 - P)) := by noncomm_ring
  have ha := rectHSNorm_mul_le_right r (1 - P) X
  have hb := rectHSNorm_mul_le_left r X (1 - P)
  have hc : rectHSNorm r (P * (X * (1 - P))) ≤ rectHSNorm r (X * (1 - P)) :=
    (sq_le_sq₀ (rectHSNorm_nonneg r _) (rectHSNorm_nonneg r _)).mp
      (rectHSNorm_projection_mul_sq_le r hP (X * (1 - P)))
  have ht := rectHSNorm_add_le r ((1 - P) * X) (P * (X * (1 - P)))
  rw [← he] at ht
  change rectHSNorm r ((1 - P) * X) ≤ rectHSNorm r (1 - P) * matrixOpNorm X at ha
  change rectHSNorm r (X * (1 - P)) ≤ matrixOpNorm X * rectHSNorm r (1 - P) at hb
  nlinarith

theorem matrixFrame_compression_loss_opNorm {d n : Nat} (r : Nat)
    (F : Matrix (Fin n) (Fin d) ℂ) (hF : Fᴴ * F = 1) (X : CMatrix n) :
    rectHSNorm r (X - matrixFrameLift F (Fᴴ * X * F)) ≤
      2 * rectHSNorm r (1 - F * Fᴴ) * matrixOpNorm X := by
  rw [matrixFrameLift_compression]
  exact matrixProjection_compression_loss_opNorm r _ X (matrixFrame_final_projection F hF)

theorem matrixFrame_complement_hsNorm {d n : Nat} (hn : 0 < n)
    (F : Matrix (Fin n) (Fin d) ℂ) (hF : Fᴴ * F = 1) :
    hsNorm (1 - F * Fᴴ) = Real.sqrt (1 - (d : ℝ) / n) := by
  have ht : matrixTraceReal n (1 - F * Fᴴ) = 1 - (d : ℝ) / n := by
    rw [matrixFrame_complement_trace n F hF, sub_div, div_self (ne_of_gt (Nat.cast_pos.mpr hn))]
  have hs := rectHSNorm_projection_sq n (matrixFrame_final_projection F hF).one_sub
  rw [ht, rectHSNorm_eq_hsNorm] at hs
  rw [← hs, Real.sqrt_sq (hsNorm_nonneg _)]

theorem matrixFrameCompression_lift {d n : Nat} (F : Matrix (Fin n) (Fin d) ℂ)
    (hF : Fᴴ * F = 1) (X : CMatrix d) : Fᴴ * matrixFrameLift F X * F = X := by
  simp only [matrixFrameLift, Matrix.mul_assoc]
  rw [hF, Matrix.mul_one, ← Matrix.mul_assoc, hF, Matrix.one_mul]

end ThomGame.Analysis

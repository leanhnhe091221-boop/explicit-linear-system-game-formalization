module

public import ThomGame.Analysis.MatrixPolarCompletionDistance

/-!
# Actual unitary completions of compressed unitaries

Completing the polar factor of q u q on the range of q gives both
inequalities (3.12) of ALT. All norms use the original normalization r.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_matrixCompressionPolar (r : Nat) {q : Matrix ι ι ℂ}
    (hq : IsStarProjection q) (u : Matrix.unitaryGroup ι ℂ) :
    ∃ W : Matrix ι ι ℂ,
      Wᴴ * W = q ∧ W * Wᴴ = q ∧
      Wᴴ * (q * u.val * q) = matrixRectAbs (q * u.val * q) ∧
      rectHSNorm r (W - q * u.val * q) ^ 2 ≤
        rectHSNorm r ((1 - q) * u.val * q) ^ 2 ∧
      rectHSNorm r (W - q * u.val) ^ 2 ≤
        rectHSNorm r (u.val * q - q * u.val) ^ 2 ∧
      rectHSNorm r (u.val * q - W) ^ 2 ≤
        rectHSNorm r (u.val * q - q * u.val) ^ 2 := by
  have hqstar := hq.isSelfAdjoint.isHermitian.eq
  have hqmul := hq.isIdempotentElem.eq
  have hu : u.valᴴ * u.val = 1 := u.prop.1
  have huv : u.val * u.valᴴ = 1 := u.prop.2
  let X := q * u.val * q
  have hXq : X * q = X := by simp only [X, Matrix.mul_assoc, hqmul]
  have hqX : q * X = X := by simp only [X, ← Matrix.mul_assoc, hqmul]
  obtain ⟨W, hWi, hWf, hWX⟩ := exists_matrixPolar_completion hq hq rfl hXq hqX
  have hW : IsStarProjection (Wᴴ * W) := hWi.symm ▸ hq
  have hWq : W * q = W := by rw [← hWi]; exact matrixPartialIsometry_mul_initial hW
  have hqW : q * W = W := by rw [← hWf, Matrix.mul_assoc, hWi, hWq]
  have hWsq : Wᴴ * q = Wᴴ := by
    simpa only [Matrix.conjTranspose_mul, hqstar] using congrArg Matrix.conjTranspose hqW
  have hqWs : q * Wᴴ = Wᴴ := by
    simpa only [Matrix.conjTranspose_mul, hqstar] using congrArg Matrix.conjTranspose hWq
  have hright : (u.val * q)ᴴ * (u.val * q) = q := by
    simp only [Matrix.conjTranspose_mul, hqstar, Matrix.mul_assoc,
      ← Matrix.mul_assoc u.valᴴ u.val q, hu, Matrix.one_mul, hqmul]
  have hleft : matrixTraceReal r ((q * u.val)ᴴ * (q * u.val)) = matrixTraceReal r q := by
    rw [matrixProjection_compression_gram hq, matrixTraceReal_mul_comm r (u.valᴴ * q) u.val]
    rw [← Matrix.mul_assoc, huv, Matrix.one_mul]
  have hgram : Xᴴ * X ≤ q := by
    simpa only [X, Matrix.mul_assoc, hright] using
      matrixProjection_compression_gram_le hq (u.val * q)
  have habs := matrixTraceReal_mono r
    (matrixRectAbs_ge_gram_of_gram_le_one (hgram.trans hq.le_one))
  have hdefect : rectHSNorm r ((1 - q) * u.val * q) ^ 2 =
      matrixTraceReal r q - matrixTraceReal r (Xᴴ * X) := by
    rw [← matrixTraceReal_gram, Matrix.mul_assoc, matrixProjection_compression_gram hq.one_sub]
    have he : (u.val * q)ᴴ * (1 - q) * (u.val * q) = q - Xᴴ * X := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hright]
      congr 1
      simpa only [X, Matrix.mul_assoc] using (matrixProjection_compression_gram hq (u.val * q)).symm
    rw [he, matrixTraceReal_sub]
  have hpairRight : Wᴴ * (u.val * q) = matrixRectAbs X := by
    calc
      _ = Wᴴ * (q * u.val * q) := by simp only [← Matrix.mul_assoc, hWsq]
      _ = _ := hWX
  have hpairLeft : matrixTraceReal r (Wᴴ * (q * u.val)) = matrixTraceReal r (matrixRectAbs X) := by
    calc
      _ = matrixTraceReal r ((Wᴴ * (q * u.val)) * q) := by
        rw [matrixTraceReal_mul_comm r (Wᴴ * (q * u.val)) q]
        simp only [← Matrix.mul_assoc, hqWs]
      _ = _ := by rw [Matrix.mul_assoc]; exact congrArg (matrixTraceReal r) hWX
  have hcross : matrixTraceReal r ((u.val * q)ᴴ * (q * u.val)) = matrixTraceReal r (Xᴴ * X) := by
    calc
      _ = matrixTraceReal r (((u.val * q)ᴴ * (q * u.val)) * q) := by
        rw [matrixTraceReal_mul_comm r ((u.val * q)ᴴ * (q * u.val)) q]
        simp only [Matrix.conjTranspose_mul, hqstar, ← Matrix.mul_assoc, hqmul]
      _ = _ := by
        rw [show X = q * (u.val * q) from Matrix.mul_assoc _ _ _,
          matrixProjection_compression_gram hq]
        simp only [Matrix.mul_assoc]
  have hcomm : rectHSNorm r (u.val * q - q * u.val) ^ 2 =
      2 * matrixTraceReal r q - 2 * matrixTraceReal r (Xᴴ * X) := by
    rw [rectHSNorm_sub_sq, hright, hleft, hcross]
    ring
  refine ⟨W, hWi, hWf, hWX, ?_, ?_, ?_⟩
  · change rectHSNorm r (W - X) ^ 2 ≤ _
    rw [rectHSNorm_sub_sq, hWi, hWX, hdefect]
    linarith
  · rw [rectHSNorm_sub_sq, hWi, hleft, hpairLeft, hcomm]
    linarith
  · rw [rectHSNorm_sub_comm r (u.val * q) W, rectHSNorm_sub_sq, hWi,
      hright, hpairRight, hcomm]
    linarith

end ThomGame.Analysis

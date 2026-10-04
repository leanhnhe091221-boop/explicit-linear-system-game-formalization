module

public import ThomGame.Analysis.MatrixCompressionPolar

/-!
# Unitaries on actual projection ranges

An orthonormal frame transports the completed polar map to a genuine
unitary group on the smaller space. The two errors of ALT (3.12)
remain unchanged under this transport.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] in
theorem rectHSNorm_frame_mul (r : Nat) {F : Matrix ι κ ℂ} (hF : Fᴴ * F = 1)
    (X : Matrix κ ν ℂ) : rectHSNorm r (F * X) = rectHSNorm r X := by
  have he : (F * X)ᴴ * (F * X) = Xᴴ * X := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Fᴴ F X,
      hF, Matrix.one_mul]
  rw [rectHSNorm_eq_sqrt_gram, he, ← rectHSNorm_eq_sqrt_gram]

omit [DecidableEq ι] in
theorem rectHSNorm_mul_frame_adjoint (r : Nat) {F : Matrix ι κ ℂ} (hF : Fᴴ * F = 1)
    (X : Matrix ν κ ℂ) : rectHSNorm r (X * Fᴴ) = rectHSNorm r X := by
  rw [← rectHSNorm_conjTranspose r (X * Fᴴ), Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, rectHSNorm_frame_mul r hF, rectHSNorm_conjTranspose]

omit [Fintype ν] in
theorem exists_matrixCornerUnitary {q : Matrix ι ι ℂ} (hq : IsStarProjection q)
    {F : Matrix ι κ ℂ} (hFi : Fᴴ * F = 1) (hFf : F * Fᴴ = q)
    {W : Matrix ι ι ℂ} (hWi : Wᴴ * W = q) (hWf : W * Wᴴ = q) :
    ∃ v : Matrix.unitaryGroup κ ℂ, F * v.val * Fᴴ = W := by
  have hW : IsStarProjection (Wᴴ * W) := hWi.symm ▸ hq
  have hWq : W * q = W := by rw [← hWi]; exact matrixPartialIsometry_mul_initial hW
  have hqW : q * W = W := by rw [← hWf, Matrix.mul_assoc, hWi, hWq]
  have hWsq : Wᴴ * q = Wᴴ := by
    simpa only [Matrix.conjTranspose_mul, hq.isSelfAdjoint.isHermitian.eq] using
      congrArg Matrix.conjTranspose hqW
  have hqF : q * F = F := by rw [← hFf, Matrix.mul_assoc, hFi, Matrix.mul_one]
  have hv : (Fᴴ * W * F)ᴴ * (Fᴴ * W * F) = 1 := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = Fᴴ * Wᴴ * (F * Fᴴ) * W * F := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hFf, Matrix.mul_assoc Fᴴ Wᴴ q, hWsq, Matrix.mul_assoc Fᴴ Wᴴ W,
          hWi, Matrix.mul_assoc, hqF, hFi]
  refine ⟨⟨Fᴴ * W * F, Matrix.mem_unitaryGroup_iff'.mpr hv⟩, ?_⟩
  change F * (Fᴴ * W * F) * Fᴴ = W
  calc
    _ = (F * Fᴴ) * W * (F * Fᴴ) := by simp only [Matrix.mul_assoc]
    _ = W := by rw [hFf, hqW, hWq]

omit [Fintype ν] in
theorem exists_matrixFrameCompressionUnitary (r : Nat) {q : Matrix ι ι ℂ}
    (hq : IsStarProjection q) {F : Matrix ι κ ℂ}
    (hFi : Fᴴ * F = 1) (hFf : F * Fᴴ = q) (u : Matrix.unitaryGroup ι ℂ) :
    ∃ v : Matrix.unitaryGroup κ ℂ,
      rectHSNorm r (v.val * Fᴴ - Fᴴ * u.val) ^ 2 ≤
        rectHSNorm r (u.val * q - q * u.val) ^ 2 ∧
      rectHSNorm r (u.val * F - F * v.val) ^ 2 ≤
        rectHSNorm r (u.val * q - q * u.val) ^ 2 := by
  obtain ⟨W, hWi, hWf, _, _, hleft, hright⟩ := exists_matrixCompressionPolar r hq u
  obtain ⟨v, hv⟩ := exists_matrixCornerUnitary hq hFi hFf hWi hWf
  refine ⟨v, ?_, ?_⟩
  · rw [← rectHSNorm_frame_mul r hFi (v.val * Fᴴ - Fᴴ * u.val), Matrix.mul_sub,
      ← Matrix.mul_assoc, hv, ← Matrix.mul_assoc, hFf]
    exact hleft
  · rw [← rectHSNorm_mul_frame_adjoint r hFi (u.val * F - F * v.val), Matrix.sub_mul,
      Matrix.mul_assoc u.val F Fᴴ, hFf, hv]
    exact hright

end ThomGame.Analysis

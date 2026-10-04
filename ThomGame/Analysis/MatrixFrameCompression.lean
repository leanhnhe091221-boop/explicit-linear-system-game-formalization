module

public import ThomGame.Analysis.MatrixContractionUnitaryPair

/-!
# Transport through an actual orthonormal matrix frame

The lift preserves multiplication, adjoints, traces and HS norms.
The trace and HS normalization is the given ambient dimension r.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

noncomputable def matrixFrameLift (F : Matrix ι κ ℂ) (X : Matrix κ κ ℂ) : Matrix ι ι ℂ := F * X * Fᴴ

omit [DecidableEq ι] in
theorem matrixFrameLift_mul {F : Matrix ι κ ℂ} (hF : Fᴴ * F = 1) (X Y : Matrix κ κ ℂ) :
    matrixFrameLift F X * matrixFrameLift F Y = matrixFrameLift F (X * Y) := by
  change (F * X * Fᴴ) * (F * Y * Fᴴ) = _
  calc
    _ = F * X * (Fᴴ * F) * Y * Fᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hF, Matrix.mul_one]; simp only [matrixFrameLift, Matrix.mul_assoc]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem matrixFrameLift_star (F : Matrix ι κ ℂ) (X : Matrix κ κ ℂ) :
    (matrixFrameLift F X)ᴴ = matrixFrameLift F Xᴴ := by
  simp only [matrixFrameLift, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem matrixFrameLift_add (F : Matrix ι κ ℂ) (X Y : Matrix κ κ ℂ) :
    matrixFrameLift F (X + Y) = matrixFrameLift F X + matrixFrameLift F Y := by
  simp only [matrixFrameLift, Matrix.mul_add, Matrix.add_mul]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem matrixFrameLift_sub (F : Matrix ι κ ℂ) (X Y : Matrix κ κ ℂ) :
    matrixFrameLift F (X - Y) = matrixFrameLift F X - matrixFrameLift F Y := by
  simp only [matrixFrameLift, Matrix.mul_sub, Matrix.sub_mul]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem matrixFrameLift_smul (F : Matrix ι κ ℂ) (c : ℂ) (X : Matrix κ κ ℂ) :
    matrixFrameLift F (c • X) = c • matrixFrameLift F X := by
  simp only [matrixFrameLift, Matrix.mul_smul, Matrix.smul_mul]

omit [Fintype ι] [DecidableEq ι] in
theorem matrixFrameLift_one (F : Matrix ι κ ℂ) : matrixFrameLift F 1 = F * Fᴴ := by
  rw [matrixFrameLift, Matrix.mul_one]

omit [DecidableEq ι] in
theorem matrixFrameLift_trace (r : Nat) {F : Matrix ι κ ℂ} (hF : Fᴴ * F = 1) (X : Matrix κ κ ℂ) :
    matrixTraceReal r (matrixFrameLift F X) = matrixTraceReal r X := by
  rw [matrixFrameLift, matrixTraceReal_mul_comm r (F * X) Fᴴ, ← Matrix.mul_assoc, hF, Matrix.one_mul]

omit [DecidableEq ι] in
theorem matrixFrameLift_hsNorm (r : Nat) {F : Matrix ι κ ℂ} (hF : Fᴴ * F = 1) (X : Matrix κ κ ℂ) :
    rectHSNorm r (matrixFrameLift F X) = rectHSNorm r X := by
  rw [matrixFrameLift, rectHSNorm_mul_frame_adjoint r hF, rectHSNorm_frame_mul r hF]

omit [DecidableEq ι] [DecidableEq κ] in
theorem matrixFrameLift_compression (F : Matrix ι κ ℂ) (X : Matrix ι ι ℂ) :
    matrixFrameLift F (Fᴴ * X * F) = (F * Fᴴ) * X * (F * Fᴴ) := by
  simp only [matrixFrameLift, Matrix.mul_assoc]

theorem matrixFrameCompression_gram_le_one {q : Matrix ι ι ℂ} (hq : IsStarProjection q)
    {F : Matrix ι κ ℂ} (hFi : Fᴴ * F = 1) (hFf : F * Fᴴ = q) (U : Matrix.unitaryGroup ι ℂ) :
    (Fᴴ * U.val * F)ᴴ * (Fᴴ * U.val * F) ≤ 1 := by
  have hgram : (Fᴴ * U.val * F)ᴴ * (Fᴴ * U.val * F) = (U.val * F)ᴴ * q * (U.val * F) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = Fᴴ * U.valᴴ * (F * Fᴴ) * U.val * F := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hFf]; simp only [Matrix.mul_assoc]
  have he := matrixProjection_compression_gram_le hq (U.val * F)
  rw [matrixProjection_compression_gram hq, ← hgram] at he
  have hUi : U.valᴴ * U.val = 1 := U.prop.1
  have hu : (U.val * F)ᴴ * (U.val * F) = 1 := by
    rw [Matrix.conjTranspose_mul]
    calc
      _ = Fᴴ * (U.valᴴ * U.val) * F := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUi, Matrix.mul_one, hFi]
  rwa [hu] at he

end ThomGame.Analysis

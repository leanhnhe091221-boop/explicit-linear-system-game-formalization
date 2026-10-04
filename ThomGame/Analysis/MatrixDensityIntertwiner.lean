module

public import ThomGame.Analysis.MatrixArakiYamagami

/-! Square roots of rectangular Gram matrices and almost intertwining unitary actions. -/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem matrixRectAbs_unitary_mul (U : Matrix.unitaryGroup ι ℂ) (X : Matrix ι κ ℂ) :
    matrixRectAbs (U.val * X) = matrixRectAbs X := by
  have hU : U.valᴴ * U.val = 1 := U.prop.1
  unfold matrixRectAbs
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U.valᴴ U.val,
    hU, Matrix.one_mul]

omit [DecidableEq ι] in
theorem matrixRectAbs_mul_unitary (X : Matrix ι κ ℂ) (V : Matrix.unitaryGroup κ ℂ) :
    matrixRectAbs (X * V.val) = V.valᴴ * matrixRectAbs X * V.val := by
  have hV : V.val * V.valᴴ = 1 := V.prop.2
  unfold matrixRectAbs
  apply CFC.sqrt_unique
  · simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc V.val V.valᴴ, hV, Matrix.one_mul,
      ← Matrix.mul_assoc (CFC.sqrt (Xᴴ * X)) (CFC.sqrt (Xᴴ * X)),
      CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self X).nonneg]
    simp only [Matrix.mul_assoc]
  · exact ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Xᴴ * X))).conjTranspose_mul_mul_same
      V.val).nonneg

theorem rectHSNorm_right_density_commutator_le (r : Nat)
    (U : Matrix.unitaryGroup ι ℂ) (V : Matrix.unitaryGroup κ ℂ) (X : Matrix ι κ ℂ) :
    rectHSNorm r (matrixRectAbs X * V.val - V.val * matrixRectAbs X) ≤
      Real.sqrt 2 * rectHSNorm r (U.val * X - X * V.val) := by
  have h := rectHSNorm_rectAbs_sub_le r (U.val * X) (X * V.val)
  rw [matrixRectAbs_unitary_mul, matrixRectAbs_mul_unitary] at h
  have he : V.val * (matrixRectAbs X - V.valᴴ * matrixRectAbs X * V.val) =
      V.val * matrixRectAbs X - matrixRectAbs X * V.val := by
    have hV : V.val * V.valᴴ = 1 := V.prop.2
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hV, Matrix.one_mul]
  rw [← rectHSNorm_unitary_mul r V, he, rectHSNorm_sub_comm] at h
  exact h

theorem rectHSNorm_left_density_commutator_le (r : Nat)
    (U : Matrix.unitaryGroup ι ℂ) (V : Matrix.unitaryGroup κ ℂ) (X : Matrix ι κ ℂ) :
    rectHSNorm r (U.val * matrixRectAbs Xᴴ - matrixRectAbs Xᴴ * U.val) ≤
      Real.sqrt 2 * rectHSNorm r (U.val * X - X * V.val) := by
  have h := rectHSNorm_right_density_commutator_le r V⁻¹ U⁻¹ Xᴴ
  have hr : V⁻¹.val * Xᴴ - Xᴴ * U⁻¹.val = (X * V.val - U.val * X)ᴴ := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
    rfl
  have hl : matrixRectAbs Xᴴ * U⁻¹.val - U⁻¹.val * matrixRectAbs Xᴴ =
      (U.val * matrixRectAbs Xᴴ - matrixRectAbs Xᴴ * U.val)ᴴ := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      (matrixRectAbs_nonneg Xᴴ).isSelfAdjoint.isHermitian.eq]
    rfl
  rw [hr, hl, rectHSNorm_conjTranspose, rectHSNorm_conjTranspose, rectHSNorm_sub_comm r (X * V.val)] at h
  exact h

omit [DecidableEq κ] in
theorem rectHSNorm_mul_left_density (r : Nat) (X : Matrix ι κ ℂ) (B : Matrix ι ι ℂ) :
    rectHSNorm r (B * matrixRectAbs Xᴴ) = rectHSNorm r (B * X) := by
  rw [← rectHSNorm_conjTranspose r (B * matrixRectAbs Xᴴ),
    ← rectHSNorm_conjTranspose r (B * X)]
  simp only [Matrix.conjTranspose_mul, (matrixRectAbs_nonneg Xᴴ).isSelfAdjoint.isHermitian.eq]
  rw [rectHSNorm_eq_sqrt_gram, rectHSNorm_eq_sqrt_gram]
  congr 2
  simp only [Matrix.conjTranspose_mul, (matrixRectAbs_nonneg Xᴴ).isSelfAdjoint.isHermitian.eq,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (matrixRectAbs Xᴴ), matrixRectAbs_mul_self]
  simp only [Matrix.mul_assoc]

end ThomGame.Analysis

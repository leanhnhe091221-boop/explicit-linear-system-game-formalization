module

public import ThomGame.Analysis.MatrixCompressionUnitary

/-! Product and inverse estimates for actual rectangular approximate intertwiners. -/

@[expose] public section
namespace ThomGame.Analysis

open Matrix

open scoped Matrix.Norms.Frobenius in
theorem rectHSNorm_neg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : Nat) (X : Matrix ι κ ℂ) : rectHSNorm r (-X) = rectHSNorm r X := by
  simp only [rectHSNorm, norm_neg]

variable {d k : Nat} (r : Nat) (F : Matrix (Fin d) (Fin k) ℂ)

noncomputable def matrixIntertwiningError (U : UnitaryMatrix d) (V : UnitaryMatrix k) : ℝ :=
  rectHSNorm r (U.val * F - F * V.val)

theorem matrixIntertwiningError_nonneg (U : UnitaryMatrix d) (V : UnitaryMatrix k) :
    0 ≤ matrixIntertwiningError r F U V := rectHSNorm_nonneg _ _

theorem matrixIntertwiningError_one : matrixIntertwiningError r F 1 1 = 0 := by
  simp [matrixIntertwiningError]

theorem matrixIntertwiningError_mul_le (U W : UnitaryMatrix d) (V Z : UnitaryMatrix k) :
    matrixIntertwiningError r F (U * W) (V * Z) ≤
      matrixIntertwiningError r F U V + matrixIntertwiningError r F W Z := by
  have he : (U * W).val * F - F * (V * Z).val =
      U.val * (W.val * F - F * Z.val) + (U.val * F - F * V.val) * Z.val := by
    change (U.val * W.val) * F - F * (V.val * Z.val) = _
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  unfold matrixIntertwiningError
  rw [he]
  have h := rectHSNorm_add_le r (U.val * (W.val * F - F * Z.val))
    ((U.val * F - F * V.val) * Z.val)
  rw [rectHSNorm_unitary_mul, rectHSNorm_mul_unitary] at h
  linarith

theorem matrixIntertwiningError_inv (U : UnitaryMatrix d) (V : UnitaryMatrix k) :
    matrixIntertwiningError r F U⁻¹ V⁻¹ = matrixIntertwiningError r F U V := by
  have he : U.val * (U⁻¹.val * F - F * V⁻¹.val) * V.val = -(U.val * F - F * V.val) := by
    have hU : U.val * U⁻¹.val = 1 := congrArg Subtype.val (mul_inv_cancel U)
    have hV : V⁻¹.val * V.val = 1 := congrArg Subtype.val (inv_mul_cancel V)
    rw [Matrix.mul_sub, ← Matrix.mul_assoc U.val U⁻¹.val F, hU, Matrix.one_mul,
      Matrix.sub_mul, Matrix.mul_assoc U.val (F * V⁻¹.val) V.val,
      Matrix.mul_assoc F V⁻¹.val V.val, hV, Matrix.mul_one]
    abel
  unfold matrixIntertwiningError
  rw [← rectHSNorm_unitary_mul r U, ← rectHSNorm_mul_unitary r _ V, he]
  exact rectHSNorm_neg _ _

theorem matrixIntertwiningError_triple_le (U₀ U₁ U₂ : UnitaryMatrix d)
    (V₀ V₁ V₂ : UnitaryMatrix k) :
    matrixIntertwiningError r F (U₀ * U₁ * U₂) (V₀ * V₁ * V₂) ≤
      matrixIntertwiningError r F U₀ V₀ + matrixIntertwiningError r F U₁ V₁ +
        matrixIntertwiningError r F U₂ V₂ := by
  have h := matrixIntertwiningError_mul_le r F (U₀ * U₁) U₂ (V₀ * V₁) V₂
  have h01 := matrixIntertwiningError_mul_le r F U₀ U₁ V₀ V₁
  linarith

theorem matrixIntertwiningError_relation_le (hF : Fᴴ * F = 1)
    (U : UnitaryMatrix d) (V : UnitaryMatrix k) (z : ℂ) :
    rectHSNorm r (V.val - z • 1) ≤ matrixIntertwiningError r F U V +
      rectHSNorm r ((U.val - z • 1) * F) := by
  have he : F * (V.val - z • 1) = -(U.val * F - F * V.val) + (U.val - z • 1) * F := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
    abel
  rw [← rectHSNorm_frame_mul r hF, he]
  have h := rectHSNorm_add_le r (-(U.val * F - F * V.val)) ((U.val - z • 1) * F)
  simpa only [matrixIntertwiningError, rectHSNorm_neg] using h

theorem matrixIntertwiningError_difference_le (hF : Fᴴ * F = 1)
    (U W : UnitaryMatrix d) (V Z : UnitaryMatrix k) :
    rectHSNorm r (V.val - Z.val) ≤ matrixIntertwiningError r F U V +
      matrixIntertwiningError r F W Z + rectHSNorm r ((U.val - W.val) * F) := by
  have he : F * (V.val - Z.val) =
      -(U.val * F - F * V.val) + (W.val * F - F * Z.val) + (U.val - W.val) * F := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [← rectHSNorm_frame_mul r hF, he]
  have h₁ := rectHSNorm_add_le r (-(U.val * F - F * V.val) + (W.val * F - F * Z.val))
    ((U.val - W.val) * F)
  have h₂ := rectHSNorm_add_le r (-(U.val * F - F * V.val)) (W.val * F - F * Z.val)
  rw [rectHSNorm_neg] at h₂
  dsimp only [matrixIntertwiningError]
  linarith

end ThomGame.Analysis

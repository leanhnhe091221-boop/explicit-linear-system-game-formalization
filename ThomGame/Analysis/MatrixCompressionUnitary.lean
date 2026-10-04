module

public import ThomGame.Analysis.MatrixFrameCompression
public import ThomGame.Analysis.MatrixPartialIsometryCompression
public import ThomGame.Analysis.MatrixProjectionFinFrame

/-! A unitary on the actual compressed space, with a dimension-independent intertwining bound. -/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d k : Nat} {F : Matrix (Fin d) (Fin k) ℂ} {P : CMatrix d}

theorem matrixFrame_range_mul (hFi : Fᴴ * F = 1) (hFf : F * Fᴴ = P) : P * F = F := by
  rw [← hFf, Matrix.mul_assoc, hFi, Matrix.mul_one]

theorem rectHSNorm_mul_frame_le (r : Nat) (hFi : Fᴴ * F = 1) (A : CMatrix d) :
    rectHSNorm r (A * F) ≤ rectHSNorm r A := by
  have h := rectHSNorm_mul_sq_le_of_partialIsometry r A
    (show IsStarProjection (Fᴴ * F) by rw [hFi]; exact IsStarProjection.one _)
  exact (sq_le_sq₀ (rectHSNorm_nonneg _ _) (rectHSNorm_nonneg _ _)).mp h

theorem rectHSNorm_mul_frame_le_cut (r : Nat) (hFi : Fᴴ * F = 1) (hFf : F * Fᴴ = P)
    (A : CMatrix d) : rectHSNorm r (A * F) ≤ rectHSNorm r (A * P) := by
  have he : A * F = (A * P) * F := by rw [Matrix.mul_assoc, matrixFrame_range_mul hFi hFf]
  rw [he]
  exact rectHSNorm_mul_frame_le r hFi _

theorem matrixFrame_leakage_gram (hP : IsStarProjection P) (hFi : Fᴴ * F = 1)
    (hFf : F * Fᴴ = P) (U : UnitaryMatrix d) :
    ((1 - P) * U.val * F)ᴴ * ((1 - P) * U.val * F) =
      1 - (Fᴴ * U.val * F)ᴴ * (Fᴴ * U.val * F) := by
  have hUi : U.valᴴ * U.val = 1 := U.prop.1
  have hQ : IsStarProjection (1 - P) := hP.one_sub
  calc
    _ = Fᴴ * U.valᴴ * ((1 - P) * (1 - P)) * U.val * F := by
      simp only [Matrix.conjTranspose_mul, hQ.isSelfAdjoint.isHermitian.eq, Matrix.mul_assoc]
    _ = Fᴴ * U.valᴴ * (1 - P) * U.val * F := by rw [hQ.isIdempotentElem.eq]
    _ = Fᴴ * U.valᴴ * U.val * F - Fᴴ * U.valᴴ * P * U.val * F := by
      simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
    _ = 1 - Fᴴ * U.valᴴ * (F * Fᴴ) * U.val * F := by
      rw [Matrix.mul_assoc Fᴴ U.valᴴ U.val, hUi, Matrix.mul_one, hFi, hFf]
    _ = _ := by simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem matrixFrame_leakage_eq (hFf : F * Fᴴ = P) (U : UnitaryMatrix d) :
    (1 - P) * U.val * F = U.val * F - F * (Fᴴ * U.val * F) := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul]
  congr 1
  rw [← hFf]
  simp only [Matrix.mul_assoc]

theorem matrixFrame_leakage_le (r : Nat) (hFi : Fᴴ * F = 1) (hFf : F * Fᴴ = P)
    (U : UnitaryMatrix d) :
    rectHSNorm r ((1 - P) * U.val * F) ≤ rectHSNorm r (P * U.val - U.val * P) := by
  have he : (1 - P) * U.val * F = (U.val * P - P * U.val) * F := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul, Matrix.sub_mul,
      Matrix.mul_assoc U.val P F, matrixFrame_range_mul hFi hFf]
  rw [he, rectHSNorm_sub_comm r (P * U.val)]
  exact rectHSNorm_mul_frame_le r hFi _

theorem exists_matrixCompression_unitary (r : Nat) (hP : IsStarProjection P)
    (hFi : Fᴴ * F = 1) (hFf : F * Fᴴ = P) (U : UnitaryMatrix d) :
    ∃ V : UnitaryMatrix k, rectHSNorm r (U.val * F - F * V.val) ≤
      2 * rectHSNorm r (P * U.val - U.val * P) := by
  obtain ⟨V, _W, _hsum, hV, _hW⟩ := exists_matrixContraction_unitary_pair r
    (matrixFrameCompression_gram_le_one hP hFi hFf U)
  have hsq : rectHSNorm r (V.val - Fᴴ * U.val * F) ^ 2 =
      rectHSNorm r ((1 - P) * U.val * F) ^ 2 := by
    rw [hV, ← matrixTraceReal_gram, matrixFrame_leakage_gram hP hFi hFf U]
  have he : rectHSNorm r (V.val - Fᴴ * U.val * F) =
      rectHSNorm r ((1 - P) * U.val * F) :=
    (sq_eq_sq₀ (rectHSNorm_nonneg _ _) (rectHSNorm_nonneg _ _)).mp hsq
  have hdec : U.val * F - F * V.val =
      ((1 - P) * U.val * F) + F * (Fᴴ * U.val * F - V.val) := by
    rw [matrixFrame_leakage_eq hFf, Matrix.mul_sub]
    abel
  refine ⟨V, ?_⟩
  rw [hdec]
  have ha := rectHSNorm_add_le r ((1 - P) * U.val * F) (F * (Fᴴ * U.val * F - V.val))
  rw [rectHSNorm_frame_mul r hFi, rectHSNorm_sub_comm r (Fᴴ * U.val * F), he] at ha
  have hb := matrixFrame_leakage_le r hFi hFf U
  linarith

end ThomGame.Analysis

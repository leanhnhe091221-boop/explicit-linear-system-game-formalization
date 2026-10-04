module

public import ThomGame.Analysis.MatrixCornerUnitary
public import Mathlib.Analysis.CStarAlgebra.Unitary.Span

/-!
# A matrix contraction as the average of two actual unitaries

Complete its polar factor, and multiply by the two unitaries
`abs X ± I sqrt (1 - abs X ^ 2)`. Each squared Hilbert--Schmidt
error is exactly the normalized trace of `1 - X*X`.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixRectAbs_le_one_of_gram_le_one {X : Matrix ι ι ℂ} (hX : Xᴴ * X ≤ 1) :
    matrixRectAbs X ≤ 1 := by
  simpa only [matrixRectAbs, CFC.sqrt_one] using CFC.monotone_sqrt hX

theorem exists_matrixContraction_unitary_pair (r : Nat) {X : Matrix ι ι ℂ}
    (hX : Xᴴ * X ≤ 1) :
    ∃ V W : Matrix.unitaryGroup ι ℂ,
      V.val + W.val = (2 : ℂ) • X ∧
      rectHSNorm r (V.val - X) ^ 2 = matrixTraceReal r (1 - Xᴴ * X) ∧
      rectHSNorm r (W.val - X) ^ 2 = matrixTraceReal r (1 - Xᴴ * X) := by
  obtain ⟨Z, hZi, hZf, hZX⟩ := exists_matrixPolar_completion
    (X := X) (IsStarProjection.one (R := Matrix ι ι ℂ)) (IsStarProjection.one (R := Matrix ι ι ℂ))
    rfl (Matrix.mul_one X) (Matrix.one_mul X)
  let U : Matrix.unitaryGroup ι ℂ := ⟨Z, ⟨hZi, hZf⟩⟩
  let A : selfAdjoint (Matrix ι ι ℂ) := ⟨matrixRectAbs X, (matrixRectAbs_nonneg X).isSelfAdjoint⟩
  have hA : ‖A‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ (matrixRectAbs_nonneg X)).mpr
    (matrixRectAbs_le_one_of_gram_le_one hX)
  let T := selfAdjoint.unitarySelfAddISMul A hA
  have hUA : U.val * (A : Matrix ι ι ℂ) = X := by
    change Z * matrixRectAbs X = X
    rw [← hZX, ← Matrix.mul_assoc, hZf, Matrix.one_mul]
  have hT : T.val = (A : Matrix ι ι ℂ) + Complex.I • CFC.sqrt (1 - (A : Matrix ι ι ℂ) ^ 2) :=
    selfAdjoint.unitarySelfAddISMul_coe A hA
  have hTm : (star T).val = (A : Matrix ι ι ℂ) - Complex.I • CFC.sqrt (1 - (A : Matrix ι ι ℂ) ^ 2) := by
    rw [Unitary.coe_star]
    exact selfAdjoint.star_coe_unitarySelfAddISMul A hA
  have hsum : T.val + (star T).val = (2 : ℂ) • (A : Matrix ι ι ℂ) := by
    rw [hT, hTm, two_smul]
    abel
  have hAsq : (A : Matrix ι ι ℂ) ^ 2 = Xᴴ * X := by
    change matrixRectAbs X ^ 2 = _
    rw [sq, matrixRectAbs_mul_self]
  have hD : 0 ≤ 1 - (A : Matrix ι ι ℂ) ^ 2 := by rw [hAsq]; exact sub_nonneg.mpr hX
  have hdist : rectHSNorm r (T.val - (A : Matrix ι ι ℂ)) ^ 2 = matrixTraceReal r (1 - Xᴴ * X) := by
    rw [hT, add_sub_cancel_left, rectHSNorm_smul, Complex.norm_I, one_mul, ← matrixTraceReal_gram]
    rw [(CFC.sqrt_nonneg (1 - (A : Matrix ι ι ℂ) ^ 2)).isSelfAdjoint.isHermitian.eq,
      CFC.sqrt_mul_sqrt_self _ hD, hAsq]
  have hdistStar : rectHSNorm r ((star T).val - (A : Matrix ι ι ℂ)) ^ 2 =
      matrixTraceReal r (1 - Xᴴ * X) := by
    have he : (star T).val - (A : Matrix ι ι ℂ) = (T.val - (A : Matrix ι ι ℂ))ᴴ := by
      rw [Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_sub, A.prop.isHermitian.eq]
    rw [he, rectHSNorm_conjTranspose, hdist]
  refine ⟨U * T, U * star T, ?_, ?_, ?_⟩
  · change U.val * T.val + U.val * (star T).val = _
    rw [← Matrix.mul_add, hsum, Matrix.mul_smul, hUA]
  · change rectHSNorm r (U.val * T.val - X) ^ 2 = _
    rw [← hUA, ← Matrix.mul_sub, rectHSNorm_unitary_mul, hdist, hUA]
  · change rectHSNorm r (U.val * (star T).val - X) ^ 2 = _
    rw [← hUA, ← Matrix.mul_sub, rectHSNorm_unitary_mul, hdistStar, hUA]

end ThomGame.Analysis

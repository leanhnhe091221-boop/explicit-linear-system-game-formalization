module

public import ThomGame.Analysis.MatrixHilbertSchmidtLipschitz
public import Mathlib.Analysis.Matrix.Order

/-!
# Self-adjoint dilations and rectangular absolute values

For a rectangular matrix X, the self-adjoint dilation has off-diagonal
blocks X and X*. Its absolute value has diagonal blocks |X*| and |X|.
All Hilbert--Schmidt norms retain the original normalization.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem matrix_fromBlocks_diagonal_nonneg {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ Matrix.fromBlocks A 0 0 B := by
  have hpA := Matrix.nonneg_iff_posSemidef.mp hA
  have hpB := Matrix.nonneg_iff_posSemidef.mp hB
  apply Matrix.nonneg_iff_posSemidef.mpr
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hpA.isHermitian.fromBlocks (by simp) hpB.isHermitian) fun x => ?_
  simpa [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.fromBlocks,
    Function.comp_def] using add_nonneg
      (hpA.dotProduct_mulVec_nonneg (x ∘ Sum.inl))
      (hpB.dotProduct_mulVec_nonneg (x ∘ Sum.inr))

omit [DecidableEq ι] [DecidableEq κ] in
theorem rectHSNorm_fromBlocks_sq (r : Nat) (A : Matrix ι ι ℂ) (B : Matrix ι κ ℂ)
    (C : Matrix κ ι ℂ) (D : Matrix κ κ ℂ) :
    rectHSNorm r (Matrix.fromBlocks A B C D) ^ 2 =
      rectHSNorm r A ^ 2 + rectHSNorm r B ^ 2 +
        rectHSNorm r C ^ 2 + rectHSNorm r D ^ 2 := by
  simp only [rectHSNorm_sq, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Finset.sum_add_distrib]
  ring

noncomputable def matrixSelfAdjointDilation (X : Matrix ι κ ℂ) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ := Matrix.fromBlocks 0 X Xᴴ 0

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem matrixSelfAdjointDilation_isHermitian (X : Matrix ι κ ℂ) :
    Matrix.IsHermitian (matrixSelfAdjointDilation X) :=
  (Matrix.isHermitian_zero (n := ι) (α := ℂ)).fromBlocks rfl Matrix.isHermitian_zero

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem matrixSelfAdjointDilation_sub (X Y : Matrix ι κ ℂ) :
    matrixSelfAdjointDilation (X - Y) =
      matrixSelfAdjointDilation X - matrixSelfAdjointDilation Y := by
  ext (i | i) (j | j) <;> simp [matrixSelfAdjointDilation]

theorem matrixSelfAdjointDilation_sq (X : Matrix ι κ ℂ) :
    matrixSelfAdjointDilation X * matrixSelfAdjointDilation X =
      Matrix.fromBlocks (X * Xᴴ) 0 0 (Xᴴ * X) := by
  simp [matrixSelfAdjointDilation, Matrix.fromBlocks_multiply]

omit [DecidableEq ι] [DecidableEq κ] in
theorem rectHSNorm_selfAdjointDilation_sq (r : Nat) (X : Matrix ι κ ℂ) :
    rectHSNorm r (matrixSelfAdjointDilation X) ^ 2 = 2 * rectHSNorm r X ^ 2 := by
  rw [matrixSelfAdjointDilation, rectHSNorm_fromBlocks_sq]
  simp only [rectHSNorm_zero, rectHSNorm_conjTranspose]
  ring

noncomputable def matrixRectAbs (X : Matrix ι κ ℂ) : Matrix κ κ ℂ := CFC.sqrt (Xᴴ * X)

omit [DecidableEq ι] in
theorem matrixRectAbs_nonneg (X : Matrix ι κ ℂ) : 0 ≤ matrixRectAbs X := CFC.sqrt_nonneg _

omit [DecidableEq ι] in
theorem matrixRectAbs_mul_self (X : Matrix ι κ ℂ) :
    matrixRectAbs X * matrixRectAbs X = Xᴴ * X :=
  CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self X).nonneg

theorem matrixRectAbs_eq_cfcAbs (X : Matrix ι ι ℂ) : matrixRectAbs X = CFC.abs X := rfl

theorem matrixSelfAdjointDilation_abs (X : Matrix ι κ ℂ) :
    CFC.abs (matrixSelfAdjointDilation X) =
      Matrix.fromBlocks (matrixRectAbs Xᴴ) 0 0 (matrixRectAbs X) := by
  rw [CFC.abs]
  apply CFC.sqrt_unique
  · rw [(matrixSelfAdjointDilation_isHermitian X).star_eq,
      matrixSelfAdjointDilation_sq]
    simp [Matrix.fromBlocks_multiply, matrixRectAbs_mul_self]
  · exact matrix_fromBlocks_diagonal_nonneg (matrixRectAbs_nonneg Xᴴ) (matrixRectAbs_nonneg X)

theorem matrixSelfAdjointDilation_cfc_abs (X : Matrix ι κ ℂ) :
    cfc (abs : ℝ → ℝ) (matrixSelfAdjointDilation X) =
      Matrix.fromBlocks (matrixRectAbs Xᴴ) 0 0 (matrixRectAbs X) := by
  have he := CFC.abs_eq_cfc_norm (matrixSelfAdjointDilation X)
    (matrixSelfAdjointDilation_isHermitian X)
  simpa only [Real.norm_eq_abs, matrixSelfAdjointDilation_abs] using he.symm

end ThomGame.Analysis
